'use strict';
/**
 * MUSO-1 — Proof Gatekeeper agent for the zkVerify Agent Games.
 *
 * Single-file Vercel serverless function. The platform POSTs HMAC-signed
 * task envelopes; this agent verifies the signature, makes a deterministic
 * APPROVE/REJECT decision, generates a real Groth16 proof locally with
 * snarkjs against the official gatekeeper circuit, optionally submits it
 * to zkVerify via Kurier, and returns a signed response — well inside the
 * 60-second hard deadline.
 *
 * Protocol details implemented here follow the official /build spec
 * (agentgames.zkverify.io/build) and the /events/proof-gatekeeper trap
 * taxonomy. Circuit input signal names were recovered from the published
 * gatekeeper.wasm artifact itself and confirmed by proving locally.
 *
 * Env vars:
 *   AGENT_GAMES_HMAC_SECRET  (required) platform secret from dashboard -> agent -> Rotate Secret
 *   KURIER_API_KEY           (optional) mainnet Kurier key; without it, submission is skipped
 *                            and the agent still answers with proof + public_signals
 *   KURIER_API_URL           (optional) default https://api.kurier.xyz/api/v1
 *   KURIER_POLL_BUDGET_MS    (optional) default 8000 (Vercel Hobby functions cap at 10 s)
 *   TASK_SOFT_DEADLINE_MS    (optional) default 50000 (platform hard deadline is 60 s)
 *   SEEN_STORE_PATH          (optional) default /tmp/gatekeeper-seen.json
 */

const crypto = require('crypto');
const fs = require('fs');
const os = require('os');
const path = require('path');
const snarkjs = require('snarkjs');

// ---------------------------------------------------------------- constants
const TASK_TYPE = 'agent-games.proof-gatekeeper.v1';
const PREFLIGHT_TYPE = 'agent-games.preflight.v1';
const PROTOCOL_VERSION = 'v1';
const SIG_HEADER = 'x-agent-games-signature';
const BN128_PRIME = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
const GATEKEEPER_VK_HASH =
  '0x6b79c6012a6d8651f3e13bc4d2a20370280ab49700c90c5316d4168bfbad77b0';
const WASM_URL = 'https://agentgames.zkverify.io/circuits/gatekeeper.wasm';
const ZKEY_URL = 'https://agentgames.zkverify.io/circuits/gatekeeper_final.zkey';
const WASM_BYTES = 1755820; // integrity check on the downloaded artifact
const ZKEY_BYTES = 309750;
const MAX_BODY_BYTES = 1_048_576;

// ---------------------------------------------------------------- config
function loadConfig(env) {
  return {
    hmacSecret: env.AGENT_GAMES_HMAC_SECRET || '',
    kurierApiKey: env.KURIER_API_KEY || null,
    kurierApiUrl: env.KURIER_API_URL || 'https://api.kurier.xyz/api/v1',
    gatekeeperVkHash: env.GATEKEEPER_VK_HASH || GATEKEEPER_VK_HASH,
    seenStorePath: env.SEEN_STORE_PATH || path.join(os.tmpdir(), 'gatekeeper-seen.json'),
    kurierPollBudgetMs: Number(env.KURIER_POLL_BUDGET_MS || 8000),
    kurierPollIntervalMs: Number(env.KURIER_POLL_INTERVAL_MS || 2000),
    taskSoftDeadlineMs: Number(env.TASK_SOFT_DEADLINE_MS || 50000),
  };
}

// ---------------------------------------------------------------- HMAC
function signBody(secret, rawBody) {
  return crypto.createHmac('sha256', secret).update(rawBody).digest('hex');
}

function decodeCandidate(headerValue) {
  let v = headerValue.trim();
  if (v.toLowerCase().startsWith('sha256=')) v = v.slice('sha256='.length).trim();
  if (/^[0-9a-fA-F]{64}$/.test(v)) return Buffer.from(v, 'hex');
  try {
    const b = Buffer.from(v, 'base64');
    if (b.length === 32) return b;
  } catch { /* fall through */ }
  return null;
}

function verifyBodySignature(secret, rawBody, headerValue) {
  if (!secret || !headerValue) return false;
  const candidate = decodeCandidate(headerValue);
  if (!candidate) return false;
  const expected = crypto.createHmac('sha256', secret).update(rawBody).digest();
  return candidate.length === expected.length && crypto.timingSafeEqual(candidate, expected);
}

/** Deterministic per-task salt: HMAC(secret, "gatekeeper-salt:" + task_id) mod p. */
function deriveSalt(secret, taskId) {
  const digest = crypto
    .createHmac('sha256', secret || 'gatekeeper-local-dev')
    .update('gatekeeper-salt:' + taskId)
    .digest();
  return BigInt('0x' + digest.toString('hex')) % BN128_PRIME;
}

// ---------------------------------------------------------------- decision
function normalizeHex(v) {
  return (v || '').trim().toLowerCase();
}

function parseUint(v) {
  if (typeof v === 'number') {
    return Number.isSafeInteger(v) && v >= 0 ? BigInt(v) : null;
  }
  if (typeof v !== 'string') return null;
  const s = v.trim();
  if (/^0x[0-9a-fA-F]+$/.test(s)) return BigInt(s);
  if (/^[0-9]+$/.test(s)) return BigInt(s);
  return null;
}

/** Structural validation + parsing. Returns null on any malformed field. */
function parseInput(input) {
  if (!input || typeof input !== 'object') return null;
  const minimum = parseUint(input.minimum);
  const publicBalance = parseUint(input.public_balance);
  const amount = parseUint(input.amount);
  const maxTransfer = parseUint(input.max_transfer);
  const expiryBlock = parseUint(input.expiry_block);
  const currentBlock = parseUint(input.current_block);
  if (
    minimum === null || publicBalance === null || amount === null ||
    maxTransfer === null || expiryBlock === null || currentBlock === null
  ) return null;
  if (
    typeof input.registered_vk !== 'string' || !input.registered_vk ||
    typeof input.proof_vk !== 'string' || !input.proof_vk ||
    typeof input.recipient !== 'string' || !input.recipient ||
    typeof input.condition_recipient !== 'string' || !input.condition_recipient ||
    typeof input.proof_tx !== 'string' || !input.proof_tx
  ) return null;
  return {
    registeredVk: input.registered_vk,
    proofVk: input.proof_vk,
    minimum, publicBalance, expiryBlock, currentBlock,
    recipient: input.recipient,
    conditionRecipient: input.condition_recipient,
    amount, maxTransfer,
    proofTx: input.proof_tx,
  };
}

/**
 * Deterministic policy, mirroring the gatekeeper circuit exactly
 * (boundaries included): balance >= minimum passes, amount <= max_transfer
 * passes, current_block < expiry_block passes.
 */
function evaluate(parsed, isProofTxSeen) {
  if (normalizeHex(parsed.proofVk) !== normalizeHex(parsed.registeredVk)) {
    return { decision: 'REJECT', reason_code: 'VK_SUBSTITUTION', provable: true };
  }
  if (isProofTxSeen(parsed.proofTx)) {
    // Documented special case: a reused-proof task has no proof to submit.
    return { decision: 'REJECT', reason_code: 'PROOF_REUSED', provable: false };
  }
  if (parsed.publicBalance < parsed.minimum) {
    return { decision: 'REJECT', reason_code: 'THRESHOLD_MISMATCH', provable: true };
  }
  if (parsed.currentBlock >= parsed.expiryBlock) {
    return { decision: 'REJECT', reason_code: 'EXPIRED_CONDITION', provable: true };
  }
  if (normalizeHex(parsed.recipient) !== normalizeHex(parsed.conditionRecipient)) {
    return { decision: 'REJECT', reason_code: 'RECIPIENT_MISMATCH', provable: true };
  }
  if (parsed.amount > parsed.maxTransfer) {
    return { decision: 'REJECT', reason_code: 'AMOUNT_OVERFLOW', provable: true };
  }
  return { decision: 'APPROVE', reason_code: 'VALID_CONDITION', provable: true };
}

/** Envelope value -> BN128 field element (decimal string). */
function toFieldElement(v) {
  let n;
  if (typeof v === 'bigint') {
    n = v;
  } else {
    const s = v.trim();
    if (/^0x[0-9a-fA-F]+$/.test(s)) n = BigInt(s);
    else if (/^[0-9]+$/.test(s)) n = BigInt(s);
    else {
      // Free-form identifier (e.g. task_id "gk_8d31_x"): hash into the field.
      n = BigInt('0x' + crypto.createHash('sha256').update(s).digest('hex'));
    }
  }
  return (((n % BN128_PRIME) + BN128_PRIME) % BN128_PRIME).toString(10);
}

/**
 * Circuit inputs for gatekeeper.wasm (13 inputs; `salt` is the only private one):
 *   taskId, registeredVkHash, proofVkHash, minimum, publicBalance,
 *   expiryBlock, currentBlock, recipient, conditionRecipient,
 *   amount, maxTransfer, decision, salt
 * The circuit asserts decision == AND of the five field checks — a wrong
 * decision is unprovable (witness generation fails).
 */
function buildCircuitInputs(task, parsed, decision, salt) {
  return {
    taskId: toFieldElement(task.task_id),
    registeredVkHash: toFieldElement(parsed.registeredVk),
    proofVkHash: toFieldElement(parsed.proofVk),
    minimum: parsed.minimum.toString(10),
    publicBalance: parsed.publicBalance.toString(10),
    expiryBlock: parsed.expiryBlock.toString(10),
    currentBlock: parsed.currentBlock.toString(10),
    recipient: toFieldElement(parsed.recipient),
    conditionRecipient: toFieldElement(parsed.conditionRecipient),
    amount: parsed.amount.toString(10),
    maxTransfer: parsed.maxTransfer.toString(10),
    decision: decision === 'APPROVE' ? '1' : '0',
    salt: salt.toString(10),
  };
}

// ---------------------------------------------------------------- artifacts
// The official circuit files are public on the Agent Games site. They are
// downloaded once per instance and cached in /tmp (plus memory), so the repo
// stays code-only and deploys from GitHub with no binary uploads.
const ARTIFACTS_DIR = path.join(os.tmpdir(), 'gatekeeper-circuits');
let artifactsReady = null;

async function downloadArtifact(url, destPath, expectedBytes) {
  const res = await fetch(url);
  if (!res.ok) throw new Error(`artifact download HTTP ${res.status}: ${url}`);
  const buf = Buffer.from(await res.arrayBuffer());
  if (buf.length !== expectedBytes) {
    throw new Error(`artifact size mismatch for ${url}: got ${buf.length}, want ${expectedBytes}`);
  }
  fs.writeFileSync(destPath, buf);
}

async function ensureArtifacts() {
  if (artifactsReady) return artifactsReady;
  artifactsReady = (async () => {
    fs.mkdirSync(ARTIFACTS_DIR, { recursive: true });
    const wasmPath = path.join(ARTIFACTS_DIR, 'gatekeeper.wasm');
    const zkeyPath = path.join(ARTIFACTS_DIR, 'gatekeeper_final.zkey');
    if (!fs.existsSync(wasmPath) || fs.statSync(wasmPath).size !== WASM_BYTES) {
      await downloadArtifact(WASM_URL, wasmPath, WASM_BYTES);
    }
    if (!fs.existsSync(zkeyPath) || fs.statSync(zkeyPath).size !== ZKEY_BYTES) {
      await downloadArtifact(ZKEY_URL, zkeyPath, ZKEY_BYTES);
    }
    return { wasmPath, zkeyPath };
  })();
  // If the download fails, allow a retry on the next task instead of caching the failure.
  artifactsReady.catch(() => { artifactsReady = null; });
  return artifactsReady;
}

async function prove(circuitInputs) {
  const { wasmPath, zkeyPath } = await ensureArtifacts();
  const { proof, publicSignals } = await snarkjs.groth16.fullProve(circuitInputs, wasmPath, zkeyPath);
  return { proof, publicSignals };
}

// ---------------------------------------------------------------- Kurier
// Submits the locally generated proof to zkVerify mainnet via Kurier and
// polls until the submission transaction exists (Submitted status, ~4 s
// live). Finalization (~27 s) completes server-side at Kurier and never
// blocks the task response. Never throws; any failure returns null and the
// caller still answers with proof + public_signals.
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function submitProofAndPoll(cfg, proof, publicSignals, budgetMs) {
  if (!cfg.kurierApiKey) return null;
  const key = cfg.kurierApiKey;
  const deadline = Date.now() + Math.max(0, budgetMs);
  try {
    const submitRes = await fetch(`${cfg.kurierApiUrl}/submit-proof/${key}`, {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify({
        proofType: 'groth16',
        vkRegistered: true, // the gatekeeper vk_hash is already registered on mainnet
        proofOptions: { library: 'snarkjs', curve: 'bn128' },
        proofData: { proof, publicSignals, vk: cfg.gatekeeperVkHash },
      }),
    });
    if (!submitRes.ok) {
      console.error(`[kurier] submit-proof HTTP ${submitRes.status}`);
      return null;
    }
    const job = await submitRes.json();
    if (!job.jobId) {
      console.error('[kurier] submit-proof response missing jobId');
      return null;
    }
    let status = 'Submitted';
    let lastTxHash;
    while (Date.now() < deadline) {
      await sleep(Math.min(cfg.kurierPollIntervalMs, Math.max(0, deadline - Date.now())));
      const statusRes = await fetch(`${cfg.kurierApiUrl}/job-status/${key}/${job.jobId}`);
      if (!statusRes.ok) continue;
      const s = await statusRes.json();
      status = s.status || status;
      const txHash = s.txHash || (s.transactionInfo && s.transactionInfo.txHash);
      if (txHash) lastTxHash = txHash;
      if (status === 'Failed') return { jobId: job.jobId, status, txHash, finalized: false };
      if (txHash) return { jobId: job.jobId, status, txHash, finalized: status === 'Finalized' };
    }
    return { jobId: job.jobId, status, txHash: lastTxHash, finalized: false };
  } catch (err) {
    console.error('[kurier] submission error:', err.message);
    return null;
  }
}

// ---------------------------------------------------------------- seen store
// proof_tx seen-set (PROOF_REUSED trap) + task_id -> response cache
// (idempotent redelivery). In-memory authoritative; JSON file backs it
// across restarts (best-effort: on serverless /tmp may vanish on cold start).
class SeenStore {
  constructor(filePath) {
    this.filePath = filePath;
    this.seenProofTx = new Set();
    this.responseByTaskId = new Map();
    this.load();
  }
  load() {
    try {
      const data = JSON.parse(fs.readFileSync(this.filePath, 'utf8'));
      for (const tx of data.proofTx || []) this.seenProofTx.add(normalizeTx(tx));
      for (const [k, v] of Object.entries(data.responses || {})) this.responseByTaskId.set(k, v);
    } catch { /* missing/corrupt file -> start empty */ }
  }
  persist() {
    try {
      fs.mkdirSync(path.dirname(this.filePath), { recursive: true });
      const tmp = this.filePath + '.tmp';
      fs.writeFileSync(tmp, JSON.stringify({
        proofTx: [...this.seenProofTx],
        responses: Object.fromEntries(this.responseByTaskId),
      }));
      fs.renameSync(tmp, this.filePath);
    } catch (err) {
      console.error('[seen-store] persist failed:', err.message);
    }
  }
  hasProofTx(tx) { return this.seenProofTx.has(normalizeTx(tx)); }
  recordProofTx(tx) {
    const key = normalizeTx(tx);
    if (!key || this.seenProofTx.has(key)) return;
    this.seenProofTx.add(key);
    this.persist();
  }
  getResponse(taskId) { return this.responseByTaskId.get(taskId) || null; }
  recordResponse(taskId, body) {
    if (this.responseByTaskId.has(taskId)) return;
    this.responseByTaskId.set(taskId, body);
    this.persist();
  }
}

function normalizeTx(tx) {
  return (tx || '').trim().toLowerCase();
}

// ---------------------------------------------------------------- handler
function parseTimestamp(v) {
  if (typeof v === 'number' && Number.isFinite(v)) return v < 1e12 ? v * 1000 : v;
  if (typeof v === 'string') {
    const asNum = Number(v);
    if (/^[0-9]+$/.test(v.trim()) && Number.isFinite(asNum)) {
      return asNum < 1e12 ? asNum * 1000 : asNum;
    }
    const t = Date.parse(v);
    return Number.isNaN(t) ? null : t;
  }
  return null;
}

let cfg = null;
let store = null;

function getState() {
  if (!cfg) {
    cfg = loadConfig(process.env);
    store = new SeenStore(cfg.seenStorePath);
  }
  return { cfg, store };
}

function signed(cfg, status, obj) {
  const body = typeof obj === 'string' ? obj : JSON.stringify(obj);
  return { status, body, signature: signBody(cfg.hmacSecret, body) };
}

async function handleTask(cfg, store, task, startedAt) {
  // Idempotent redelivery: answer from the cache, never re-evaluate
  // (a redelivery must not be mistaken for proof reuse).
  if (task.task_id) {
    const cached = store.getResponse(task.task_id);
    if (cached) return signed(cfg, 200, cached);
  }

  // Timestamp sanity (HMAC already authenticates the sender; this is
  // anti-replay hygiene). Only a clearly-past deadline fails the task.
  const now = Date.now();
  const deadlineMs = parseTimestamp(task.deadline_at);
  const issuedMs = parseTimestamp(task.issued_at);
  if (deadlineMs !== null && now > deadlineMs) {
    return signed(cfg, 200, { decision: 'REJECT', reason_code: 'INVALID_TASK' });
  }
  if (issuedMs !== null && issuedMs > now + 5 * 60_000) {
    return signed(cfg, 200, { decision: 'REJECT', reason_code: 'INVALID_TASK' });
  }

  const parsed = parseInput(task.input);
  if (!parsed || !task.task_id) {
    return signed(cfg, 200, { decision: 'REJECT', reason_code: 'INVALID_TASK' });
  }

  const evaluation = evaluate(parsed, (tx) => store.hasProofTx(tx));
  const response = { decision: evaluation.decision, reason_code: evaluation.reason_code };

  if (evaluation.provable) {
    const salt = deriveSalt(cfg.hmacSecret, task.task_id);
    const circuitInputs = buildCircuitInputs(task, parsed, evaluation.decision, salt);
    try {
      const { proof, publicSignals } = await prove(circuitInputs);
      response.proof = proof;
      response.public_signals = publicSignals;
      const remaining = cfg.taskSoftDeadlineMs - (Date.now() - startedAt);
      const budget = Math.min(cfg.kurierPollBudgetMs, Math.max(0, remaining));
      const kurier = await submitProofAndPoll(cfg, proof, publicSignals, budget);
      response.proof_tx = kurier && kurier.txHash ? kurier.txHash : parsed.proofTx;
    } catch (err) {
      // Proving failed: fail closed. A claimed APPROVE without a valid
      // proof is the worst outcome, so downgrade to REJECT with no proof.
      console.error('[agent] proof generation failed:', err.message);
      return signed(cfg, 200, {
        decision: 'REJECT',
        reason_code: evaluation.decision === 'APPROVE' ? 'INVALID_TASK' : evaluation.reason_code,
        proof_tx: parsed.proofTx,
      });
    }
  } else {
    // PROOF_REUSED: documented as having no proof to submit; echo the reference.
    response.proof_tx = parsed.proofTx;
  }

  const result = signed(cfg, 200, response);
  // Record only after a successful evaluation, so a task never flags itself.
  store.recordProofTx(parsed.proofTx);
  store.recordResponse(task.task_id, result.body);
  return result;
}

async function handlePost(rawBody, signatureHeader) {
  const startedAt = Date.now();
  const { cfg, store } = getState();

  if (!cfg.hmacSecret) {
    return {
      status: 500,
      body: JSON.stringify({ error: 'server_misconfigured', detail: 'AGENT_GAMES_HMAC_SECRET not set' }),
      signature: null,
    };
  }

  // 1. Authenticate the raw body BEFORE parsing.
  if (!verifyBodySignature(cfg.hmacSecret, rawBody, signatureHeader)) {
    return { status: 401, body: JSON.stringify({ error: 'invalid_signature' }), signature: null };
  }

  let envelope;
  try {
    envelope = JSON.parse(rawBody.toString('utf8'));
  } catch {
    return signed(cfg, 400, { decision: 'REJECT', reason_code: 'INVALID_TASK' });
  }

  // 2. Preflight handshake.
  if (envelope.type === PREFLIGHT_TYPE) {
    return signed(cfg, 200, { ok: true, protocolVersion: PROTOCOL_VERSION });
  }

  if (envelope.type !== TASK_TYPE) {
    return signed(cfg, 400, { decision: 'REJECT', reason_code: 'INVALID_TASK' });
  }

  // 3. Task. Any error fails closed to REJECT.
  try {
    return await handleTask(cfg, store, envelope, startedAt);
  } catch (err) {
    console.error('[agent] task handling error:', err.message);
    return signed(cfg, 200, { decision: 'REJECT', reason_code: 'INVALID_TASK' });
  }
}

// ---------------------------------------------------------------- Vercel entry
// Vercel Serverless Function: GET = health check, POST = preflight + tasks.
// The raw request body is read from the stream (no body parsing) so the HMAC
// is verified over the exact bytes the platform signed.
module.exports = async (req, res) => {
  if (req.method === 'GET') {
    res.writeHead(200, { 'content-type': 'application/json' });
    res.end(JSON.stringify({ ok: true, protocolVersion: PROTOCOL_VERSION }));
    return;
  }

  if (req.method !== 'POST') {
    res.writeHead(405, { 'content-type': 'application/json' });
    res.end(JSON.stringify({ error: 'method_not_allowed' }));
    return;
  }

  const chunks = [];
  let size = 0;
  try {
    for await (const chunk of req) {
      size += chunk.length;
      if (size > MAX_BODY_BYTES) {
        res.writeHead(413, { 'content-type': 'application/json' });
        res.end(JSON.stringify({ error: 'payload_too_large' }));
        return;
      }
      chunks.push(chunk);
    }
  } catch {
    res.writeHead(400, { 'content-type': 'application/json' });
    res.end(JSON.stringify({ error: 'bad_request' }));
    return;
  }

  const rawBody = Buffer.concat(chunks);
  const sig = req.headers[SIG_HEADER];
  const result = await handlePost(rawBody, Array.isArray(sig) ? sig[0] : sig);
  const headers = { 'content-type': 'application/json' };
  if (result.signature) headers[SIG_HEADER] = result.signature;
  res.writeHead(result.status, headers);
  res.end(result.body);
};

// Test hooks (not used by Vercel).
module.exports._test = {
  loadConfig, signBody, verifyBodySignature, deriveSalt,
  parseInput, evaluate, toFieldElement, buildCircuitInputs,
  handlePost, parseTimestamp,
};
