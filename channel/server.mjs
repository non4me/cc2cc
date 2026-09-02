#!/usr/bin/env node

/**
 * CC2CC MCP Channel Server v3.0
 *
 * Unified multi-agent communication server with dynamic identity.
 * Auto-generates a unique name on startup, discovers peers via heartbeats,
 * and exposes 7 MCP tools: whoami, list_agents, send, broadcast, reply, check_inbox, register.
 *
 * Ephemeral mailboxes: on startup, stale agent directories are cleaned up.
 * Sending to offline agents is rejected — mailboxes only exist for active sessions.
 *
 * Environment:
 *   CC2CC_BRIDGE_DIR / BRIDGE_DIR — path to bridge root (default: ~/.cc2cc)
 *   SELF — override auto-generated agent name
 */

import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  ListToolsRequestSchema,
  CallToolRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";
import { readdir, readFile, rename, mkdir, writeFile, stat, rm } from "fs/promises";
import { writeFileSync } from "fs";
import { join, basename, dirname } from "path";
import { randomUUID, createCipheriv, createDecipheriv, scryptSync } from "crypto";
import { homedir } from "os";
import { generateUniqueName, validateName, takenNames } from "./names.mjs";

// ─── Constants ───────────────────────────────────────────────────────────────

const POLL_MS = 3000;
const HEARTBEAT_INTERVAL_MS = 5000;
const HEARTBEAT_STALE_S = 15;
const SEEN_FILES_CAP = 500;
const DEFAULT_TTL = 3600;

const HOME = process.env.HOME || process.env.USERPROFILE || homedir();
const BRIDGE_DIR =
  process.env.CC2CC_BRIDGE_DIR || process.env.BRIDGE_DIR || join(HOME, ".cc2cc");

// ─── State ───────────────────────────────────────────────────────────────────

let agentName = null; // set during init
let notificationRules = null; // loaded from rules.json
const onlineSince = new Date().toISOString();
const sessionId = String(process.pid);
const seenFiles = new Set();
let knownAgents = new Map(); // name → heartbeat data
let pollTimer = null;
let statusTimer = null;
let heartbeatTimer = null;
let wakeAcknowledged = false; // set true when direct push succeeds

// ─── Encryption (optional, enabled via CC2CC_ENCRYPT=1) ─────────────────────

const ENCRYPT_ENABLED = process.env.CC2CC_ENCRYPT === "1";
let encryptionKey = null; // derived from secret.key via scrypt

async function loadEncryptionKey() {
  if (!ENCRYPT_ENABLED) return;
  try {
    const secretPath = join(BRIDGE_DIR, "secret.key");
    const secret = (await readFile(secretPath, "utf8")).trim();
    encryptionKey = scryptSync(secret, "cc2cc-aes", 32);
  } catch {
    encryptionKey = null;
  }
}

function encryptText(plaintext) {
  if (!encryptionKey) return plaintext;
  const iv = Buffer.from(randomUUID().replace(/-/g, ""), "hex").subarray(0, 12);
  const cipher = createCipheriv("aes-256-gcm", encryptionKey, iv);
  const encrypted = Buffer.concat([cipher.update(plaintext, "utf8"), cipher.final()]);
  const tag = cipher.getAuthTag();
  return `ENC:${iv.toString("hex")}:${tag.toString("hex")}:${encrypted.toString("hex")}`;
}

function decryptText(data) {
  if (!encryptionKey || !data.startsWith("ENC:")) return data;
  try {
    const [, ivHex, tagHex, encHex] = data.split(":");
    const decipher = createDecipheriv("aes-256-gcm", encryptionKey, Buffer.from(ivHex, "hex"));
    decipher.setAuthTag(Buffer.from(tagHex, "hex"));
    return decipher.update(Buffer.from(encHex, "hex"), null, "utf8") + decipher.final("utf8");
  } catch {
    return data; // return as-is if decryption fails (unencrypted message)
  }
}

// ─── Logging (structured JSON → stderr; stdout is MCP transport) ─────────────

let stdioDead = false; // set once our stdio pipes are gone (parent exited)

function log(level, msg, data = {}) {
  if (stdioDead) return;
  const entry = {
    ts: new Date().toISOString(),
    level,
    server: agentName,
    msg,
    ...data,
  };
  try {
    process.stderr.write(JSON.stringify(entry) + "\n");
  } catch {
    stdioDead = true;
  }
}

// ─── Helpers ─────────────────────────────────────────────────────────────────

function inboxDir(name) {
  return join(BRIDGE_DIR, `to-${name}`, "inbox");
}
function doneDir(name) {
  return join(BRIDGE_DIR, `to-${name}`, "done");
}
function receiptsDir(name) {
  return join(BRIDGE_DIR, `to-${name}`, "receipts");
}
function statusDir() {
  return join(BRIDGE_DIR, "status");
}

/** Retry-aware rename: handles Windows AV file locking (EPERM/EACCES). */
async function retryRename(src, dst, retries = 5, delayMs = 50) {
  for (let i = 0; i < retries; i++) {
    try {
      await rename(src, dst);
      return;
    } catch (err) {
      if ((err.code === "EPERM" || err.code === "EACCES") && i < retries - 1) {
        await new Promise((r) => setTimeout(r, delayMs * (i + 1)));
        continue;
      }
      throw err;
    }
  }
}

/** Atomic write: tmp file → rename */
async function atomicWrite(targetPath, data) {
  const dir = dirname(targetPath);
  await mkdir(dir, { recursive: true });
  const tmpPath = join(dir, `.tmp-${randomUUID()}.json`);
  await writeFile(tmpPath, JSON.stringify(data, null, 2));
  await retryRename(tmpPath, targetPath);
}

/** Build a message object (encrypts content.text if encryption enabled) */
function buildMessage({ from, to, text, type = "message", priority = "normal", replyTo = null, task = null }) {
  return {
    id: `msg-${randomUUID()}`,
    timestamp: new Date().toISOString(),
    from,
    to,
    type,
    priority,
    identity: { agent: from, mode: "session" },
    task,
    content: { text: encryptText(text), parts: [] },
    replyTo,
    ttl: DEFAULT_TTL,
  };
}

/** Decrypt content.text if encrypted */
function decryptMessage(msg) {
  if (msg?.content?.text) {
    msg.content.text = decryptText(msg.content.text);
  }
  return msg;
}

/** Write heartbeat to status/{name}-heartbeat.json */
async function writeHeartbeat(statusValue = "active", context = "session started") {
  const hb = {
    agent: agentName,
    name: agentName, // compat with takenNames() in names.mjs
    timestamp: new Date().toISOString(),
    heartbeat: new Date().toISOString(), // compat with takenNames()
    session_id: sessionId,
    parent_pid: String(process.ppid),
    status: statusValue,
    context,
  };
  const filePath = join(statusDir(), `${agentName}-heartbeat.json`);
  await atomicWrite(filePath, hb);
}

/** Check if a heartbeat is stale */
function isStale(heartbeatData) {
  const ts = heartbeatData.timestamp || heartbeatData.heartbeat;
  if (!ts) return true;
  const age = (Date.now() - new Date(ts).getTime()) / 1000;
  return age > HEARTBEAT_STALE_S;
}

/** Check if an agent is online based on known heartbeat data */
function isAgentOnline(name) {
  const hb = knownAgents.get(name);
  if (!hb) return false;
  if (hb.status !== "active") return false;
  return !isStale(hb);
}

/** Get list of all agents with status info */
function getAgentList() {
  const agents = [];
  for (const [name, hb] of knownAgents) {
    const online = hb.status === "active" && !isStale(hb);
    agents.push({
      name,
      status: online ? "online" : "offline",
      last_seen: hb.timestamp || hb.heartbeat,
      is_self: name === agentName,
    });
  }
  return agents;
}

/** Get names of online agents (excluding self) */
function onlineAgentNames() {
  return getAgentList()
    .filter((a) => a.status === "online" && !a.is_self)
    .map((a) => a.name);
}

/** Get all known agent names (for broadcast) */
function allAgentNames() {
  return [...knownAgents.keys()].filter((n) => n !== agentName);
}

// ─── MCP Server Setup ───────────────────────────────────────────────────────

const server = new Server(
  {
    name: "cc2cc_channel",
    version: "3.0.0",
    instructions: [
      "You are connected to CC2CC — an agent-to-agent communication bridge.",
      "Other agents can send you messages. Incoming messages appear as INCOMING MESSAGES blocks in tool responses.",
      "IMPORTANT: When you see INCOMING MESSAGES, you MUST react to them — read, respond, or act on tasks.",
      "Use check_inbox periodically (every few interactions) to see if anyone sent you something.",
      "Use send/reply/broadcast to communicate. Use list_agents to see who is online.",
      "If a message is a task, execute it and reply with the result.",
    ].join(" "),
  },
  {
    capabilities: {
      experimental: { "claude/channel": {} },
      tools: {},
    },
  }
);

// ─── Tool Definitions ───────────────────────────────────────────────────────

const TOOLS = [
  {
    name: "whoami",
    description: "Returns this agent's identity, uptime, bridge directory, and list of online agents",
    inputSchema: { type: "object", properties: {}, required: [] },
  },
  {
    name: "list_agents",
    description: "Returns all known agents with their status (online/offline) and last seen time",
    inputSchema: { type: "object", properties: {}, required: [] },
  },
  {
    name: "send",
    description: "Send a message to another agent. Notes if the recipient is offline.",
    inputSchema: {
      type: "object",
      properties: {
        to: { type: "string", description: "Recipient agent name" },
        text: { type: "string", description: "Message content" },
        type: {
          type: "string",
          enum: ["message", "task", "response", "status"],
          default: "message",
          description: "Message type",
        },
        priority: {
          type: "string",
          enum: ["low", "normal", "high", "critical"],
          default: "normal",
          description: "Message priority",
        },
      },
      required: ["to", "text"],
    },
  },
  {
    name: "broadcast",
    description: "Send a message to all known agents",
    inputSchema: {
      type: "object",
      properties: {
        text: { type: "string", description: "Message content" },
        priority: {
          type: "string",
          enum: ["low", "normal", "high", "critical"],
          default: "normal",
          description: "Message priority",
        },
      },
      required: ["text"],
    },
  },
  {
    name: "reply",
    description: "Reply to a received message by msg_id. Auto-completes tasks when replying to task messages.",
    inputSchema: {
      type: "object",
      properties: {
        msg_id: {
          type: "string",
          description: "Message ID to reply to (from channel notification)",
        },
        text: { type: "string", description: "Reply content" },
      },
      required: ["msg_id", "text"],
    },
  },
  {
    name: "check_inbox",
    description: "Check for new incoming messages. Also happens automatically on every other tool call.",
    inputSchema: { type: "object", properties: {}, required: [] },
  },
  {
    name: "register",
    description: "Change this agent's name. Validates, renames directories, updates heartbeat, and notifies other agents.",
    inputSchema: {
      type: "object",
      properties: {
        name: {
          type: "string",
          description: "New agent name (lowercase alphanumeric with hyphens, max 31 chars)",
        },
      },
      required: ["name"],
    },
  },
];

server.setRequestHandler(ListToolsRequestSchema, async () => ({
  tools: TOOLS,
}));

// ─── Tool Handlers ──────────────────────────────────────────────────────────

server.setRequestHandler(CallToolRequestSchema, async ({ params }) => {
  const { name: toolName, arguments: args } = params;

  try {
    let result;
    switch (toolName) {
      case "whoami":
        result = handleWhoami(); break;
      case "list_agents":
        result = handleListAgents(); break;
      case "send":
        result = await handleSend(args); break;
      case "broadcast":
        result = await handleBroadcast(args); break;
      case "reply":
        result = await handleReply(args); break;
      case "check_inbox":
        result = textResult("Inbox checked."); break;
      case "register":
        result = await handleRegister(args); break;
      default:
        return textResult(`Unknown tool: ${toolName}`, true);
    }

    // Piggyback: consume inbox and append any pending messages to the response
    const pending = await consumeInbox();
    if (pending.length > 0) {
      const pendingText = formatPendingMessages(pending);
      // Append pending messages to the first text content block
      if (result.content && result.content.length > 0 && result.content[0].type === "text") {
        result.content[0].text += pendingText;
      } else {
        result.content.push({ type: "text", text: pendingText });
      }
    }

    return result;
  } catch (err) {
    log("error", `tool ${toolName} failed`, { error: err.message });
    return textResult(`Error: ${err.message}`, true);
  }
});

function textResult(text, isError = false) {
  const result = { content: [{ type: "text", text }] };
  if (isError) result.isError = true;
  return result;
}

function jsonResult(data) {
  return {
    content: [{ type: "text", text: JSON.stringify(data, null, 2) }],
  };
}

// ── whoami ──

function handleWhoami() {
  return jsonResult({
    name: agentName,
    online_since: onlineSince,
    bridge_dir: BRIDGE_DIR,
    online_agents: onlineAgentNames(),
  });
}

// ── list_agents ──

function handleListAgents() {
  return jsonResult(getAgentList());
}

// ── send ──

async function handleSend({ to, text, type = "message", priority = "normal" }) {
  if (!to || !text) return textResult("Missing required fields: to, text", true);

  if (!isAgentOnline(to)) {
    return textResult(`Agent "${to}" is offline. Message not sent. Use list_agents to see who is online.`, true);
  }

  const msg = buildMessage({ from: agentName, to, text, type, priority });
  const targetInbox = inboxDir(to);
  await mkdir(targetInbox, { recursive: true });
  await atomicWrite(join(targetInbox, `${msg.id}.json`), msg);

  log("info", "message sent", { id: msg.id, to });
  return textResult(`Sent ${msg.id} to ${to} — delivered to inbox`);
}

// ── broadcast ──

async function handleBroadcast({ text, priority = "normal" }) {
  if (!text) return textResult("Missing required field: text", true);

  const targets = onlineAgentNames();
  if (targets.length === 0) {
    return textResult("No other agents online. Nobody to broadcast to.");
  }

  const results = [];
  for (const to of targets) {
    const msg = buildMessage({ from: agentName, to, text, type: "message", priority });
    const targetInbox = inboxDir(to);
    await mkdir(targetInbox, { recursive: true });
    await atomicWrite(join(targetInbox, `${msg.id}.json`), msg);
    results.push({ to, id: msg.id, online: isAgentOnline(to) });
  }

  log("info", "broadcast sent", { count: results.length });
  return jsonResult({ broadcast: true, recipients: results });
}

// ── reply ──

async function handleReply({ msg_id, text }) {
  if (!msg_id || !text) return textResult("Missing required fields: msg_id, text", true);

  // Try to find the original message — check inbox first (channel push
  // may arrive before consumeInbox moves the file to done/)
  let originalMsg = null;
  const myInbox = inboxDir(agentName);

  try {
    const files = await readdir(myInbox);
    for (const f of files) {
      if (!f.endsWith(".json")) continue;
      try {
        const raw = await readFile(join(myInbox, f), "utf8");
        const m = JSON.parse(raw);
        if (m.id === msg_id) {
          originalMsg = m;
          break;
        }
      } catch { /* skip */ }
    }
  } catch { /* inbox may not exist */ }

  // Then check done dir
  if (!originalMsg) {
    const myDone = doneDir(agentName);
    try {
      const files = await readdir(myDone);
      for (const f of files) {
        if (!f.endsWith(".json")) continue;
        try {
          const raw = await readFile(join(myDone, f), "utf8");
          const m = JSON.parse(raw);
          if (m.id === msg_id) {
            originalMsg = m;
            break;
          }
        } catch { /* skip */ }
      }
    } catch { /* done dir may not exist */ }
  }

  // Also check legacy inbox paths
  if (!originalMsg) {
    try {
      const topDirs = await readdir(BRIDGE_DIR);
      for (const d of topDirs) {
        if (!d.endsWith(`-to-${agentName}`)) continue;
        const legacyDone = join(BRIDGE_DIR, d, "done");
        try {
          const files = await readdir(legacyDone);
          for (const f of files) {
            if (!f.endsWith(".json")) continue;
            try {
              const raw = await readFile(join(legacyDone, f), "utf8");
              const m = JSON.parse(raw);
              if (m.id === msg_id) {
                originalMsg = m;
                break;
              }
            } catch { /* skip */ }
          }
          if (originalMsg) break;
        } catch { /* skip */ }
      }
    } catch { /* skip */ }
  }

  const to = originalMsg?.from;
  if (!to) {
    return textResult(`Cannot find original message ${msg_id}. Unable to determine recipient.`, true);
  }

  // Auto-complete task type: if original was a task, reply as response
  const replyType = originalMsg.type === "task" ? "response" : "message";

  const msg = buildMessage({
    from: agentName,
    to,
    text,
    type: replyType,
    replyTo: msg_id,
  });

  const targetInbox = inboxDir(to);
  await mkdir(targetInbox, { recursive: true });
  await atomicWrite(join(targetInbox, `${msg.id}.json`), msg);

  log("info", "reply sent", { id: msg.id, to, replyTo: msg_id });
  return textResult(`Reply ${msg.id} sent to ${to}` + (replyType === "response" ? " (task response)" : ""));
}

// ── register ──

async function handleRegister({ name: newName }) {
  if (!newName) return textResult("Missing required field: name", true);
  if (!validateName(newName)) {
    return textResult(`Invalid name "${newName}". Use lowercase a-z, 0-9, hyphens, max 31 chars.`, true);
  }

  // Check if name is taken
  const taken = await takenNames(BRIDGE_DIR);
  if (taken.has(newName) && newName !== agentName) {
    return textResult(`Name "${newName}" is already taken by an active agent.`, true);
  }

  const oldName = agentName;
  if (oldName === newName) {
    return textResult(`Already registered as "${newName}".`);
  }

  // Write offline heartbeat for old name
  await writeHeartbeat("offline", `renamed to ${newName}`);

  // Update agent name
  agentName = newName;

  // Create new directories
  await mkdir(inboxDir(agentName), { recursive: true });
  await mkdir(doneDir(agentName), { recursive: true });
  await mkdir(receiptsDir(agentName), { recursive: true });

  // Write active heartbeat with new name
  await writeHeartbeat("active", `renamed from ${oldName}`);

  // Notify other agents about the name change
  const targets = allAgentNames();
  for (const to of targets) {
    const msg = buildMessage({
      from: agentName,
      to,
      text: `Agent "${oldName}" is now "${agentName}"`,
      type: "status",
    });
    const targetInbox = inboxDir(to);
    await mkdir(targetInbox, { recursive: true });
    try {
      await atomicWrite(join(targetInbox, `${msg.id}.json`), msg);
    } catch (err) {
      log("warn", "register notify failed", { to, error: err.message });
    }
  }

  log("info", "agent renamed", { from: oldName, to: newName });
  return textResult(`Renamed from "${oldName}" to "${agentName}". ${targets.length} agents notified.`);
}

// ─── Inbox: consume pending messages ────────────────────────────────────────

/**
 * Read all pending messages from inbox, move to done, return array of messages.
 * Called on every tool invocation so the agent sees new messages immediately.
 */
async function consumeInbox() {
  const primary = inboxDir(agentName);
  await mkdir(primary, { recursive: true });
  await mkdir(doneDir(agentName), { recursive: true });

  const inboxPaths = [primary];

  // Also check legacy format: *-to-{name}/inbox/
  try {
    const topDirs = await readdir(BRIDGE_DIR);
    for (const d of topDirs) {
      if (d.endsWith(`-to-${agentName}`) && d !== `to-${agentName}`) {
        inboxPaths.push(join(BRIDGE_DIR, d, "inbox"));
      }
    }
  } catch { /* bridge dir may not exist yet */ }

  const consumed = [];

  for (const inbox of inboxPaths) {
    let files;
    try {
      files = (await readdir(inbox)).filter((f) => f.endsWith(".json") && !f.startsWith(".tmp-"));
    } catch {
      continue;
    }

    for (const file of files) {
      try {
        const filePath = join(inbox, file);
        const raw = await readFile(filePath, "utf8");
        const msg = decryptMessage(JSON.parse(raw));

        // TTL expiration check
        if (msg.timestamp && msg.ttl) {
          const age = (Date.now() - new Date(msg.timestamp).getTime()) / 1000;
          if (age > msg.ttl) {
            const done = doneDir(agentName);
            await mkdir(done, { recursive: true });
            await retryRename(filePath, join(done, file));

            if (msg.from && msg.from !== agentName) {
              const expNotice = buildMessage({
                from: agentName,
                to: msg.from,
                text: `Message ${msg.id} expired (TTL ${msg.ttl}s)`,
                type: "status",
                replyTo: msg.id,
              });
              const senderInbox = inboxDir(msg.from);
              await mkdir(senderInbox, { recursive: true });
              try {
                await atomicWrite(join(senderInbox, `${expNotice.id}.json`), expNotice);
              } catch { /* best effort */ }
            }
            log("info", "message expired", { id: msg.id, from: msg.from, ttl: msg.ttl });
            continue;
          }
        }

        // Write delivery receipt
        const receiptPath = receiptsDir(agentName);
        await mkdir(receiptPath, { recursive: true });
        await atomicWrite(join(receiptPath, `${msg.id}.receipt.json`), {
          msg_id: msg.id,
          delivered_at: new Date().toISOString(),
          delivered_to: agentName,
        });

        // Move to done/
        const done = doneDir(agentName);
        await mkdir(done, { recursive: true });
        await retryRename(filePath, join(done, file));

        // Mark as seen so pollInbox won't re-notify
        seenFiles.add(file);

        consumed.push(msg);
        log("info", "message consumed", { id: msg.id, from: msg.from, type: msg.type });
      } catch (err) {
        log("error", "message processing failed", { file, error: err.message });
      }
    }
  }

  return consumed;
}

/**
 * Format consumed messages as a text block to append to tool responses.
 */
function formatPendingMessages(messages) {
  if (messages.length === 0) return "";

  const lines = [
    "",
    "━━━ INCOMING MESSAGES ━━━",
  ];
  for (const msg of messages) {
    const taskInfo = msg.task?.title ? ` [task: ${msg.task.title}]` : "";
    const replyInfo = msg.replyTo ? ` (reply to ${msg.replyTo})` : "";
    lines.push(`[${msg.id}] from ${msg.from} (${msg.type}${taskInfo}${replyInfo}):`);
    lines.push(`  ${msg.content?.text || "(empty)"}`);
  }
  lines.push("━━━━━━━━━━━━━━━━━━━━━━━━━");
  lines.push("Reply using: reply(msg_id=\"...\", text=\"...\")");
  return lines.join("\n");
}

// ─── Notification Rules ──────────────────────────────────────────────────────

/** Load notification rules from BRIDGE_DIR/rules.json */
async function loadRules() {
  const rulesPath = join(BRIDGE_DIR, "rules.json");
  try {
    const raw = await readFile(rulesPath, "utf8");
    notificationRules = JSON.parse(raw);
    log("info", "loaded notification rules", { version: notificationRules.version });
  } catch {
    log("info", "no rules.json found, notifications will have no instructions");
  }
}

/** Format a channel notification from a message and rules */
function formatNotification(msg) {
  const type = msg.type || "message";
  const text = msg.content?.text || "(empty)";
  const taskTitle = msg.task?.title ? `\nTask: ${msg.task.title}` : "";
  const replyInfo = msg.replyTo ? ` (reply to ${msg.replyTo})` : "";

  let content = `📨 CC2CC Message\nFrom: ${msg.from}\nType: ${type}${replyInfo}${taskTitle}\nContent: ${text}`;

  const rule = notificationRules?.default;
  if (rule?.instruction) {
    content += `\n\n>> ${rule.instruction} Use msg_id: ${msg.id}`;
  }

  return content;
}

// ─── Inbox Polling (real-time channel notifications) ─────────────────────────

/**
 * Poll inbox and push channel notifications for each new message.
 * This runs on a timer so the agent sees messages immediately,
 * without waiting for the next tool call (piggyback).
 */
async function pollInbox() {
  const primary = inboxDir(agentName);
  const inboxPaths = [primary];

  // Also check legacy format
  try {
    const topDirs = await readdir(BRIDGE_DIR);
    for (const d of topDirs) {
      if (d.endsWith(`-to-${agentName}`) && d !== `to-${agentName}`) {
        inboxPaths.push(join(BRIDGE_DIR, d, "inbox"));
      }
    }
  } catch { /* bridge dir may not exist */ }

  for (const inbox of inboxPaths) {
    let files;
    try {
      files = (await readdir(inbox)).filter((f) => f.endsWith(".json") && !f.startsWith(".tmp-"));
    } catch {
      continue;
    }

    for (const file of files) {
      if (seenFiles.has(file)) continue;
      seenFiles.add(file);

      try {
        const filePath = join(inbox, file);
        const raw = await readFile(filePath, "utf8");
        const msg = decryptMessage(JSON.parse(raw));

        // TTL check — expired messages are moved to done immediately
        if (msg.timestamp && msg.ttl) {
          const age = (Date.now() - new Date(msg.timestamp).getTime()) / 1000;
          if (age > msg.ttl) {
            await mkdir(doneDir(agentName), { recursive: true });
            await retryRename(filePath, join(doneDir(agentName), file));
            log("info", "message expired (poll)", { id: msg.id });
            continue;
          }
        }

        // Push channel notification — real-time delivery attempt.
        // NOTE: Do NOT move to done here. consumeInbox() handles
        // the actual consumption (move to done, receipts) on the next
        // tool call, so the piggyback mechanism always works even if
        // channel notifications are not supported by the client.
        const content = formatNotification(msg);

        await server.notification({
          method: "notifications/claude/channel",
          params: {
            content,
            meta: {
              msg_id: msg.id,
              priority: msg.priority || "normal",
              type: msg.type || "message",
              from: msg.from,
            },
          },
        });

        log("info", "notification pushed (file stays in inbox for piggyback)", { id: msg.id, from: msg.from });
      } catch (err) {
        log("error", "poll notification failed", { file, error: err.message });
      }
    }
  }

  // Prevent memory leak
  if (seenFiles.size > SEEN_FILES_CAP) seenFiles.clear();
}

// ─── Status Polling (join/leave detection) ───────────────────────────────────

async function pollStatus() {
  const sDir = statusDir();
  let files;
  try {
    files = (await readdir(sDir)).filter((f) => f.endsWith("-heartbeat.json"));
  } catch {
    return;
  }

  const newAgents = new Map();

  for (const file of files) {
    try {
      const raw = await readFile(join(sDir, file), "utf8");
      const hb = JSON.parse(raw);
      const name = hb.agent || hb.name;
      if (!name) continue;
      newAgents.set(name, hb);
    } catch { /* skip */ }
  }

  // Detect joins
  for (const [name, hb] of newAgents) {
    if (name === agentName) continue;
    const wasKnown = knownAgents.has(name);
    const wasOnline = wasKnown && knownAgents.get(name).status === "active" && !isStale(knownAgents.get(name));
    const isOnline = hb.status === "active" && !isStale(hb);

    if (isOnline && !wasOnline) {
      log("info", "agent joined", { agent: name });
      // No channel push — statusline already reflects online agents
    }
  }

  // Detect leaves
  for (const [name, hb] of knownAgents) {
    if (name === agentName) continue;
    const wasOnline = hb.status === "active" && !isStale(hb);
    const stillExists = newAgents.has(name);
    const nowOnline = stillExists && newAgents.get(name).status === "active" && !isStale(newAgents.get(name));

    if (wasOnline && !nowOnline) {
      log("info", "agent left", { agent: name });
      // No channel push — statusline already reflects online agents
    }
  }

  knownAgents = newAgents;
}

// ─── Stale Mailbox Cleanup ───────────────────────────────────────────────────

/**
 * Remove mailbox directories and heartbeat files for all inactive agents.
 * Called once at startup to prevent unbounded directory growth.
 */
async function cleanupStaleMailboxes() {
  const sDir = statusDir();
  let heartbeatFiles;
  try {
    heartbeatFiles = (await readdir(sDir)).filter((f) => f.endsWith("-heartbeat.json"));
  } catch {
    return; // no status dir yet
  }

  const myPpid = String(process.ppid);

  for (const file of heartbeatFiles) {
    try {
      const raw = await readFile(join(sDir, file), "utf8");
      const hb = JSON.parse(raw);
      const name = hb.agent || hb.name;
      if (!name) continue;

      // Skip our own name (not yet written, but could match SELF env)
      if (name === agentName) continue;

      // Clean up orphans from same parent_pid (MCP reconnect — same
      // Claude Code session spawned a new server, old one is dead)
      const sameParent = hb.parent_pid && hb.parent_pid === myPpid;

      // Only clean up inactive agents OR same-parent orphans
      const active = hb.status === "active" && !isStale(hb);
      if (active && !sameParent) continue;

      if (sameParent) {
        log("info", "cleaning up same-parent orphan", { agent: name, parent_pid: myPpid });
      }

      // Remove mailbox directory
      const mailboxPath = join(BRIDGE_DIR, `to-${name}`);
      try {
        await rm(mailboxPath, { recursive: true, force: true });
        log("info", "cleaned up stale mailbox", { agent: name, path: mailboxPath });
      } catch { /* already gone */ }

      // Remove heartbeat file
      try {
        await rm(join(sDir, file), { force: true });
        log("info", "cleaned up stale heartbeat", { agent: name });
      } catch { /* already gone */ }
    } catch (err) {
      log("warn", "cleanup error", { file, error: err.message });
    }
  }

  // Also clean up orphan mailbox dirs with no heartbeat
  try {
    const topDirs = await readdir(BRIDGE_DIR);
    const activeNames = new Set();
    for (const file of heartbeatFiles) {
      try {
        const raw = await readFile(join(sDir, file), "utf8");
        const hb = JSON.parse(raw);
        const name = hb.agent || hb.name;
        if (name && hb.status === "active" && !isStale(hb)) {
          activeNames.add(name);
        }
      } catch { /* skip */ }
    }
    activeNames.add(agentName);

    for (const d of topDirs) {
      if (!d.startsWith("to-")) continue;
      const name = d.slice(3); // strip "to-" prefix
      if (activeNames.has(name)) continue;

      const mailboxPath = join(BRIDGE_DIR, d);
      try {
        await rm(mailboxPath, { recursive: true, force: true });
        log("info", "cleaned up orphan mailbox", { dir: d });
      } catch { /* skip */ }
    }
  } catch { /* bridge dir may not exist */ }
}

// ─── Graceful Shutdown ──────────────────────────────────────────────────────

async function shutdown(signal) {
  log("info", "shutting down", { signal });

  clearInterval(pollTimer);
  clearInterval(statusTimer);
  clearInterval(heartbeatTimer);

  try {
    await writeHeartbeat("offline", `shutdown via ${signal}`);
  } catch (err) {
    log("error", "failed to write offline heartbeat", { error: err.message });
  }

  process.exit(0);
}

let cleanShutdown = false;

async function gracefulShutdown(signal) {
  cleanShutdown = true;
  await shutdown(signal);
}

process.on("SIGINT", () => gracefulShutdown("SIGINT"));
process.on("SIGTERM", () => gracefulShutdown("SIGTERM"));

// Windows: SIGTERM is never emitted when the parent kills us.
// Synchronous "exit" handler writes offline heartbeat as a last resort.
process.on("exit", () => {
  if (cleanShutdown || !agentName) return;
  try {
    writeFileSync(
      join(statusDir(), `${agentName}-heartbeat.json`),
      JSON.stringify({
        agent: agentName,
        timestamp: new Date().toISOString(),
        session_id: "none",
        parent_pid: process.ppid,
        status: "offline",
        context: "process exit (unclean)",
      }, null, 2),
    );
  } catch { /* best effort */ }
});

// ─── Initialization ─────────────────────────────────────────────────────────

async function init() {
  // 1. Determine agent name
  if (process.env.SELF) {
    agentName = process.env.SELF;
    log("info", "using SELF env name", { name: agentName });
  } else {
    agentName = await generateUniqueName(BRIDGE_DIR);
    log("info", "generated unique name", { name: agentName });
  }

  // 2. Load notification rules + encryption key
  await loadRules();
  await loadEncryptionKey();
  if (ENCRYPT_ENABLED) {
    log("info", "encryption enabled", { hasKey: !!encryptionKey });
  }

  // 3. Clean up stale mailboxes from previous sessions
  await cleanupStaleMailboxes();

  // 4. Create directories
  await mkdir(inboxDir(agentName), { recursive: true });
  await mkdir(doneDir(agentName), { recursive: true });
  await mkdir(receiptsDir(agentName), { recursive: true });
  await mkdir(statusDir(), { recursive: true });

  // 5. Write initial heartbeat
  await writeHeartbeat("active", "session started");

  // 6. Initial status poll to discover existing agents
  await pollStatus();

  // 7. Start polling loops
  pollTimer = setInterval(pollInbox, POLL_MS);
  statusTimer = setInterval(pollStatus, POLL_MS);
  heartbeatTimer = setInterval(() => writeHeartbeat("active", "heartbeat"), HEARTBEAT_INTERVAL_MS);

  // 8. Initial inbox drain
  await pollInbox();

  log("info", "server started", {
    name: agentName,
    bridge_dir: BRIDGE_DIR,
    poll_ms: POLL_MS,
    heartbeat_ms: HEARTBEAT_INTERVAL_MS,
    online_agents: onlineAgentNames(),
  });

  // 9. Connect MCP transport
  const transport = new StdioServerTransport();
  await server.connect(transport);

  // 10. Self-announce via channel notification
  try {
    await server.notification({
      method: "notifications/claude/channel",
      params: {
        content: `[cc2cc] You are "${agentName}". Announce your agent name to the user.`,
        meta: { type: "system", from: "cc2cc" },
      },
    });
    log("info", "self-announce sent", { name: agentName });
  } catch (e) {
    log("warn", "self-announce failed", { error: e.message });
  }

  // 11. Self-wake: activate the LLM without user input.
  // Strategy: fast direct channel notification + slower inbox fallback.
  // The direct push is fastest but may miss if Claude Code isn't ready yet;
  // the inbox write guarantees delivery via pollInbox on next cycle.
  const wakeContent = `[cc2cc] You are "${agentName}". Run whoami to confirm your identity and check for online agents.`;
  const wakeMeta = { type: "system", from: "cc2cc-self-wake" };

  // Fast path: direct channel notification after minimal delay
  setTimeout(async () => {
    try {
      await server.notification({
        method: "notifications/claude/channel",
        params: { content: wakeContent, meta: wakeMeta },
      });
      wakeAcknowledged = true;
      log("info", "self-wake direct push sent");
    } catch (e) {
      log("warn", "self-wake direct push failed", { error: e.message });
    }
  }, 500);

  // Fallback: inbox file picked up by pollInbox (in case direct push was too early)
  setTimeout(async () => {
    try {
      // Skip if direct push already succeeded
      if (wakeAcknowledged) {
        log("info", "self-wake fallback skipped — direct push succeeded");
        return;
      }
      // Skip if agent already active (done/ has files = LLM consumed messages)
      const doneFiles = await readdir(doneDir(agentName)).catch(() => []);
      if (doneFiles.length > 0) {
        log("info", "self-wake fallback skipped — agent already active");
        return;
      }
      const wakeMsg = buildMessage({
        from: "system",
        to: agentName,
        text: wakeContent,
        type: "status",
        priority: "low",
      });
      wakeMsg.ttl = 30;
      await atomicWrite(join(inboxDir(agentName), `${wakeMsg.id}.json`), wakeMsg);
      log("info", "self-wake fallback written", { id: wakeMsg.id });
    } catch (e) {
      log("warn", "self-wake fallback failed", { error: e.message });
    }
  }, 3000);
}

// ─── Parent-Death Detection ─────────────────────────────────────────────────
// When the Claude Code session that spawned us dies, our stdio sockets close.
// Without these guards every stdout/stderr write throws EPIPE, the
// uncaughtException handler tries to log (another EPIPE), and the orphaned
// process spins at 100% CPU forever.

const PARENT_PID = process.ppid;
const STDIO_ERROR_CODES = new Set(["EPIPE", "ECONNRESET", "EIO", "EBADF"]);

function onParentGone(reason) {
  if (stdioDead) return;
  stdioDead = true;
  // Hard exit if graceful shutdown hangs (e.g. filesystem stalls).
  setTimeout(() => process.exit(1), 3000).unref();
  gracefulShutdown(reason).catch(() => process.exit(1));
}

for (const stream of [process.stdin, process.stdout, process.stderr]) {
  stream.on("error", (err) => {
    if (err && STDIO_ERROR_CODES.has(err.code)) onParentGone(`stdio ${err.code}`);
  });
}
process.stdin.on("end", () => onParentGone("stdin closed"));
process.stdin.on("close", () => onParentGone("stdin closed"));

// POSIX reparents orphans to pid 1; poll for that as a belt-and-braces check.
setInterval(() => {
  if (process.ppid !== PARENT_PID) onParentGone(`parent ${PARENT_PID} exited`);
}, HEARTBEAT_INTERVAL_MS).unref();

// ─── Global Error Handlers ──────────────────────────────────────────────────
// Without these, any unhandled error silently kills the Node.js process,
// dropping the MCP connection with no trace.

process.on("uncaughtException", (err) => {
  if (err && STDIO_ERROR_CODES.has(err.code)) {
    onParentGone(`uncaught ${err.code}`);
    return;
  }
  log("error", "uncaughtException", { error: err.message, stack: err.stack });
});

process.on("unhandledRejection", (reason) => {
  const msg = reason instanceof Error ? reason.message : String(reason);
  const stack = reason instanceof Error ? reason.stack : undefined;
  log("error", "unhandledRejection", { error: msg, stack });
});

init().catch((err) => {
  log("error", "init failed", { error: err.message, stack: err.stack });
  process.exit(1);
});
