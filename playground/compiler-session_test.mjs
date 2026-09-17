import assert from "node:assert/strict";
import { test } from "node:test";
import { readFileSync } from "node:fs";
import { createContext, runInContext } from "node:vm";
import {
  COMPILER_PROTOCOL,
  CompilerSession,
  MAX_SESSION_REQUESTS,
} from "./web/compiler-session.js";

function harness() {
  const workers = [], timers = new Map();
  let clock = 0, nextTimer = 0;
  const session = new CompilerSession({
    createWorker() {
      const worker = {
        sent: [],
        terminated: false,
        postMessage(data) {
          this.sent.push(data);
        },
        terminate() {
          this.terminated = true;
        },
        emit(data) {
          this.onmessage({ data: { protocol: COMPILER_PROTOCOL, ...data } });
        },
        ready() {
          this.emit({ kind: "ready" });
        },
        finish(response = { sourceChecked: true }, extra = {}) {
          this.emit({
            kind: "compiled",
            id: this.sent.at(-1)?.id,
            compileMs: 2,
            response,
            ...extra,
          });
        },
      };
      workers.push(worker);
      return worker;
    },
    now: () => clock,
    setTimer(fn, ms) {
      const id = ++nextTimer;
      timers.set(id, { fn, ms });
      return id;
    },
    clearTimer(id) {
      timers.delete(id);
    },
  });
  return {
    session,
    workers,
    timers,
    tick(ms) {
      clock += ms;
    },
    expire(ms) {
      const due = [...timers.values()].filter((t) => t.ms === ms);
      assert.equal(due.length, 1);
      due[0].fn();
    },
  };
}

test("cold then warm requests reuse runtime, including after a source error", async () => {
  const h = harness(), s = h.session;
  const cold = s.compile("one");
  const w = h.workers[0];
  assert.equal(w.sent.length, 0);
  h.tick(20);
  w.ready();
  h.tick(3);
  w.finish();
  assert.deepEqual((await cold).timing, {
    reusedCompiler: false,
    startupMs: 20,
    compileMs: 2,
    roundTripMs: 3,
  });
  s.cancelPending(); // editing an idle source does not discard the runtime
  const bad = s.compile("missing");
  w.finish({ error: "unknown identifier" });
  assert.equal((await bad).response.error, "unknown identifier");
  const warm = s.compile("corrected");
  h.tick(4);
  w.finish();
  assert.deepEqual((await warm).timing, {
    reusedCompiler: true,
    startupMs: 0,
    compileMs: 2,
    roundTripMs: 4,
  });
  assert.deepEqual(w.sent.map((p) => p.id), [1, 2, 3]);
  assert.deepEqual(w.sent.map((p) => p.source), [
    "one",
    "missing",
    "corrected",
  ]);
  assert.equal(h.workers.length, 1);
  s.cancel();
  assert.equal(w.terminated, true);
  assert.equal(h.timers.size, 0);
});

test("concurrent requests and oversized UTF-8 input cannot disturb active work", async () => {
  const h = harness(), s = h.session;
  await assert.rejects(s.compile("😀".repeat(8193)), /32 KiB/);
  assert.equal(h.workers.length, 0);
  const p = s.compile("first");
  await assert.rejects(s.compile("second"), /already active/);
  h.workers[0].ready();
  h.workers[0].finish();
  await p;
  s.cancel();
});

test("cancellation during startup or compile discards worker and ignores its late events", async () => {
  for (const start of [false, true]) {
    const h = harness(), s = h.session;
    const p = s.compile("old"), old = h.workers[0];
    if (start) old.ready();
    s.cancelPending();
    await assert.rejects(p, { name: "AbortError" });
    assert.equal(old.terminated, true);
    const fresh = s.compile("new"), w = h.workers[1];
    old.ready();
    old.finish();
    old.onerror({ message: "late failure" });
    assert.equal(w.sent.length, 0);
    w.ready();
    w.finish({ value: "fresh" });
    assert.equal((await fresh).response.value, "fresh");
    s.cancel();
  }
});

test("stale request IDs cannot satisfy or fail a subsequent request", async () => {
  const h = harness(), s = h.session;
  const first = s.compile("one"), w = h.workers[0];
  w.ready();
  w.finish();
  await first;
  const second = s.compile("two");
  let resolved = false;
  second.then(() => {
    resolved = true;
  });
  w.finish({ value: "stale" }, { id: 1 });
  w.emit({ kind: "error", id: 1, error: "stale error" });
  await Promise.resolve();
  assert.equal(resolved, false);
  w.finish({ value: "current" });
  assert.equal((await second).response.value, "current");
  s.cancel();
});

test("startup and compile deadlines terminate work; idle deadline releases runtime", async () => {
  for (const ready of [false, true]) {
    const h = harness(), s = h.session;
    const p = s.compile("loop"), w = h.workers[0];
    if (ready) w.ready();
    h.expire(ready ? 10000 : 90000);
    await assert.rejects(p, /exceeded/);
    assert.equal(w.terminated, true);
    assert.equal(h.timers.size, 0);
  }
  const h = harness(), p = h.session.compile("ok"), w = h.workers[0];
  w.ready();
  w.finish();
  await p;
  h.expire(60000);
  assert.equal(w.terminated, true);
  assert.equal(h.timers.size, 0);
});

test("sessions recycle after the bounded request count", async () => {
  const h = harness(), s = h.session;
  for (let i = 0; i < MAX_SESSION_REQUESTS; i++) {
    const p = s.compile(String(i)), w = h.workers[0];
    if (i === 0) w.ready();
    w.finish();
    await p;
  }
  assert.equal(h.workers[0].terminated, true);
  const p = s.compile("new session"), w = h.workers[1];
  w.ready();
  w.finish();
  assert.equal((await p).timing.reusedCompiler, false);
  assert.equal(w.sent[0].id, MAX_SESSION_REQUESTS + 1);
  s.cancel();
});

test("protocol errors, duplicate ready, malformed replies and worker faults fail closed", async () => {
  const faults = [
    (w) => w.emit({ kind: "ready", protocol: "old-protocol" }),
    (w) => {
      w.ready();
      w.ready();
    },
    (w) => {
      w.ready();
      w.finish(null);
    },
    (w) => {
      w.ready();
      w.finish({}, { compileMs: NaN });
    },
    (w) => w.emit({ kind: "error", error: "startup failed" }),
    (w) => {
      w.ready();
      w.emit({ kind: "error", id: w.sent[0].id, error: "Go panic" });
    },
    (w) => w.onerror({ message: "worker crash" }),
    (w) => w.onmessageerror(),
  ];
  for (const fault of faults) {
    const h = harness(), p = h.session.compile("test"), w = h.workers[0];
    fault(w);
    await assert.rejects(p);
    assert.equal(w.terminated, true);
    assert.equal(h.timers.size, 0);
  }
});

test("default timers do not pass the session as a Window host-method receiver", async () => {
  const originalSet = globalThis.setTimeout,
    originalClear = globalThis.clearTimeout;
  globalThis.setTimeout = function (...args) {
    assert.equal(this instanceof CompilerSession, false);
    return originalSet(...args);
  };
  globalThis.clearTimeout = function (...args) {
    assert.equal(this instanceof CompilerSession, false);
    return originalClear(...args);
  };
  const worker = { postMessage() {}, terminate() {} };
  const session = new CompilerSession({ createWorker: () => worker });
  try {
    const p = session.compile("main");
    worker.onmessage({ data: { protocol: COMPILER_PROTOCOL, kind: "ready" } });
    worker.onmessage({
      data: {
        protocol: COMPILER_PROTOCOL,
        kind: "compiled",
        id: 1,
        compileMs: 1,
        response: {},
      },
    });
    await p;
    session.cancel();
  } finally {
    globalThis.setTimeout = originalSet;
    globalThis.clearTimeout = originalClear;
    session.cancel();
  }
});

test("production worker enforces protocol, IDs, UTF-8 source and session bounds", () => {
  const replies = [], sources = [];
  const context = createContext({
    importScripts() {},
    postMessage(data) {
      replies.push(data);
    },
    TextEncoder,
    performance: { now: () => 0 },
    Go: class {
      run() {
        return new Promise(() => {});
      }
    },
    fetch: async () => ({
      ok: true,
      arrayBuffer: async () => new ArrayBuffer(0),
    }),
    WebAssembly: { instantiate: async () => ({ instance: {} }) },
    oakCompile(source) {
      sources.push(source);
      return JSON.stringify({ source });
    },
  });
  context.self = context;
  runInContext(
    readFileSync(new URL("web/compiler-worker.js", import.meta.url), "utf8"),
    context,
  );
  const send = (data) =>
    context.onmessage({ data: { protocol: COMPILER_PROTOCOL, ...data } });
  send({ id: 1, source: "before ready" });
  assert.equal(replies.at(-1).kind, "error");
  context.oakCompilerReady();
  assert.equal(replies.at(-1).protocol, COMPILER_PROTOCOL);
  assert.equal(replies.at(-1).kind, "ready");
  for (
    const data of [
      { id: 0, source: "zero" },
      { id: 1.5, source: "fraction" },
      { id: 1, source: "bad version", protocol: "old" },
      { id: 1, source: "😀".repeat(8193) },
      { id: 1, source: null },
    ]
  ) {
    send(data);
    assert.equal(replies.at(-1).kind, "error");
  }
  assert.equal(sources.length, 0);
  for (let id = 1; id <= MAX_SESSION_REQUESTS; id++) {
    send({ id, source: String(id) });
    assert.equal(replies.at(-1).kind, "compiled");
    assert.equal(replies.at(-1).id, id);
    assert.equal(replies.at(-1).response.source, String(id));
    send({ id, source: "duplicate" });
    assert.equal(replies.at(-1).kind, "error");
  }
  send({ id: MAX_SESSION_REQUESTS + 1, source: "over budget" });
  assert.equal(replies.at(-1).kind, "error");
  assert.equal(sources.length, MAX_SESSION_REQUESTS);
});
