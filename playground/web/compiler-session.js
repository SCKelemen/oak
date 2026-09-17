// Reuse only the loaded Go runtime, never semantic state or admitted artifacts.
export const COMPILER_PROTOCOL = "oak.compiler-worker.v1";
export const MAX_SESSION_REQUESTS = 32;

export class CompilerSession {
  constructor({
    createWorker = () =>
      new Worker(new URL("./compiler-worker.js", import.meta.url)),
    startupMs = 90000,
    requestMs = 10000,
    idleMs = 60000,
    now = () => performance.now(),
    // Do not invoke Window host methods with the session as their receiver.
    setTimer = (fn, ms) => setTimeout(fn, ms),
    clearTimer = (id) => clearTimeout(id),
  } = {}) {
    Object.assign(this, {
      createWorker,
      startupMs,
      requestMs,
      idleMs,
      now,
      setTimer,
      clearTimer,
    });
    this.worker = null;
    this.pending = null;
    this.nextID = 0;
    this.ready = false;
    this.completed = 0;
    this.timer = null;
  }

  compile(source) {
    if (this.pending) {
      return Promise.reject(Error("A compilation is already active."));
    }
    if (
      typeof source !== "string" ||
      new TextEncoder().encode(source).length > 32768
    ) {
      return Promise.reject(Error("Expected source text of at most 32 KiB."));
    }
    if (!Number.isSafeInteger(this.nextID + 1)) {
      this.cancel();
      return Promise.reject(
        Error("Compiler request identity exhausted. Reload the page."),
      );
    }
    this.clearTimer(this.timer);
    return new Promise((resolve, reject) => {
      this.pending = {
        id: ++this.nextID,
        source,
        resolve,
        reject,
        started: this.now(),
        reusedCompiler: this.ready,
        startupMs: 0,
      };
      try {
        if (this.ready) {
          this.send();
          return;
        }
        const worker = this.createWorker();
        this.worker = worker;
        worker.onmessage = ({ data }) => {
          if (worker !== this.worker) return; // terminated worker's queued event
          try {
            this.receive(data);
          } catch (error) {
            this.fail(error);
          }
        };
        worker.onerror = (event) => {
          if (worker === this.worker) {
            this.fail(Error(String(event.message).slice(0, 8192)));
          }
        };
        worker.onmessageerror = () => {
          if (worker === this.worker) {
            this.fail(Error("Cannot decode compiler message."));
          }
        };
        this.timer = this.setTimer(
          () => this.fail(Error("Compiler startup exceeded 90 seconds.")),
          this.startupMs,
        );
      } catch (error) {
        this.fail(error);
      }
    });
  }

  send() {
    const p = this.pending;
    this.clearTimer(this.timer);
    p.sent = this.now();
    this.timer = this.setTimer(
      () =>
        this.fail(Error("Compilation exceeded 10 seconds. Worker terminated.")),
      this.requestMs,
    );
    this.worker.postMessage({
      protocol: COMPILER_PROTOCOL,
      id: p.id,
      source: p.source,
    });
  }

  receive(data) {
    if (data?.protocol !== COMPILER_PROTOCOL) {
      throw Error("Unsupported compiler-worker protocol.");
    }
    if (data.kind === "ready") {
      if (this.ready || !this.pending) {
        throw Error("Unexpected compiler ready message.");
      }
      this.ready = true;
      this.pending.startupMs = this.now() - this.pending.started;
      this.send();
      return;
    }
    // Startup failures have no request ID; all request replies must echo it.
    if (!this.ready && data.kind === "error") {
      throw Error(String(data.error).slice(0, 8192));
    }
    if (!this.pending || data.id !== this.pending.id) return;
    if (data.kind === "error") throw Error(String(data.error).slice(0, 8192));
    if (
      data.kind !== "compiled" || !this.ready ||
      !data.response || typeof data.response !== "object" ||
      !Number.isFinite(data.compileMs) || data.compileMs < 0
    ) {
      throw Error("Malformed compiler response.");
    }
    const p = this.pending;
    const timing = {
      reusedCompiler: p.reusedCompiler,
      startupMs: p.startupMs,
      compileMs: data.compileMs,
      roundTripMs: this.now() - p.sent,
    };
    this.pending = null;
    this.clearTimer(this.timer);
    if (++this.completed >= MAX_SESSION_REQUESTS) this.discard();
    else this.timer = this.setTimer(() => this.discard(), this.idleMs);
    p.resolve({ response: data.response, timing });
  }

  discard() {
    this.clearTimer(this.timer);
    this.worker?.terminate();
    this.worker = null;
    this.ready = false;
    this.completed = 0;
  }

  fail(error) {
    const p = this.pending;
    this.pending = null;
    this.discard();
    p?.reject(error);
  }

  cancel() {
    this.fail(new DOMException("Compilation cancelled.", "AbortError"));
  }
  cancelPending() {
    if (this.pending) this.cancel();
  }
}
