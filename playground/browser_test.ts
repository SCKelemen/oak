// Optional real-browser smoke test, no npm dependencies.
// deno run --allow-read --allow-write=/tmp --allow-net=127.0.0.1 --allow-run playground/browser_test.ts /path/to/chrome
const chromePath = Deno.args[0];
if (!chromePath) throw Error("Pass a Chrome/Chromium executable path.");
const profile = await Deno.makeTempDir({
  dir: "/tmp",
  prefix: "oak-browser-smoke-",
});
const files = new Set([
  "index.html",
  "app.js",
  "compiler-session.js",
  "compiler-worker.js",
  "run-worker.js",
  "style.css",
  "oakc.wasm",
  "wasm_exec.js",
]);
const server = Deno.serve(
  { hostname: "127.0.0.1", port: 0, onListen() {} },
  async (request) => {
    const name = new URL(request.url).pathname.slice(1) || "index.html";
    if (!files.has(name)) return new Response("Not found", { status: 404 });
    const type = name.endsWith(".wasm")
      ? "application/wasm"
      : name.endsWith(".js")
      ? "text/javascript"
      : name.endsWith(".css")
      ? "text/css"
      : "text/html";
    return new Response(
      await Deno.readFile(new URL("web/" + name, import.meta.url)),
      {
        headers: { "Content-Type": type, "X-Content-Type-Options": "nosniff" },
      },
    );
  },
);
const chrome = new Deno.Command(chromePath, {
  args: [
    "--headless=new",
    "--no-first-run",
    "--no-default-browser-check",
    "--disable-background-networking",
    "--remote-debugging-port=0",
    "--remote-debugging-address=127.0.0.1",
    "--user-data-dir=" + profile,
    "about:blank",
  ],
  stdout: "null",
  stderr: "null",
}).spawn();
let socket: WebSocket | undefined;
const sleep = (ms: number) => new Promise((resolve) => setTimeout(resolve, ms));
try {
  let port = "";
  for (let i = 0; i < 100; i++) {
    try {
      port = (await Deno.readTextFile(profile + "/DevToolsActivePort")).split(
        "\n",
      )[0];
      break;
    } catch {
      await sleep(100);
    }
  }
  if (!port) throw Error("Chrome did not start.");
  const pages = await (await fetch("http://127.0.0.1:" + port + "/json/list"))
    .json();
  socket = new WebSocket(
    pages.find((p: { type: string }) => p.type === "page").webSocketDebuggerUrl,
  );
  await new Promise<void>((resolve, reject) => {
    socket!.onopen = () => resolve();
    socket!.onerror = reject;
  });
  let next = 0;
  const pageErrors: unknown[] = [];
  type Reply = { result?: { value?: unknown }; exceptionDetails?: unknown };
  const pending = new Map<
    number,
    { resolve: (v: Reply) => void; reject: (v: unknown) => void }
  >();
  socket.onmessage = (event) => {
    const reply = JSON.parse(event.data);
    if (reply.method === "Runtime.exceptionThrown" && pageErrors.length < 16) {
      pageErrors.push(reply.params?.exceptionDetails);
    }
    const p = pending.get(reply.id);
    if (p) {
      pending.delete(reply.id);
      reply.error ? p.reject(reply.error) : p.resolve(reply.result);
    }
  };
  const call = (method: string, params = {}): Promise<Reply> =>
    new Promise((resolve, reject) => {
      const id = ++next;
      const timer = setTimeout(() => {
        pending.delete(id);
        reject(Error("Chrome protocol timeout: " + method));
      }, 15000);
      pending.set(id, {
        resolve: (value) => {
          clearTimeout(timer);
          resolve(value);
        },
        reject: (reason) => {
          clearTimeout(timer);
          reject(reason);
        },
      });
      socket!.send(JSON.stringify({ id, method, params }));
    });
  const evaluate = async (expression: string): Promise<string | boolean> => {
    const r = await call("Runtime.evaluate", {
      expression,
      returnByValue: true,
    });
    if (r.exceptionDetails) throw Error(JSON.stringify(r.exceptionDetails));
    const value = r.result?.value;
    if (
      typeof value !== "string" && typeof value !== "boolean" &&
      value !== undefined
    ) throw Error("Unexpected evaluation result");
    return value ?? "";
  };
  await call("Runtime.enable");
  await call("Page.navigate", { url: "http://127.0.0.1:" + server.addr.port });
  for (let i = 0; i < 100; i++) {
    if (await evaluate("!!document.getElementById('run')?.onclick")) break;
    await sleep(100);
  }
  if (!await evaluate("!!document.getElementById('run')?.onclick")) {
    throw Error(
      "Browser app did not initialize: " +
        JSON.stringify(pageErrors).slice(0, 8192),
    );
  }
  // Retain one real compiler response to test report corruption independently
  // of the compiler. The wrapper observes messages but does not alter them.
  await evaluate(`
    globalThis.realWorker = Worker;
    globalThis.workerProtocol = 'oak.compiler-worker.v1';
    globalThis.compilerWorkers = 0;
    globalThis.initialSource = document.getElementById('source').value;
    globalThis.compiledFixture = null;
    globalThis.Worker = class extends realWorker {
      constructor(...args) {
        super(...args);
        if (String(args[0]).endsWith('compiler-worker.js')) compilerWorkers++;
        this.addEventListener('message', ({data}) => {
          if (data.kind === 'compiled' && !data.response.error && !compiledFixture) {
            globalThis.compiledFixture = structuredClone(data.response);
          }
        });
      }
    };
    document.getElementById('run').click();
  `);
  let output = "";
  for (let i = 0; i < 300; i++) {
    output = String(
      await evaluate("document.getElementById('output').textContent"),
    );
    if (await evaluate("!document.getElementById('run').disabled")) break;
    await sleep(300);
  }
  if (output !== "Result: 4950") {
    throw Error(
      "Initial example failed: " + output + "; page exceptions: " +
        JSON.stringify(pageErrors).slice(0, 8192),
    );
  }
  if (
    !String(
      await evaluate("document.getElementById('verification').textContent"),
    ).includes("NOT formally verified")
  ) throw Error("Missing verification qualification");
  console.log(
    "PASS: browser compiler → actual Wasm → execution = 4950; verification status qualified",
  );
  if (
    !String(
      await evaluate("document.getElementById('verification').textContent"),
    ).includes("Oak byte validator accepted")
  ) {
    throw Error("Missing independent byte-validation status");
  }
  if (
    !String(await evaluate("document.getElementById('artifact').textContent"))
      .includes("wasm.admit")
  ) {
    throw Error("Missing emission DAG provenance");
  }
  const coldTiming = String(
    await evaluate("document.getElementById('timing').textContent"),
  );
  const warmTimings = [];
  // Actual sequential calls through the same Go runtime; record observations,
  // not a flaky wall-clock speed threshold.
  for (let request = 0; request < 3; request++) {
    await evaluate("document.getElementById('compile').click()");
    for (let i = 0; i < 100; i++) {
      if (await evaluate("!document.getElementById('compile').disabled")) break;
      await sleep(100);
    }
    const timing = String(
      await evaluate("document.getElementById('timing').textContent"),
    );
    const parsed = JSON.parse(timing);
    if (
      !parsed.reusedCompiler || parsed.startupMs !== 0 ||
      !await evaluate("compilerWorkers === 1") ||
      await evaluate("document.getElementById('download').disabled")
    ) {
      throw Error("Warm request reloaded compiler or lost artifact: " + timing);
    }
    warmTimings.push(parsed);
  }
  console.log(
    "PASS: one compiler worker serves cold and three warm requests",
    JSON.stringify({ cold: JSON.parse(coldTiming), warm: warmTimings }),
  );
  await evaluate(`
    document.getElementById('source').value = '/* 😀 */ main: (): i32 = missing()';
    document.getElementById('source').dispatchEvent(new Event('input'));
    document.getElementById('compile').click();
  `);
  for (let i = 0; i < 100; i++) {
    if (await evaluate("!document.getElementById('compile').disabled")) break;
    await sleep(100);
  }
  if (
    !await evaluate("!!document.querySelector('#diagnostics button')") ||
    !await evaluate("document.getElementById('download').disabled")
  ) {
    throw Error("Missing structured diagnostic or invalid-source cleanup");
  }
  await evaluate(
    "[...document.querySelectorAll('#diagnostics button')].find(b => b.textContent.includes('missing')).click()",
  );
  if (
    !await evaluate(
      "document.getElementById('source').selectionStart === document.getElementById('source').value.indexOf('missing')",
    )
  ) {
    throw Error("Diagnostic did not navigate to UTF-16 source location");
  }
  await evaluate(`
    document.getElementById('source').value = initialSource;
    document.getElementById('source').dispatchEvent(new Event('input'));
    document.getElementById('run').click();
  `);
  for (let i = 0; i < 100; i++) {
    if (await evaluate("!document.getElementById('run').disabled")) break;
    await sleep(100);
  }
  if (
    !await evaluate(
      "compilerWorkers === 1 && document.getElementById('output').textContent === 'Result: 4950' && document.getElementById('diagnostics').children.length === 0",
    )
  ) {
    throw Error("Source error polluted or discarded warm compiler session");
  }
  console.log(
    "PASS: UTF-16 diagnostic navigation and corrected source reuse isolated compilation state",
  );
  // Both report hashes agree with each other but not the actual valid module.
  // A string-to-string report check alone would accept this stale evidence.
  await evaluate(`
    // Explicitly reset the idle real session before installing the test worker.
    document.getElementById('stop').dispatchEvent(new Event('click'));
    globalThis.Worker = class {
      constructor() { queueMicrotask(() => this.onmessage?.({data:{protocol:workerProtocol,kind:'ready'}})); }
      postMessage({id}) {
        const response = structuredClone(compiledFixture);
        response.moduleSHA256 = '0'.repeat(64);
        response.module.byteValidation.sha256 = response.moduleSHA256;
        queueMicrotask(() => this.onmessage?.({data:{protocol:workerProtocol,id,kind:'compiled',response,compileMs:0}}));
      }
      terminate() {}
    };
    document.getElementById('compile').click();
  `);
  for (let i = 0; i < 100; i++) {
    if (await evaluate("!document.getElementById('compile').disabled")) break;
    await sleep(100);
  }
  output = String(
    await evaluate("document.getElementById('output').textContent"),
  );
  if (
    !output.includes("hash does not match actual bytes") ||
    !await evaluate("document.getElementById('download').disabled")
  ) {
    throw Error("Corrupt byte report exposed an artifact: " + output);
  }
  await evaluate("void (globalThis.Worker = realWorker)");
  console.log(
    "PASS: actual-byte hashing refuses a stale byte-admission report",
  );
  // Pause hashing after a valid response, then invalidate the source request.
  // Resolving that old asynchronous work must not restore an artifact.
  await evaluate(`
    globalThis.realDigest = crypto.subtle.digest.bind(crypto.subtle);
    globalThis.pendingDigests = [];
    crypto.subtle.digest = (...args) => new Promise((resolve, reject) => {
      pendingDigests.push(() => realDigest(...args).then(resolve, reject));
    });
    globalThis.Worker = class {
      constructor() { queueMicrotask(() => this.onmessage?.({data:{protocol:workerProtocol,kind:'ready'}})); }
      postMessage({id}) { queueMicrotask(() => this.onmessage?.({data:{protocol:workerProtocol,id,kind:'compiled',response:structuredClone(compiledFixture),compileMs:0}})); }
      terminate() {}
    };
    document.getElementById('compile').click();
  `);
  for (let i = 0; i < 100; i++) {
    if (await evaluate("pendingDigests.length === 2")) break;
    await sleep(100);
  }
  if (!await evaluate("pendingDigests.length === 2")) {
    throw Error("Did not reach asynchronous hash boundary");
  }
  await evaluate(`
    document.getElementById('source').dispatchEvent(new Event('input'));
    document.getElementById('stop').dispatchEvent(new Event('click'));
    crypto.subtle.digest = realDigest;
    globalThis.Worker = realWorker;
    pendingDigests.forEach((release) => release());
  `);
  await sleep(100);
  if (
    !String(await evaluate("document.getElementById('artifact').textContent"))
      .includes("No current artifact")
  ) {
    throw Error("Stale asynchronous hashing restored an artifact");
  }
  console.log(
    "PASS: source invalidation discards stale asynchronous hash results",
  );
  if (!await evaluate("document.getElementById('download').disabled")) {
    throw Error("Editing source retained stale download");
  }
  await evaluate(
    "document.getElementById('source').value='main: (): u32 { i: u32 = 0; while i == i { i = i + u32(1) }; i }'; document.getElementById('compile').click()",
  );
  for (let i = 0; i < 300; i++) {
    if (await evaluate("!document.getElementById('compile').disabled")) break;
    await sleep(300);
  }
  output = String(
    await evaluate("document.getElementById('output').textContent"),
  );
  if (
    !output.endsWith("Not executed.") ||
    await evaluate("document.getElementById('download').disabled")
  ) {
    throw Error("Compile-only ran or failed to publish the loop: " + output);
  }
  console.log(
    "PASS: Compile only admits and downloads an infinite loop without executing it",
  );
  await evaluate("document.getElementById('run').click()");
  for (let i = 0; i < 300; i++) {
    output = String(
      await evaluate("document.getElementById('output').textContent"),
    );
    if (await evaluate("!document.getElementById('run').disabled")) break;
    await sleep(300);
  }
  if (!output.includes("Execution exceeded 2 seconds")) {
    throw Error("Infinite-loop cancellation failed: " + output);
  }
  console.log(
    "PASS: infinite user loop terminated without freezing the editor",
  );
  await evaluate(
    "document.getElementById('source').value='main: (): i32 = missing()'; document.getElementById('run').click()",
  );
  for (let i = 0; i < 300; i++) {
    output = String(
      await evaluate("document.getElementById('output').textContent"),
    );
    if (await evaluate("!document.getElementById('run').disabled")) break;
    await sleep(300);
  }
  if (
    !output.includes("missing") ||
    !await evaluate("document.getElementById('download').disabled")
  ) throw Error("Invalid source exposed an artifact: " + output);
  console.log(
    "PASS: bad source reports diagnostics and invalidates previous artifact",
  );
} finally {
  socket?.close();
  try {
    chrome.kill("SIGTERM");
  } catch { /* already exited */ }
  await chrome.status;
  await server.shutdown();
  await Deno.remove(profile, { recursive: true });
}
