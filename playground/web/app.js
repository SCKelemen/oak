import { CompilerSession } from "./compiler-session.js";
const $ = (id) => document.getElementById(id);
const compiler = new CompilerSession();
let runner, timer, sequence = 0, artifact = null;
function stop() {
  sequence++;
  clearTimeout(timer);
  compiler.cancelPending();
  runner?.terminate();
  runner = null;
  $("compile").disabled = false;
  $("run").disabled = false;
  $("stop").disabled = true;
}
function error(message) {
  $("output").textContent = String(message).slice(0, 8192);
  stop();
}
function deadline(ms, message) {
  clearTimeout(timer);
  timer = setTimeout(() => error(message), ms);
}
$("source").oninput = () => {
  stop();
  artifact = null;
  $("download").disabled = true;
  $("artifact").textContent = "Source changed. No current artifact.";
  $("verification").textContent =
    "Source not checked. Module not validated. Translation not formally verified.";
  $("output").textContent = "Source changed. Compile to check and run.";
  $("diagnostics").replaceChildren();
  $("timing").textContent = "No current request timing.";
};
$("stop").onclick = () => {
  compiler.cancel();
  error("Stopped. Workers discarded.");
};
addEventListener("pagehide", () => {
  compiler.cancel();
  stop();
});

// textarea selection indices and compiler ranges are both UTF-16. Refuse
// malformed/out-of-source locations instead of silently clamping a highlight.
function sourceOffset(source, position) {
  if (
    !Number.isSafeInteger(position?.line) || position.line < 0 ||
    !Number.isSafeInteger(position?.character) || position.character < 0
  ) return null;
  const lines = source.split("\n");
  if (
    position.line >= lines.length ||
    position.character > lines[position.line].length
  ) return null;
  let offset = position.character;
  for (let i = 0; i < position.line; i++) offset += lines[i].length + 1;
  // Do not split a surrogate pair even when the numeric range is in bounds.
  if (
    offset > 0 && /[\uD800-\uDBFF]/.test(source[offset - 1]) &&
    /[\uDC00-\uDFFF]/.test(source[offset] ?? "")
  ) return null;
  return offset;
}

function showDiagnostics(response, source) {
  const list = $("diagnostics");
  list.replaceChildren();
  for (
    const d
      of (Array.isArray(response.diagnostics)
        ? response.diagnostics.slice(0, 64)
        : [])
  ) {
    if (!d || typeof d.message !== "string") continue;
    const item = document.createElement("li");
    const start = sourceOffset(source, d.range?.start);
    const end = sourceOffset(source, d.range?.end);
    const text = String(d.severity ?? "diagnostic").slice(0, 32) + " " +
      String(d.code ?? "").slice(0, 128) + ": " + d.message.slice(0, 8192);
    if (start !== null && end !== null && start <= end) {
      const button = document.createElement("button");
      button.textContent = `${d.range.start.line + 1}:${
        d.range.start.character + 1
      } ${text}`;
      button.onclick = () => {
        if ($("source").value !== source) return;
        $("source").focus();
        $("source").setSelectionRange(start, end);
      };
      item.append(button);
    } else item.textContent = text;
    list.append(item);
  }
  if (response.diagnosticsTruncated) {
    const item = document.createElement("li");
    item.textContent = "Additional diagnostics omitted (64-diagnostic limit).";
    list.append(item);
  }
}
async function sha256(bytes) {
  const hash = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
  return Array.from(hash, (b) => b.toString(16).padStart(2, "0")).join("");
}
$("compile").onclick = () => compile(false);
$("run").onclick = () => compile(true);
async function compile(runAfter) {
  stop();
  const current = sequence;
  artifact = null;
  $("download").disabled = true;
  $("artifact").textContent = "No artifact yet.";
  $("diagnostics").replaceChildren();
  $("timing").textContent = "Request pending.";
  $("verification").textContent =
    "Source not checked. Module not validated. Translation not formally verified.";
  const source = $("source").value;
  const sourceBytes = new TextEncoder().encode(source);
  if (sourceBytes.length > 32768) {
    error("Source exceeds 32 KiB.");
    return;
  }
  $("run").disabled = true;
  $("compile").disabled = true;
  $("stop").disabled = false;
  $("output").textContent = compiler.ready
    ? "Checking source and compiling…"
    : "Loading local compiler…";
  try {
    const { response, timing } = await compiler.compile(source);
    if (current !== sequence) return;
    $("timing").textContent = JSON.stringify(timing, null, 2);
    if (!response || typeof response !== "object") {
      throw Error("Malformed compiler response.");
    }
    if (response.error) {
      const sourceHash = await sha256(sourceBytes);
      if (current !== sequence) return;
      if (sourceHash !== response.sourceSHA256) {
        throw Error("Diagnostic source hash does not match actual bytes.");
      }
      showDiagnostics(response, source);
      error(response.error);
      return;
    }
    if (
      response.sourceChecked !== true ||
      response.module?.profile !== "oak.wasm.scalar.v1" ||
      response.module.translationVerified !== false
    ) {
      throw Error("Unexpected verification claim.");
    }
    const byteCheck = response.module.byteValidation;
    if (
      byteCheck?.validator !== "oak.wasm.check.v1" ||
      byteCheck.profile !== response.module.profile ||
      byteCheck.sha256 !== response.moduleSHA256
    ) {
      throw Error("Missing or mismatched byte-validation report.");
    }
    if (
      typeof response.module.bytes !== "string" ||
      response.module.bytes.length > 1398104
    ) {
      throw Error("Encoded module exceeds playground limit.");
    }
    const raw = atob(response.module.bytes);
    if (raw.length > 1048576) throw Error("Module exceeds playground limit.");
    const bytes = Uint8Array.from(raw, (c) => c.charCodeAt(0));
    const [sourceHash, moduleHash] = await Promise.all([
      sha256(sourceBytes),
      sha256(bytes),
    ]);
    if (current !== sequence) return; // edited/stopped while hashing
    if (
      sourceHash !== response.sourceSHA256 ||
      moduleHash !== response.moduleSHA256
    ) {
      throw Error("Source or module hash does not match actual bytes.");
    }
    if (!WebAssembly.validate(bytes)) {
      throw Error("Engine rejected emitted bytes.");
    }
    showDiagnostics(response, source);
    artifact = bytes;
    $("verification").textContent =
      "Source checked. Oak byte validator accepted. Wasm engine validated the bytes. Translation NOT formally verified.";
    $("artifact").textContent = JSON.stringify(
      {
        profile: response.module.profile,
        bytes: artifact.length,
        sourceSHA256: response.sourceSHA256,
        moduleSHA256: response.moduleSHA256,
        byteValidation: byteCheck,
        pipeline: response.pipeline,
        exports: response.module.exports,
      },
      null,
      2,
    );
    $("download").disabled = false;
    if (!runAfter) {
      $("output").textContent = "Compiled " + artifact.length +
        " bytes. Not executed.";
      stop();
      return;
    }
    const main = response.module.exports.find((e) => e.name === "main");
    if (!main || main.parameters.length) {
      error("Compiled successfully. Add a zero-argument main to run.");
      return;
    }
    $("output").textContent = "Running in isolated worker…";
    runner = new Worker("run-worker.js");
    runner.onerror = (event) => {
      if (current === sequence) error(event.message);
    };
    runner.onmessage = ({ data }) => {
      if (current !== sequence) return;
      if (data.kind === "error") {
        error(data.error);
        return;
      }
      // JS exposes i32/i64 as signed carriers. Restore Oak's unsigned display.
      let result = data.result;
      if (main.result === "u32") result = String(Number(result) >>> 0);
      if (main.result === "u64") {
        result = String(BigInt.asUintN(64, BigInt(result)));
      }
      if (main.result === "Bool") result = result === "0" ? "false" : "true";
      $("output").textContent = "Result: " + result;
      stop();
    };
    deadline(2000, "Execution exceeded 2 seconds. Worker terminated.");
    runner.postMessage({ bytes: artifact });
  } catch (failure) {
    if (current === sequence) {
      compiler.cancel(); // discard a protocol/admission failure, not ordinary source errors
      error(failure);
    }
  }
}
$("download").onclick = () => {
  if (!artifact) return;
  const url = URL.createObjectURL(
    new Blob([artifact], { type: "application/wasm" }),
  );
  const link = document.createElement("a");
  link.href = url;
  link.download = "program.wasm";
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
};
stop(); // enable controls only once the module and all handlers are installed
