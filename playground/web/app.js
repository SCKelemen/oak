"use strict";
const $ = (id) => document.getElementById(id);
let compiler, runner, timer, sequence = 0, artifact = null;
function stop() {
  sequence++;
  clearTimeout(timer);
  compiler?.terminate();
  runner?.terminate();
  compiler = runner = null;
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
};
$("stop").onclick = () => {
  error("Stopped. Workers discarded.");
};
async function sha256(bytes) {
  const hash = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
  return Array.from(hash, (b) => b.toString(16).padStart(2, "0")).join("");
}
$("compile").onclick = () => compile(false);
$("run").onclick = () => compile(true);
function compile(runAfter) {
  stop();
  const current = sequence;
  artifact = null;
  $("download").disabled = true;
  $("artifact").textContent = "No artifact yet.";
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
  $("output").textContent = "Loading local compiler…";
  compiler = new Worker("compiler-worker.js");
  compiler.onerror = (event) => {
    if (current === sequence) error(event.message);
  };
  deadline(90000, "Compiler startup exceeded 90 seconds.");
  compiler.onmessage = async ({ data }) => {
    if (current !== sequence) return;
    if (data.kind === "ready") {
      $("output").textContent = "Checking source and compiling…";
      deadline(
        10000,
        "Compilation exceeded 10 seconds. Try a smaller program.",
      );
      compiler.postMessage({ source });
      return;
    }
    if (data.kind === "error") {
      error(data.error);
      return;
    }
    if (data.kind !== "compiled") return;
    clearTimeout(timer);
    compiler.terminate();
    compiler = null;
    const response = data.response;
    try {
      if (!response || typeof response !== "object") {
        throw Error("Malformed compiler response.");
      }
      if (response.error) {
        error(response.error);
        return;
      }
      if (
        response.sourceChecked !== true ||
        response.module.translationVerified !== false
      ) {
        throw Error("Unexpected verification claim.");
      }
      const byteCheck = response.module.byteValidation;
      if (
        byteCheck?.validator !== "oak.wasm.check.v0" ||
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
      if (current === sequence) error(failure);
    }
  };
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
