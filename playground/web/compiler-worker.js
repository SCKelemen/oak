"use strict";
const protocol = "oak.compiler-worker.v1";
let lastID = 0, requests = 0;
importScripts("wasm_exec.js");
let ready = false;
globalThis.oakCompilerReady = () => {
  ready = true;
  postMessage({ protocol, kind: "ready" });
};
self.onmessage = ({ data }) => {
  if (
    !ready || data?.protocol !== protocol || !Number.isSafeInteger(data.id) ||
    data.id <= lastID || requests >= 32 || typeof data.source !== "string" ||
    new TextEncoder().encode(data.source).length > 32768
  ) {
    postMessage({
      protocol,
      id: data?.id,
      kind: "error",
      error: "Invalid compiler request or session limit exceeded.",
    });
    return;
  }
  lastID = data.id;
  requests++;
  try {
    const started = performance.now();
    const response = JSON.parse(globalThis.oakCompile(data.source));
    postMessage({
      protocol,
      id: data.id,
      kind: "compiled",
      response,
      compileMs: performance.now() - started,
    });
  } catch (error) {
    postMessage({
      protocol,
      id: data.id,
      kind: "error",
      error: String(error).slice(0, 8192),
    });
  }
};
(async () => {
  const go = new Go();
  const response = await fetch("oakc.wasm");
  if (!response.ok) {
    throw Error("Build oakc.wasm with playground/build.sh first.");
  }
  const { instance } = await WebAssembly.instantiate(
    await response.arrayBuffer(),
    go.importObject,
  );
  await go.run(instance);
})().catch((error) =>
  postMessage({ protocol, kind: "error", error: String(error).slice(0, 8192) })
);
