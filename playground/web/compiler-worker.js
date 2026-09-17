"use strict";
importScripts("wasm_exec.js");
let ready = false;
globalThis.oakCompilerReady = () => { ready = true; postMessage({ kind: "ready" }); };
self.onmessage = ({ data }) => {
  if (!ready || typeof data?.source !== "string" || new TextEncoder().encode(data.source).length > 32768) {
    postMessage({ kind: "error", error: "Compiler not ready or source exceeds 32 KiB." }); return;
  }
  try { postMessage({ kind: "compiled", response: JSON.parse(globalThis.oakCompile(data.source)) }); }
  catch (error) { postMessage({ kind: "error", error: String(error).slice(0, 8192) }); }
};
(async () => {
  const go = new Go();
  const response = await fetch("oakc.wasm");
  if (!response.ok) throw Error("Build oakc.wasm with playground/build.sh first.");
  const { instance } = await WebAssembly.instantiate(await response.arrayBuffer(), go.importObject);
  await go.run(instance);
})().catch(error => postMessage({ kind: "error", error: String(error).slice(0, 8192) }));
