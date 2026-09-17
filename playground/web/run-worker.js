"use strict";
// No imports are granted to the user module. Wasm cannot reach this worker's
// JS/network/DOM APIs without explicitly provided host functions.
self.onmessage = async ({ data }) => {
  try {
    if (!(data?.bytes instanceof Uint8Array) || data.bytes.byteLength > 1048576) throw Error("Invalid module size.");
    if (!WebAssembly.validate(data.bytes)) throw Error("Engine rejected Wasm bytes.");
    const module = await WebAssembly.compile(data.bytes);
    if (WebAssembly.Module.imports(module).length) throw Error("Host imports are disabled.");
    const instance = await WebAssembly.instantiate(module, {});
    if (typeof instance.exports.main !== "function" || instance.exports.main.length !== 0) throw Error("Run requires a zero-argument main.");
    const result = instance.exports.main();
    postMessage({ kind: "result", result: String(result ?? "()"), validated: true });
  } catch (error) { postMessage({ kind: "error", error: String(error).slice(0, 8192) }); }
};
