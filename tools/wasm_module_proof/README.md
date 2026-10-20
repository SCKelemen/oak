# Source-bound complete Wasm module proof gate

Run `python3 tools/wasm_module_proof/check.py --lake /absolute/path/to/lake`.
The existing required `TestLeanWasmBitwiseModuleFaithful` Go test invokes this
checker after its unchanged source-extraction correspondence check. It first
runs `test_check.py`, including negative axiom-report controls.

The checker requires official Lean 4.33.1. It discovers all local transitive
imports of `Oak.WasmBitwiseModuleExact`, rebuilds every one from current source
into a fresh temporary directory with `-j1 -t0 -M2048`, then checks an exact
16-theorem axiom inventory and the complete module controls with the same
trust-zero settings. Only official core/Std artifacts are reused. Candidate
`.olean` paths are absent from `LEAN_PATH`. Each source, the committed audit
inventory, and controls are hashed before/after the build; identities are printed
with the successful result. Unexpected, missing, duplicate, or nonstandard
axiom reports fail. The committed audit module must exactly match the gate's
inventory. There is no private checker or native evaluation shortcut.

The scope is the actual extracted module writer's valid success domain and
supplementary valid-profile capacity refusal, using the existing disjoint-array
extraction model. It is not a proof of extraction/compiler correctness or a
source parser. See `docs/spec/91-wasm-module-exact-proof.md` for all premises and
remaining boundaries. The previous finite 106-claim source/compiler corpus is
retained separately and unchanged.
