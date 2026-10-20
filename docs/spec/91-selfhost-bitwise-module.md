# Additive Oak bitwise Wasm module producer

`asm/selfhost/bitwise_wasm.oak` defines
`wasm_bitwise_module(dst, op, name): u32`, alongside the unchanged scalar
assembler in `wasm.oak`. Operation tags are 1 (AND), 2 (OR), and 3 (XOR).
The export name is 1–256 bytes, each in 1–127. This common strict-image name
profile is intentionally narrower than the Wasm-only loader. Name and operation
are caller proposals; this routine does not parse or compile Oak source.

The writer emits the complete magic/version, type, function, export and code
sections. The sole function has two i32 parameters and one i32 result, with
zero local declarations and `local.get 0; local.get 1; op; end`. There are no
imports, memory, start, custom sections, extra functions, or trailing bytes.
The name is exported without the native `oak_` symbol prefix.

For name length n, let L be its unsigned LEB length, E = n + L + 3 the export
payload length, and P the unsigned LEB length of E. Complete size is
36 + n + L + P, between 39 and 296 bytes. Both length encodings use the existing
Oak `wasm_write_uleb`; the six instruction bytes use `wasm_assemble`.
The section-length threshold is n=124, before the name-length threshold n=128.
All op/name/capacity checks precede the first mutation. Zero indicates refusal
with the entire destination unchanged. Success reports the complete size and
preserves every following destination byte. The name and writable destination
must be disjoint, as required by Oak borrowing. The full capacity check also
makes the fixed assembler and LEB calls fit; no post-write refusal path exists.

## Evidence and exact boundary

`TestE2ESelfHostedWasmBitwiseModule` compiles the writer through the Go seed's
C backend and the system C compiler, captures the entire binary stdout without
adding an envelope in Go, and compares every byte with fresh Go `EmitWasm`
production. It covers all operations with `bitwise`, `Mix9`, and names of lengths
1, 123, 124, 127, 128 and 256, at exact capacity and with a sentinel suffix.
`TestE2ESelfHostedWasmBitwiseModuleRefusal` checks invalid operation/name inputs,
late-invalid names, length 257, and short destinations. It checks the complete
sentinel destination, both inside compiled Oak and in captured stdout.

`TestLeanWasmBitwiseModuleExtract` mechanically extracts both source files in
the existing `Oak.WasmAssembler` namespace. It requires the complete helper
prefix to equal the unchanged committed `WasmAssemblerExtracted.lean` byte for
byte, replaces only that verified prefix with an import, and verifies full
reconstruction. There are no renamed or hand-edited generated definitions.
Any helper drift or factoring mismatch fails closed. The old source, extraction,
and checker-embedded closure are unchanged.

`TestLeanWasmBitwiseModuleFaithful` kernel-checks complete-array success/refusal
results for the same finite corpus, including untouched suffixes and actual
module admission. It uses `decide +kernel`, not `native_decide`. Equipped runs
set `OAK_REQUIRE_WASM_LEAN=1`; missing Lean is then an error.

`Oak.WasmBitwiseModuleGuards` additionally proves universal early refusal for
invalid operation tags or represented name lengths, without inspecting any name
byte or changing any destination byte, even at zero extraction fuel. It proves
termination at already-false scan/copy guards. These small source-extracted laws
do not cover admitted name scans or successful emission.

These are mechanically source-tied extraction, scoped early-guard laws, and
finite correspondence checks, not a universal envelope-writer refinement. The existing `assemble_exact` and
`BitwiseFunction.emitted_function_success` theorems remain reusable foundations.
A universal join still needs the new name-scan/copy loop invariants and fuel,
representable array lengths, nonwrapping index arithmetic, every store footprint,
exact LEB/helper success at each call, complete output equality, and framing.
The extractor's `getD`/`setIfInBounds` semantics do not discharge Oak bounds checks.
No compiler/source-parser correctness, changed checker authority, Linux startup,
or whole-toolchain self-hosting claim follows from this patch.

The [raw complete-image integration](94-selfhost-image-admission.md) captures
these actual outputs for direct unchanged-checker admission and adds separate
mandatory exact producer/admission gates without replacing the existing gates.
