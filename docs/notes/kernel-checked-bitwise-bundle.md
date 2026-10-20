# Kernel-checked bitwise bundle API

`compiler.EmitKernelCheckedBitwiseBundle` is the optional production API for
one narrowly scoped bundle: original source bytes, a complete core/wasm32
module, a complete Linux AArch64 ELF64 ET_REL object, and a complete Linux
RV64 LP64D ELF64 ET_REL object. Every successful call independently admits
the exact tuple using the pinned Lean kernel before returning an opaque
`*bitwisecheck.CheckedBundle`.

The source grammar is canonical ASCII: one identifier-first two-`u32`
function, a colon return type, one parameter-ordered `&`, `|`, or `^`
expression, exact single spaces, and a final LF. For example:

```oak
mix: (left: u32, right: u32): u32 = left ^ right
```

This is not a general source-language or compiler-correctness claim. See the
runtime [trust and model boundaries](../../bitwisecheck/README.md) and the
bundle's receipt for the existing Wasm model, ARM register/alignment, RV64
stack-frame, native loading, and host-custody assumptions.

## Use

```go
installation, err := bitwisecheck.Install(ctx, "/path/to/lean-4.33.1-linux.tar.zst")
if err != nil {
    return err
}
defer installation.Close()

bundle, err := compiler.EmitKernelCheckedBitwiseBundle(ctx, installation,
    compiler.SourceText{
        Path: "mix.oak",
        Text: "mix: (left: u32, right: u32): u32 = left ^ right\n",
    }).Get()
if err != nil {
    return err
}
source := bundle.SourceBytes()
wasm := bundle.WasmBytes()
arm := bundle.ARM64Bytes()
rv := bundle.RV64Bytes()
receipt := bundle.Receipt()
```

The imports are `github.com/SCKelemen/oak/bitwisecheck` and
`github.com/SCKelemen/oak/compiler`. The example assumes the caller supplies
`ctx` and handles its own output destination; this API publishes no files.

Installation verifies the offline official archive against built-in pins,
extracts it privately, and freshly compiles the embedded semantic/auditor
closure. It is intentionally expensive. Reuse one installation for multiple
requests, then close it. A missing, zero, or closed installation is a hard
refusal. An authentic installation cannot be reconstructed from a caller's
manifest, previous receipt, or executable version string.

The compiler takes one snapshot of `SourceText.Text`; it does not read
`SourceText.Path` from disk. Callers loading a file should read it once. Each
target receives a fresh default compilation of that same snapshot. Final bytes
are copied before checking. There are no package, session, overlay, assembly,
target, ABI, rewrite, runner, or verification options on this API, and no C or
synthetic-sibling fallback. Getters return copies. Receipts identify historical
results and cannot be deserialized into admission authority. Rechecking stored
artifacts requires their actual source and all three byte files again.

Cancellation is observed between synchronous compiler stages and during the
independent checker process. It does not interrupt the existing synchronous
parser/lowering/emitter internals. Any compiler, bootstrap, proof, protocol,
resource, cancellation, or subprocess failure returns no checked bundle.

This API does not change `asm.VerdictProven`, the existing `-verified` profile,
or `wasm.Module.TranslationVerified`. There is no checked-bundle CLI or atomic
output-publication contract in this first API slice.

## Required equipped tests

Set `OAK_BITWISECHECK_LEAN_ARCHIVE` to the offline pinned archive and
`OAK_REQUIRE_BITWISECHECK=1`, then run:

```sh
python3 .github/scripts/required_backend_tests.py checked-bitwise-sources
python3 .github/scripts/required_backend_tests.py checked-bitwise-runtime
python3 .github/scripts/required_backend_tests.py checked-bitwise-bundle
```

The required runner rejects missing named tests and every nested skip. The
compiler matrix exercises all three operations with two identifier families:
six real bundles, eighteen final production artifacts, and three audited roots
per bundle. Further cases cover rejected sources/artifacts, copy custody,
receipt replay refusal, consistent parameter renaming with fresh admission,
stage cancellation, closure, and legacy-verdict regressions. The dedicated CI
workflow also runs the real auditor's wrong-type, axiom, kernel-policy, and
valid-record-followed-by-failure controls serially.
