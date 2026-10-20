# Exact-artifact nested Wasm call composition

`Oak.WasmCallComposition` proves all-input execution for one exact Oak source
fixture and the complete actual binary emitted for it. It is an increment on the
internal `WasmModule` / `WasmCalls` execution path, not a new source grammar or an
extension of `oak.wasm.scalar.v1`. Memory remains outside that production profile.

## Program and result

The fixture is independently pinned as `WasmCallComposition.source` and
`wasmCallCompositionSource` in the compiler regression:

```oak
difference: (x: u32, y: u32): u32 {
  temp: u32 = x - y
  temp
}
reverse: (x: u32, y: u32): u32 {
  keep: u32 = u32(99)
  result: u32 = difference(y, x)
  result + keep - keep
}
main: (a: u32, b: u32): u32 {
  keep: u32 = a + u32(7)
  result: u32 = reverse(a, b)
  result - keep - keep
}
```

For every pair of 32-bit words `a,b`, exported `main(a,b)` returns

```
(b - a) - (a + 7) - (a + 7)  modulo 2^32.
```

The actual decoded function table is in compiler order `difference, main,
reverse`. Both non-leaf functions have two extra i32 locals. Main saves `a+7`
in its local 2; reverse writes 99 to its own local 2. A local-array alias would
therefore change the observable result. Reverse passes its second parameter
before its first to a noncommutative subtraction, so argument reversal is also
observable. Function index 1 is exported as `main`; names, indices, signatures,
local declarations and all instruction tokens are checked together.

## Universal claims

- `fresh_main`, `fresh_reverse`: arbitrary arguments and arbitrary suspended
  operand suffixes produce an isolated activation, fresh zero locals, an empty
  operand stack and a fresh function label.
- `main_enters_reverse`: seven transitions of the existing call machine suspend
  main with its saved value and continuation before entering reverse.
- `reverse_returns`: eighteen transitions, including the nested call, restore
  **any** suspended caller's operands, locals, continuation, labels and outer
  callers, prepending only `b-a`. This is not restricted to an empty caller.
- `invoke_more`: successful external invocation in any function table remains
  successful with additional execution fuel.
- `invocation`: all 2^64 input pairs succeed in 32 transitions or more. The
  theorem gives the whole final state, including original parameters, saved
  `a+7`, and the returned `b-a` in main's locals.
- `insufficient_fuel`: 31 transitions exhaust the model for every input pair.
  Model fuel exhaustion is not a WebAssembly runtime trap.
- `accepted_invocation`: exact source identity and complete decoded-module
  acceptance imply the all-input named-export result, with no assumed execution
  success, signature validity or desired return value.

`advance` only iterates the existing `WasmCalls.tick`. It does not introduce a
second definition of individual instruction, activation or return semantics.

## Binding and checks

`accepts original bytes` checks byte-for-byte equality with the exact source
fixture and decodes the entire binary using `WasmModule.decode`. The decoded
module must equal the independently stated functions and export table. No body
metadata comes from the caller, no section is discarded, and trailing bytes
are refused. Semantically equivalent padded section-length LEBs are allowed;
this is structural/semantic admission, not equality with an embedded binary.

`TestWasmCallCompositionLean` compiles the original source with the real
`Compiler.EmitWasm` path, supplies those complete bytes to Lean, kernel-checks
acceptance with `decide +kernel`, and specializes `accepted_invocation` to
arbitrary inputs and extra fuel. It does not replace the compiler artifact with
a handcrafted envelope or rely on a prior byte pin. The original fixture bytes
are provided independently from the Go test and checked against the Lean pin.

The same regression checks refusal for changed original source, changed spelling
outside this singleton fixture, wrong or out-of-bounds callee indices, argument
order, arithmetic operator, local slots/counts/widths, parameter/result
signatures, early return, export routing, every strict byte prefix, and trailing
bytes. Both actual and padded-length modules have all-input theorem instances.

`TestWasmCallCompositionEngine` independently validates every binary with the
configured Node/Deno engine and checks the bounded Go validator separately.
Empty and type-only prefixes are valid Core modules but outside the executable
profile; these expected domain differences are pinned explicitly. Valid modules
run 712 invocations each: 100 boundary pairs and 256 deterministic pseudorandom
pairs, each presented in both signed and unsigned host-number form. Expected
results use independent JavaScript BigInt arithmetic. The same instance is
reused across calls; fresh zero initialization is established by the activation
proofs. Every valid semantic byte
mutation must change a tested outcome (or trap); source-only controls correctly
retain the original engine behavior while failing source-bound admission.

The Lean regression prints and checks the axiom closure of every accepted
artifact theorem, every rejection theorem and the central reusable theorems.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Missing,
duplicate or unexpected audit reports fail closed. No `sorry`, custom axiom,
`native_decide`, external source fetch or additional proof toolchain is used.

The existing required formal lane runs both tests under
`OAK_REQUIRE_WASM_LEAN=1` and `OAK_REQUIRE_WASM_TESTS=1`; `Oak.lean` imports the
new proof. The existing Wasm workflow's `TestWasm...` selection also includes
these tests, with independent engine execution required.

## Remaining boundaries

This is a proof of the internal decoded execution model for the complete
compiler artifact of **one exact source fixture**. The source equality checks
identity, not a parsing/typing/lowering derivation. The arithmetic contract is
manually reviewed against the fixture; there is no generalized source language
or universal production compiler-refinement theorem here. Harmless changes to
the original source spelling are intentionally outside this singleton claim.

`WasmModule.decode` is structural admission, not a proof of full Core validation.
The separate scalar typing and source-pinned manual Core bitwise proofs retain
their own scopes. This direct-call theorem does not extend the independent Core
relations, prove a Core importer/transcription, or verify the Node/Deno runtime.
Engine agreement is regression evidence, not a universal engine-correctness
proof. General recursion, arbitrary source programs, memory, imports and ambient
host effects remain outside this increment. `TranslationVerified` stays false;
no production verified label, certificate authority or runtime verdict changes.
