# Narrow Core-shaped bitwise projection

## Status

`Oak.WasmCoreBitwiseProjection` is a **hand-written relational projection**, with
Lean-kernel-checked proofs about that projection. It is **not an imported external
WebAssembly Core mechanization**, not a proof of the official binary grammar,
not an external `Module_ok` derivation, and not a full Core instantiation theorem.
No production certificate, verified label, or acceptance policy uses this module.

The existing complete-byte checker is reused unchanged. For every accepted source
and Wasm module, and **all** pairs of 32-bit inputs, the final theorem combines:

1. Grammar membership of the original restricted source bytes.
2. Success of the established typed source `LoweringRefinement.evalX`.
3. A projected one-function module and singleton allocation/export lookup.
4. A restricted `(i32,i32)->i32` body-typing derivation with initialized locals.
5. A Core-shaped small-step derivation through two local reads, a binary operator,
   then label and frame removal, returning the same 32-bit result.
6. Success of the existing complete-module byte executor.

This is a useful intermediate obligation, **not closure of the external Core
boundary**. It is a shared-result refinement for the fixed profile, not a general
step-by-step simulation for arbitrary Wasm instructions or modules.

## Authoritative source and pin

Official repository: <https://github.com/WebAssembly/spec>

Revision: [`970c4116e644e2bf7acb39aab8b733db14ccdf28`](https://github.com/WebAssembly/spec/commit/970c4116e644e2bf7acb39aab8b733db14ccdf28)
(2026-10-03). This is a development repository revision, not a claim of a dated W3C
Recommendation. Sources are its `specification/wasm-3.0` profile.

`provenance.json` records exact source URLs and SHA-256 values of the UTF-8 contents
retrieved from the GitHub connector. The manifest is audit evidence, not a
kernel-verified importer or a claim of source-to-Lean equivalence. Lean does not
read that JSON file.

| Local element | Pinned external source/rule |
| --- | --- |
| `Typed.localGet` | `2.3-validation.instructions.spectec`, `Instr_ok/local.get`, initialized `SET I32` local |
| `Typed.binary` | Same file, `Instr_ok/binop`, two i32 operands to one i32 |
| `Step.localGet` | `4.3-execution.instructions.spectec`, `Step_read/local.get`, `Step/read`, `Step/ctxt-instrs` |
| `Step.binary` | Same file, `Step_pure/binop-val`, `Step/pure`, `Step/ctxt-instrs` |
| `Step.labelContext`, `labelValues` | Same file, `Step/ctxt-label`, `Step_pure/label-vals` |
| `Step.frameContext`, `frameValues` | Same file, `Step/ctxt-frame`, `Step_pure/frame-vals` |
| `entered` | Post-state shape of `Step/call_ref-func`, with arity 1 and locals consisting of the two arguments |
| `instantiate`, `exported` | Only an empty-store singleton projection of `4.4-execution.modules.spectec` allocation/export rules |
| `numeric`, `NumericResult` | `3.1-numerics.scalar.spectec` dispatch to `iand`, `ior`, `ixor`; normative bit-string equations in `document/core/exec/numerics.rst`, `op-iand`, `op-ior`, `op-ixor` |
| Final `end` byte | `5.3-binary.instructions.spectec`, `Bexpr`; byte 0x0B is consumed by the expression grammar, **not executed** |

The upstream SpecTec numeric file **declares** these primitive bitwise functions
as builtins. Their mathematical definitions are in the normative document's
bit-string equations. `numeric_bits` proves the corresponding pointwise Boolean
law in Lean; `numeric_unique` proves its unique result. Translation of the
normative bit-string representation to this local representation is still manual.

The upstream label-values rule does not constrain the label's arity to the value
count; the frame-values rule does. The local rules preserve this distinction.
Typing of this exact body establishes one result. `Step` contains no rule that
turns a trap, bad local access, or malformed state into success. The all-input
result is an explicit successful reduction derivation, not merely equality of
faults. This alone does not prove that no trap is reachable in the full external
semantics; that requires the external bridge below.

## Exact remaining external obligations

Before describing this path as source-to-external-Core correctness, establish:

1. **Source-rule fidelity:** a checked importer/translation, or an explicit reviewed
   trusted transcription boundary, relating these inductive constructors and
   numeric meanings to the pinned external relations. A hash only pins content;
   it does not prove translation fidelity.
2. **Binary grammar:** show that *every* module accepted by `BitwiseModule.load`
   has an official `Bmodule` derivation yielding the intended abstract module.
   This includes magic/version, section order/exhaustion, counts, padded LEB128
   lengths/indices, function/type/export indices, ASCII-to-UTF-8 names, local
   declarations, opcodes and final expression delimiter. Existing decoding and
   all-byte exhaustion are useful inputs; they are not that external theorem.
3. **Validation:** derive the complete pinned `Module_ok`, including type section,
   function declaration/code matching, export uniqueness/index/type, and
   instruction-expression typing. `Typed` proves only this body's restricted
   initialized-i32 stack typing.
4. **Instantiation and invocation:** relate the projected singleton instance to
   Core allocation, recursive module/type closure and export addresses; discharge
   `$instantiate` and `$invoke` premises; derive the call-ref entry step and show
   the unused store components are unchanged. `entered_returns` starts **after**
   call-ref, so this missing step is explicit rather than assumed as an axiom.
5. **Host observation:** prove or state the interface that supplies/observes i32
   bit patterns. `signed_unsigned_bits` proves that signed and unsigned integer
   presentations convert back to the same 32 bits, including high-bit-set words;
   it does not certify a JavaScript embedding or runtime.

For this profile there are no imports, memory, tables, globals, start function,
additional functions/exports/locals, calls inside the body, or memory effects.
The allocation projection is limited to an empty store. General store extension,
linking, host calls, execution-resource limits and full language support are
outside it. Restricting the profile is not evidence that the remaining external
proof obligations have already been discharged.

## Route assessment

The official SpecTec sources are the closest source-of-truth connection. A checked
translation of the relevant DSL fragment into Lean would preserve one proof
kernel. Building/running the SpecTec interpreter and comparing fixtures would be
useful tests, but would not discharge a universally quantified semantics theorem.
No verified SpecTec-to-Lean importer is used or supplied here.

[WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq) is an independent Rocq
mechanization. Its README describes Wasm 2.0 plus subtyping/tail-call additions.
[WasmCert-Isabelle](https://github.com/WasmCert/WasmCert-Isabelle) is an Isabelle
mechanization. Proving this profile directly in either is a plausible stronger
external route, but needs its own pinned build, axiom review and a cross-model
source/byte bridge. A Rocq/Isabelle proof or extracted interpreter cannot simply be
claimed as a Lean-kernel proof. Neither toolchain is installed or trusted by this
change.

## Reproduce the focused proof and axiom audit

With the repository's Lean 4.33.1 environment:

```sh
cd spec/lean
lake build Oak.WasmCoreBitwiseProjection
lake env lean ../wasm-core/Audit.lean
```

The key final theorems use only standard Lean axioms `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`, custom semantics axiom,
`native_decide` axiom, or external solver oracle. The small body typing theorem
has no axioms. This audit concerns proof terms about the local definitions; it
cannot audit whether their manual transcription faithfully represents Core.
