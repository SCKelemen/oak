# Source-pinned restricted WebAssembly Core derivation

## Status and exact claim

`Oak.WasmCoreSource.source_to_core` derives the complete admitted narrow path
**inside a hand-transcribed, source-pinned Core formalization**:

original restricted source bytes → existing typed source meaning → independent
binary grammar derivation for the actual complete module → restricted Module_ok
→ fresh allocation/instantiation → named export lookup → external invocation →
non-null call-ref entry → local reads/bitwise operation → label/frame return.

All 32-bit input pairs and every module admitted by the existing checker are
covered, including its accepted padded LEB128 lengths/counts/indices. The theorem
also quantifies over any pre-existing store in the represented fragment. It is
not limited to a particular module fixture or an empty store.

**This is not a verified SpecTec importer or an independently mechanized proof
that this transcription/representation is equivalent to the official full Core
relations.** The original manual transcription boundary remains. No production
certificate, verified label, runtime verdict, or CI workflow uses this change.
Production Go parser/compiler correctness and runtime implementation correctness
are separate boundaries.

## Files and proofs

- `WasmCoreBitwiseProjection.lean`: i32 bit-string result relation, unique result,
  signed/unsigned bit preservation, body typing and relational instruction steps.
  Its earlier empty-store projection is retained, but is not used as a substitute
  for the stronger module/instantiation path below.
- `WasmCoreModule.lean`: explicit type/function/export/module AST fields;
  constructive type/function/export/module validity; indexed export allocation;
  arbitrary-store fresh function allocation; external invoke, call-ref and
  administrative activation/result relations.
- `WasmCoreBinary.lean`: independent natural-valued BuN, instruction, expression,
  UTF-8 ASCII name, section and module grammars; proof from the existing loader
  to those relations. The loader's six helper definitions were made public for
  these proofs; their implementations and behavior were not changed.
- `WasmCoreSource.lean`: composes all of these with original source grammar and
  the existing typed `LoweringRefinement.evalX` result.
- `Audit.lean`: prints axioms of the central proof terms.

The grammar relations do not invoke the loader or admission predicate.
`loaded_binary` destructs the successful loader computation and reconstructs
all consumed byte chunks, length/count encodings and sections. Its proof is
universal over raw bytes. `admitted_binary` connects the checked operator to that
structural derivation. The existing decoder is reused rather than replaced.

## Authoritative source and pin

Official repository: <https://github.com/WebAssembly/spec>

Revision: [`970c4116e644e2bf7acb39aab8b733db14ccdf28`](https://github.com/WebAssembly/spec/commit/970c4116e644e2bf7acb39aab8b733db14ccdf28)
(2026-10-03), profile `specification/wasm-3.0`. This is a pinned development
revision, not a claim of a particular dated W3C Recommendation.

`provenance.json` contains exact URLs and SHA-256 hashes of UTF-8 source contents
retrieved using the GitHub connector. It is audit evidence, not an importer or a
kernel dependency. Lean does not consume that manifest.

| Local relation | Pinned rule/source |
| --- | --- |
| `Unsigned`, `leb_to_unsigned` | `5.1-binary.values.spectec`, `BuN`: unsigned naturals, remaining width, continuation byte minus 128 |
| `UTF8Name`, `ascii_name`, `name_representation_injective` | Same file, `$utf8`, `Bname`; Unicode scalar/byte representation is injective on admitted ASCII names |
| `Section` | `5.4-binary.modules.spectec`, `Bsection_`; declared size equals actual payload length |
| Type/function/export/code payloads | Same file, `Btypesec`, `Bfuncsec`, `Bexportsec`, `Bcode`, `Bcodesec`, and `5.2-binary.types.spectec` |
| `Instruction`, `Expression` | `5.3-binary.instructions.spectec`, local.get, i32.and/or/xor, `Bexpr` |
| `BinaryModule` | `5.4-binary.modules.spectec`, `Bmodule`, with other sections absent and function/code vectors each singleton |
| `I32TypesOk`, `FuncTypeOk`, `ClosedTypeOk`, `TypesOk` | `2.1-validation.types.spectec`: numeric/result/composite/subtype/recursive type rules; `2.4-validation.modules.spectec`: `Type_ok`, `Types_ok` |
| `Typed`, `FunctionOk` | `2.3-validation.instructions.spectec`: local.get/binop/sequence/expression rules; `2.4-validation.modules.spectec`: `Func_ok` |
| `ExportOk`, `ModuleOk` | `2.4-validation.modules.spectec`: `Externidx_ok/func`, `Export_ok`, `Module_ok` |
| `ExportAllocated`, `Allocation` | `4.4-execution.modules.spectec`: export-index lookup, allocfunc, allocfuncs, allocmodule |
| `Instantiation`, `instantiate` | Same file, `$instantiate`; empty initialization vectors and absent start yield no initialization instructions |
| `Invoke` | Same file, `$invoke`; fresh address lookup and the function's parameter arity/types |
| `CallStep.callRef` | `4.3-execution.instructions.spectec`, `Step/call_ref-func`; concrete non-null address, closed type match and initialized parameter/local frame |
| `Step.localGet`, `Step.binary` | Same file, local.get, binop-val, read/pure/context rules |
| Label and activation reductions | Same file, ctxt-label/label-vals, ctxt-frame/frame-vals |
| `NumericResult`, `numeric_bits`, `numeric_unique` | `3.1-numerics.scalar.spectec` builtin dispatch, plus `document/core/exec/numerics.rst` normative `op-iand`, `op-ior`, `op-ixor` bit-string equations |

## What is actually discharged

### Binary decoding

The derivation retains magic/version, exact section order, section and body sizes,
vector counts, function/type/export indices, byte length of the UTF-8 name, zero
local declarations, individual instruction productions and complete exhaustion.
`leb_to_unsigned` proves the earlier signed-Int-shaped LEB relation agrees with
the pinned unsigned-natural rules on this path; modulo-128 limbs are proved to
match byte-minus-128 limbs. Legal padded encodings are preserved.

`end` (0x0B) belongs to the expression grammar and contributes no instruction to
the AST. Function return instead reduces an administrative label and activation.
There is no reinterpretation of unsupported control flow as successful execution.

### Validation

The AST independently carries type definitions, function type indices, local
declarations, code, export indices/names and non-function section fields.
Module validity is an inductive derivation over these fields, not an alias of
admission or an equality test against the intended module. Function context
lookups and body typing, export lookups, export-name uniqueness, and omitted
section/start premises are checked. `Each₂` requires both cardinalities to agree;
`module_cardinality`, `function_index_valid` and `export_index_valid` expose those
consequences. Invalid type/export index examples cannot derive the respective
validity judgments.

### Instantiation and invocation

A fresh function is appended at the old function-store length. Its instance
contains the real module address vector and code/type relationship. Export
allocation uses indexed lookup through that vector, not source-index/address
conflation. The old function entries and abstract other-store component remain
unchanged. `fresh_before`, `fresh_function`, `allocated_code_type`,
`preserves_function`, `preserves_other`, and `export_resolves` state those facts.

External invocation looks up the allocated function and checks two i32 arguments.
The call-ref rule requires a concrete non-null function reference and matching
closed type, then builds an activation containing the correct module instance,
parameter locals, result arity and label. Empty extra-local declarations yield
no added local values. The final frame-values rule checks the one-result arity
and removes the activation, producing a result vector rather than a surviving
callee frame. Both invocation and return are constructed for all inputs.

### Numeric primitives

The upstream SpecTec numeric file only **declares** iand/ior/ixor as builtins.
Their normative mathematical definitions use bit-string Boolean operations in
`document/core/exec/numerics.rst`. `NumericResult` independently states the
pointwise Boolean law; the binary reduction rule requires that relation rather
than simply returning the Oak evaluator's chosen result. `numeric_bits` proves
Lean BitVec operations satisfy it; `numeric_unique` proves uniqueness.
`signed_unsigned_bits` proves signed and unsigned host integer presentations
convert back to identical 32-bit words, including words with bit 31 set.

## Trust ledger and remaining external boundary

The following representation choices are **manual specializations of the pinned
rules**, not independently verified translations:

1. `ClosedType.recFinalFunc` compresses a final parentless function subtype in a
   singleton recursive group (and its index-zero definition projection). All
   value types are i32, represented by units, so no type references occur and
   rolling/substitution is structurally identity. The proofs derive the local
   closed-type judgments; they do not verify the full Core recursive-type DSL.
2. Names use their admitted ASCII bytes as a compact representation of Unicode
   scalar sequences. UTF-8 derivation and representation injectivity are proved
   for this subset, not arbitrary UTF-8 strings.
3. The represented store contains function instances plus an opaque list of
   natural tokens for other components. Arbitrary stores **in this representation**
   are covered. An embedding from the full Core store, with arbitrary host
   functions, memories, tags and other values, remains a representation-review
   obligation. Preserving opaque state is not proof of that embedding.
4. The activation relation represents the single entered frame and its module
   explicitly. The body fragment cannot call, branch, access memory or mutate
   locals/store. Unused outer-state components and type-context components are
   omitted. The successful reduction is not a general determinism/type-safety
   theorem for every malformed or unsupported configuration.
5. The DSL rules, bit-string conventions and these simplifications were manually
   read and transcribed. A checked importer or a proof of an embedding into an
   independently mechanized complete Core semantics is still needed to remove
   this trust boundary. Hashes and Lean axiom audits do not remove it.
6. Production Go implementation refinement, runtime/host embedding correctness,
   resource exhaustion and unrepresented Wasm features remain outside this work.

The prior missing **local** binary/Module_ok/instantiation/invocation derivations
are now provided for this profile; the **external transcription/embedding**
boundary is explicitly not declared closed. No extra axiom assumes that a module
is valid, that instantiation succeeds, or that its intended invocation returns.

## Reproduce the focused proof and axiom audit

With the repository's Lean 4.33.1 environment:

```sh
cd spec/lean
lake build Oak.WasmCoreSource
lake env lean ../wasm-core/Audit.lean
```

Only standard Lean axioms `propext`, `Classical.choice`, `Quot.sound` occur in the
central theorem closure; there is no `sorryAx`, custom semantics axiom, native
computation axiom or external solver oracle. Audit results concern the actual
local definitions, not correctness of their source transcription.

## Longer-term route

A verified translation of the relevant official SpecTec fragment into Lean is
the strongest single-kernel route. Running its interpreter or comparing fixtures
would be tests, not a universal proof. Alternatively,
[WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq) or
[WasmCert-Isabelle](https://github.com/WasmCert/WasmCert-Isabelle) supplies an
independent mechanization, but requires a pinned build, axiom review, and
cross-model source/byte bridge. Neither is installed or trusted by this change.
