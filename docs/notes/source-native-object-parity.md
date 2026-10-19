# Restricted source to complete-artifact parity

`Oak.BitwiseSourceObjectParity` composes the independently checked original-source grammar, the existing typed expression semantics, the complete Wasm module checker, and the strict native ET_REL object checker. It is layered on `Oak.NativeBitwiseObject` and included in the aggregate `Oak.lean` import list. A mandatory formal-workflow step checks its exact theorem inventory, fixtures, and axiom reports. It does not change compiler APIs or production verdicts.

## Exact guarantee

`check source wasm arm rv` receives the full original source bytes, the complete Wasm module bytes, and both complete native object byte lists. It receives no declaration, symbol name, operation, body, or source-to-term relation from the caller. It parses a declaration from the original bytes and uses that declaration's name and operation for all three artifact checks.

- `check_sound` recovers the exact parsed declaration and all three artifact admission facts.
- `accepted_source_object_binding` proves exact source reconstruction and declarative grammar membership, plus both actual decoded native symbol names, symbol uniqueness, full checked bodies, section-relative entries, file extents, and complete canonical container profiles.
- `accepted_all_input_success` quantifies over every u32 input pair, every typed-expression fuel value, every permitted ARM caller state, both aligned non-wrapping modeled code bases, and all RV caller/memory/mapping states satisfying the explicit frame premise. It proves identical full-u32 results in the named source evaluator, established typed expression interpreter, complete Wasm module interpreter, and both modeled named native entry invocations.
- `accepts_iff` links Boolean admission to the declaration returned by `check`. The declaration in the success theorem is checked output, not a trusted caller label.
- `refuses_outside_grammar` proves that a source outside the declarative grammar is rejected regardless of all supplied artifacts. `refuses_unsupported` covers computational parse failure; `refuses_source_replay` prevents replay of a declaration against changed original bytes.

The original-source grammar is intentionally narrow: one canonical ASCII identifier-first declaration with two distinct u32 parameters, one parameter-ordered AND/OR/XOR expression, and the required spacing/final LF. Unsupported types, references, comments, additional declarations, and other grammar extensions are not accepted. The theorem does not assume that the production parser produced an equivalent AST.

## Explicit boundaries

The native container profile is the strict one-function/no-data/no-relocation ELF64 ET_REL shape; arbitrary ELF objects, linking, executable files, and `e_entry` dispatch are not covered. The function entry comes from the checked symbol and section model. The theorem's native observations include modeled loading of the exact checked full body at that named entry.

ARM retains the existing no-fault scalar instruction projection, low-32-bit argument convention, and unrestricted high input halves. RV64 retains the actual 36-byte wrapper, LP64D entry adapter, and the external aligned/readable/writable/noninterfering 96-byte stack-frame premise. Code-base alignment and no-wrap bounds are explicit arguments. The physical memory mapping, instruction fetch, external ISA/model refinement, code/data coherence, faults, OS loader/linker, and validity/execution of the physical return target are not proved. Underlying models prove return/state facts; this composed theorem's observation is the full u32 result.

Wasm uses the existing bounded module/interpreter model rather than an external engine or Core-spec refinement. This establishes parity for independently admitted concrete source/artifact tuples, not arbitrary compiler or whole-language correctness. It enables no production verification authority.

## Validation

With Lean 4.33.1, from `spec/lean`:

    LEAN_NUM_THREADS=1 lake build Oak.BitwiseSourceObjectParityAudit

This targets only the required dependency closure and the new proof, fixtures, and axiom audit. The fixture module contains four positive checks: AND, OR, XOR, and a consistently renamed `Mix9` declaration with renamed parameters. It also has fifteen refusal checks covering source operation/name mismatches, each artifact's operation/name mismatches, swapped architectures, trailing bytes in each artifact, unsupported types/references, a second declaration, and a comment.

Eight native source/object fixture pairs are copied byte-for-byte from `NativeBitwiseObjectFixtures.lean` generated from the current emitter. Their source fixture file SHA-256 is `8e7ce33f5da4ee92aadf9b408ca0342959b56f59050f60c6c51e8be07eeed9f2`. The renamed positive test uses an explicitly hand-constructed bounded Wasm module, not a claim about a new compiler run. All finite checks use `decide +kernel`.

`BitwiseSourceObjectParityAudit.lean` prints axiom dependencies for all seven exported composition theorems and all nineteen fixture theorems. Allowed foundational dependencies are `propext`, `Quot.sound`, and `Classical.choice`; the new files introduce no axioms, `sorry`, or native evaluator oracle. Existing dependency linter warnings are unrelated and unchanged. No aggregate repository build or production test suite is claimed for this separate composition-only change.

The formal workflow additionally runs `python3 tools/source_object_parity.py`. This gate pins all twenty-six theorem names, rejects missing/duplicate/changed source inventories or audit queries, kernel-checks the fixture import closure, and replays the audit through the native-object gate's existing strict multiline report parser. Missing, extra, malformed, duplicated, or unapproved-axiom reports fail the step. The gate's regression controls run first. This is a CI evidence check, not a production artifact-verification API.
