# Source-linked unsigned conditional execution

`Oak.WasmConditionalSource` connects a small, explicit original-source grammar
to `LoweringRefinement.Expr` and complete decoded Wasm export execution for
**every pair of 32-bit inputs**. `Oak.WasmConditionalExecution` proves the
conditional body and its caller/local framing. This extends the fixture-identity
boundary of the direct-call proof with a source-meaning theorem for this slice.

## Canonical source grammar

The accepted shape is exactly:

```oak
choose: (x: u32, y: u32): u32 = (x < y) ? (x - y) | (y - x)
```

The final LF is required. Function and parameter names may change consistently.
All three names must be pairwise distinct and satisfy the existing
`BitwiseSource.identifier` policy, without changing that policy or the bitwise
source grammar. Each name is at most 64 bytes; source input is at most 1024 bytes.
Whitespace, punctuation, unsigned types, condition, operand order and both arms
are part of the grammar. Comments, extra declarations, CRLF and hidden suffixes
are outside this canonical slice, even when the production parser accepts them.

`Grammar.function` describes the complete rendered bytes independently of the
parser's candidate-field discovery. `parse_sound` proves successful recognition
belongs to that grammar; `parse_exact` proves equality of every original byte.
This is a soundness theorem, not a parser-completeness theorem for all names.

`environment` resolves the two distinct source parameter names to their input
values. `grammar_evaluation` proves source evaluation returns
`if a.toNat < b.toNat then a - b else b - a`, with `BitVec 32` subtraction.
The comparison is unsigned; the selected negative difference wraps modulo
2^32. This is not a mathematical absolute-value calculation.

`toExpr` maps the resolved parameter positions to the existing typed `u32`
variables and uses its comparison, subtraction and conditional constructors.
`typed_meaning` and `grammar_to_existing` prove agreement with the existing
`LoweringRefinement.evalX` for arbitrary inputs and arbitrary expression fuel.
This loop-free expression does not consume that fuel.

## Actual byte admission and all-input theorem

`accepts source claim bytes` independently checks both the original source
against its declaration claim and the entire decoded module against the expected
function table and named export. Export names are obtained from the checked
source declaration. The function has two i32 parameters, one i32 result and one
fresh i32 phi local. Its complete body compares with `i32.lt_u`, selects one
subtraction arm, stores the chosen value to local 2, and reads that phi local.

The Go gate compiles four original sources using the actual compiler. It passes
those unchanged source bytes and returned module bytes into generated Lean
certificates. No modeled emitter substitutes for these compiler artifacts. The
60-byte example above produces a 66-byte module, whose SHA-256 at introduction is
`19f42a6e52c83149508167e52ee27a18d42eab35095738ab315fd8fdbfef4a87`.
The gate checks the compiler's byte-admission digest, recompiles independently,
and requires deterministic bytes. Parameter-only renaming is also required to
leave the emitted module unchanged. Digest metadata is not proof authority.

`accepted_source_to_export` assumes only checker acceptance, arbitrary `a b :
BitVec 32`, arbitrary expression fuel and arbitrary additional runtime fuel. It
derives grammar membership, named source evaluation, existing typed expression
meaning, complete decoding and successful named-export invocation. Invocation at
`16 + extra` fuel returns exactly one selected result and local state
`#[a, b, result]`. Both branch paths are proved; execution success is a conclusion,
not a supplied premise. Concrete kernel-checked acceptance specializes this
universal theorem to each actual compiler artifact. Equivalent padded section
length encodings are accepted when the existing decoder returns the same module.

The separate call-composition theorem takes an arbitrary suspended caller,
arbitrary outer callers and an operand suffix. Its only caller-state premise is
that the top operands contain the two i32 arguments in Wasm stack order. Actual
call entry consumes precisely those arguments, initializes the phi local to
zero and creates a separate function label. Twelve existing machine ticks then
restore the caller's locals, labels, continuation and outer callers, prepending
only the selected result to the operand suffix. The theorem uses the existing
`WasmCalls.call` and `tick`; it does not define another instruction semantics.

## Regression and hostile controls

`TestWasmConditionalSourceLean` and `TestWasmConditionalSourceEngine` cover 110
source/module controls. There are also 19 independent source-parser checks and
12 central theorem audits, for 141 audited conclusions in total:

- Four independently compiled naming variants, including 64-byte names, and
  four equivalent padded modules.
- Source replay with a changed declaration, signed types, changed comparison,
  changed arm or operand binding, duplicate names, function/parameter shadowing,
  reserved names, unsupported identifier characters, oversized names or source,
  missing LF, CRLF, comments and extra declarations.
- Independent parser certificates for source mutations. Valid consistent
  renaming parses to its new declaration but cannot replay the old claim.
- Signed or inverted byte comparisons, reversed arm operands, phi-local writes
  that clobber a parameter, wrong phi reads, wrong block results, a missing else,
  out-of-bounds locals, local-width mismatch, an unused extra local, a trapping
  return route, parameter/result signature changes and a wrong export index.
- Bad magic, every strict module prefix and a trailing byte.

The Lean gate audits every certificate and the central generic theorems against
only `propext`, `Classical.choice` and `Quot.sound`. Missing audits, additional
axioms or missing required Lean fail the gate. Each certificate batch runs with
one Lean worker and an 896 MiB Lean memory limit. The mandatory formal workflow
retains the existing decoded-execution and independent-engine gates and adds
this suite to their regular expression.

The independent engine checks 209 boundary/random input pairs in both unsigned
and signed JavaScript argument presentations, or 418 invocations per valid
module. A BigInt oracle models unsigned comparison and wrapping subtraction.
Semantically changed valid mutations must exhibit a difference or a trap;
source-only mutations and the unused-local control retain the expected result.
Core-valid empty/type-only prefixes are distinguished from the narrower
project admission policy. These differential checks complement, rather than
replace, the all-input Lean theorem.

## Remaining trust boundaries

This is a deliberately canonical source slice and translation validation of
actual artifacts, not a proof of the production Go parser, compiler, IR passes,
register/local allocation or general source-language semantics. The independent
byte grammar and its positional translation to the existing typed expression
are modeled definitions, not an importer refinement of production compiler data.
No theorem says every compiler invocation accepts or emits this shape.

Execution uses the project's existing manually modeled decoded Wasm machine.
The proof does not establish correspondence to the complete independent Wasm
Core specification, verify the Core importer, or verify Node/Deno or a deployed
runtime. It does not cover loops, memory, other types or arbitrary conditionals.
No runtime `TranslationVerified` authority is added: the actual emission gate
requires that field to remain false. All existing byte, assembler, typing,
source-provenance and independent-engine boundaries remain in place.
