# Original-source binding for the two-u32 bitwise proof slice

`Oak.BitwiseSource` adds an independent byte-level recognizer and source
semantics to the existing named Wasm-module checker. It does not authorize a
production `TranslationVerified` or `-verified` result.

## Language boundary

The owner of the language syntax remains `docs/spec/10-syntax.md`, especially
§3 (identifier-first callable declarations, colon result, expression body) and
§3b (same-width unsigned AND/OR/XOR). `docs/spec/83-modules.md` reserves internal
identifier spellings. This proof uses the following strictly narrower canonical
form, with exactly the spaces shown and one final LF byte:

```
name: (first: u32, second: u32): u32 = first OP second\n
```

`OP` is exactly `&`, `|`, or `^`. Each name starts with an ASCII letter and
continues with ASCII letters or digits. All three names differ. Keywords from
`token/token.go` and the listed built-in type names are excluded. The special `main` entry
name is also excluded. Underscores
are excluded, which also excludes discard, internal `__` names and native ABI
suffixes. Contextual words such as `kernel`, `forall`, and `exists` remain
identifiers in these positions. Names are unbounded in the source grammar;
the existing Wasm loader separately limits export names to 256 ASCII bytes.

There is no import, package context, implicit prelude, overload, alias, effect,
comment, BOM, CRLF, Unicode name, alternate whitespace, semicolon, parenthesized
body, trailing declaration, reversed reference, extra argument, or nested
expression in this profile. Even semantically equivalent source outside this
shape refuses. This is an isolated closed function's source semantics, not a
proof about full-project name resolution or contextual validity in an arbitrary
package. The prose specification identifies why this syntax and same-width
bitwise meaning are the intended Oak subset; it is not a formal mechanized
inclusion theorem for the complete Oak language.

## What is proved

- `candidate` discovers name and operator fields directly from the original
  byte list. `parse` additionally checks every original byte against a complete
  grammar expansion and checks identifier/uniqueness restrictions. No Go AST,
  optimizer AST, digest, or externally asserted parser-correctness premise is
  involved.
- The declarative `Grammar` relation is separate from field discovery.
  `parse_sound` proves every successful parse belongs to it. Soundness suffices
  for admission; completeness of the field-discovery algorithm is not claimed.
- `environment` and `evaluate` read each named parameter in declaration order.
  `grammar_evaluation` proves the expression produces the common `BitVec 32`
  AND/OR/XOR result for every pair of inputs. The function name and parameter
  identity are part of the checked claim, rather than only an operation tag.
- `accepted_source_to_module` quantifies over arbitrary original source bytes,
  claimed declaration, target/ABI and complete module bytes. Acceptance proves
  source meaning and successful named-module invocation for every input pair.
  Source recognition, export-name selection, module loading, function-byte
  decoding and mathematical evaluation are linked in the theorem.
- Source mutation tests flip every bit of every byte in the canonical source
  for all three operations. Explicit tests cover names, parameter order,
  keywords, type changes, body references, extra source, ABI/target and byte
  mismatch. Consistent renaming can form a new admitted program, but cannot
  replay an old identity claim.

The declaration grammar is a quantified family over arbitrary admitted
identifiers and three operators, not a whitelist of the concrete test fixtures.
The fixtures merely give executable regressions for the general theorem.

## Actual compiler correspondence and remaining trust boundary

The existing required Wasm Lean test lane compiles all three canonical sources
using the real compiler, serializes the exact original source bytes and final
module bytes, and generates kernel-checked acceptance and all-input theorems.
This closes source/byte identity for those actual emitted artifacts: changing
an artifact or substituting an AST no longer leaves only an unrelated
operation theorem. The test's mapping is not the proof of source semantics;
the independently checked grammar and named environment supply that proof.

The universal theorem is conditional on the independent checker accepting the
actual source and emitted bytes. It does not prove the Go compiler always
produces accepted bytes, that all Oak programs fall inside the profile, or
that the production Go parser/refactoring is universally correct. Running the
Go test/generator and retaining the correct artifacts remains operational
provenance; the generated Lean literals themselves are checked by the kernel.

The Wasm loader and executor are the repository's restricted Lean models.
Correspondence with the external WebAssembly Core specification, a real host
loader/engine, and its memory/runtime environment remains separate. Native
function/ELF loading, entry selection, ABI/memory assumptions and external ISA
refinement remain separate obligations, not consequences of this Wasm source
binding. Existing native equality certificates consume abstract declarations
and do not become source-authoritative merely because this module exists.

## Unified three-target claim matrix

`Oak.BitwiseSourceParity.accepted_all_input_success` composes the shared source
checker with all three admitted target profiles. There is one common input
pair and one full 32-bit mathematical result; no comparison of traps or OS exit
statuses is substituted for successful function return.

| Boundary | Wasm | ARM64 | RV64 |
| --- | --- | --- | --- |
| Source admission | Same canonical original-byte grammar and named-parameter evaluation | Same | Same |
| Original identity | Entire original byte list checked against claimed name, parameters and operation | Same source claim, plus complete native body bytes | Same source claim, plus complete native body bytes |
| Successful internal semantics | Full named module load and typed function invocation returns `.ok (eval op left right)` | Exact 8-byte logical-W operation plus RET returns successfully; observed W0 is the full u32 result | Exact 36-byte production wrapper returns successfully; observed low 32 bits of a0 are the full u32 result |
| Calling precondition | Two i32 locals, zero extra locals, validated restricted module | Initial W0/W1 low 32 bits equal the input pair; high halves unconstrained | LP64D sign-extension adapter; initial caller/frame state satisfies `frameSafe` |
| Memory precondition | Profile has no memory/import/start section | Profile has no memory access | SP at least 96 and aligned to 16; the complete 96-byte frame externally asserted mapped readable/writable; flat little-endian data memory and instruction/data separation |
| Actual production byte pin | Real `EmitWasm` final module from exactly the admitted source | Real `EmitNative(ELF)` result, named `oak_mix` symbol's entire 8-byte extent | Real `EmitNative(ELF)` result, named `oak_mix` symbol's entire 36-byte extent, LP64D flags, no unresolved relocation in extent |
| Name/container boundary | The Lean loader parses the complete module and selects the source name's export | Go ELF extraction is tested, not proved; native symbol/name/address lookup and subsequent loading are external | Same unproved ELF extraction/loading boundary |
| External semantics boundary | Refinement to WebAssembly Core and real loader/engine remains unproved | Refinement from restricted model to external ISA and concrete fetched state remains separate | Concrete fetched Sail/ISA state, decoder/return/memory/permissions refinement remains separate |
| Proof versus test | Admission-to-success is universal over accepted sources/modules and all input pairs; actual compiler/literal correspondence is tested | Universal accepted-body success under explicit register preconditions; compiler artifact correspondence is tested | Universal accepted-body success under explicit ABI/frame preconditions; compiler artifact correspondence is tested |

The RV64 frame premise is essential. The theorem does not claim ARM64/Wasm and
RV64 have identical requirements, stack behavior, memory effects, or total
machine states. It establishes the same source/result semantics once each
lane's stated preconditions are satisfied. Native entry selection, real
instruction fetch, and loader/ISA agreements cannot be inferred from body
parity. The imported native theorems separately record their register and
memory effects; the parity conclusion intentionally observes only the result.

`compiler/source_bitwise_parity_test.go` passes the **identical original source**
`mix: (a: u32, b: u32): u32 = a OP b` plus LF to all three production paths.
It does not append a `main`, change the signature to an arrow, or regenerate an
AST. For each operation it serializes the source, complete Wasm module and
complete extracted native bodies into Lean literals, checks combined admission
in the kernel, and instantiates the all-input theorem. It runs as a subtest of
the already required `OAK_REQUIRE_WASM_LEAN` execution lane; no new optional CI
job or weakened gate is introduced. ELF extraction is explicitly executable
evidence, not a kernel proof of container/name correspondence.

Axiom audits of `parse_sound`, `grammar_evaluation`,
`accepted_source_to_module`, and `accepted_all_input_success` report only
standard Lean logical axioms (`propext`, `Quot.sound`, and, where needed,
`Classical.choice`). These statements do not depend on `sorryAx`, native
oracle axioms, a circular compiler/source-correctness assumption, or an
external ISA-correctness axiom. The absence of such axioms does not establish
that the restricted models are the full external specifications.
