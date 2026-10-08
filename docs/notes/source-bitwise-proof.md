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
