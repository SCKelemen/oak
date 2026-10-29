# Stateful copy: source-bound raw OptIR projection and refinement

## Delivered boundary

`Compilation.StatefulCopyOptIR()` runs the ordinary package `Check` and the
existing checked OptIR lowerer/`Project` on exactly `copy_checked` and resolved
`bytes__copy_uinto`. It returns an owned **raw**, unoptimized artifact. No native,
Wasm, optimization, or physical-ABI support is enabled by this API.

The frozen caller still saves `n = len(src)` before one non-inlined direct call,
receives the real `Result[u32, bytes.CopyError]`, and observes its payload against
that saved value. Lengths and bytes are runtime inputs, not specialized fixtures.
The `[]u8`/`[*]u8` descriptors and Result remain logical values, not integer or
sentinel carriers. The actual checked generic instantiation supplies the type
inventory and ordered constructor payloads.

**Raw-profile admission is not a copy-refinement verdict.** For example, changing
increment one to two can remain well typed. The separate fresh kernel translation-validator acceptance must
reject that graph; the tests deliberately demonstrate this distinction.

## Authority and custody

* `optir.StatefulProgram` has private snapshots and defensive getters. Structural
  `Project` is rerun and the CFG compared with `ExactCFGEqual`, not only a hash.
* The closed profile allows eight logical types and only the operations needed
  by this closure. Unknown opcode/type/attribute/effect, wrong arity, constructor,
  call target or formal substitution refuses.
* Dedicated byte-access records bind source, formal descriptor, structured SSA
  descriptor/index/value IDs, width one, `u8`, partial access kind and explicit
  bounds/mapping/initialization-or-trap policy. Original checked extent proof
  records are retained, but do not establish ownership or eliminate checks.
* Call effects are instantiated relative to the actual `(dst, src)` operands:
  destination may-write, source read, plus call and trap effects. Nothing promotes
  partial byte writes to whole-region replacement, must-write, or NoModRef.
* Existing scalar global memory authority is unchanged. This scoped raw profile
  rejects package value initialization, arbitrary calls, shadowed builtin `len`,
  shadowing Result payload bindings, and external syntax rewrites.
* Exact parsed Oak source-file bytes and semantic package/file occurrences are
  retained for the caller, stdlib bytes package and actual `std#stdlib.oak`
  prelude. Export roundtrip comparison covers every structured/CFG, authority
  and source field in this artifact. Original `oak.mod` bytes are not retained;
  this is not complete module-manifest attestation. The equipped fixture fixes
  its module declaration, while package resolution remains a tested/trusted
  boundary. Binding original module bytes is a separate narrow custody improvement.

`ExportLean` emits every field of the actual CFG. The required Go test regenerates
it from the checked fixture on every run. The proof gate independently checks
JSON-to-Lean reification and substitutes that fresh generated module in an
isolated trust-zero Lean build. It never accepts the committed development
snapshot merely because an old proof still compiles. Every equipped proof builds
the ordinary fixture under a deliberately long (at least 180-byte) source path
and checks that its complete identity is retained. Different absolute package
paths remain different exact source identities; no undocumented source rebasing
is performed to force portable hashes.

## Kernel claim

`Oak.OptIRExecution` faithfully records the existing CFG syntax and interprets
ordinary operations, edges, parameter bindings and separate call frames over
shared `StatefulCopy.Memory`. There is no copy opcode and no interpreter shortcut
to `liftedCopy`. Unknown/bad operations and inactive payloads fault; fuel exhaustion
is a distinct outcome, never `DestinationTooSmall`.

`Oak.OptIRStatefulCopy` proves the actual freshly generated callee's loop simulates
existing `Oak.Stdlib.Bytes.copy_into.loop1`, with generic single-byte writes joined
to existing `writeWindow`. The caller theorem executes the actual call, restores
its saved environment, returns `callerObservation`, and establishes
`StatefulCopy.ObservesCopy` for arbitrary valid `Invocation` windows/bytes.
`checkProjection` conjoins **entire CFG record** equality against that fresh
snapshot with explicit instruction/control/liveness schema equations. The same
validation module proves the fresh graph is accepted, and its equality soundness
transfers the full refinement theorem to every accepted candidate. This
is deliberately an exact snapshot translation validator, not a general verified
frontend or optimizer.

Same-owner disjoint windows are supported without strengthening `Invocation` to
different owner IDs. The invariant preserves source-window reads, not the
source owner's entire original backing. The inhabited control changes a byte
elsewhere in that common backing and checks unchanged source, suffix and unmapped
external addresses.

Exact IR costs count each operation and terminator, including the callee:

| Case | Callee | Caller |
|---|---:|---:|
| source fits (`s` bytes) | `11 + 7*s` | `19 + 7*s` |
| destination short | `8` | `16` |
| source empty | `11` | `19` |

The theorem also covers all sufficiently larger IR budgets. These are not target
instruction counts. Logical Result encode/decode is exact; physical register,
stack, endian-byte or Wasm aggregate transport remains open.

## Explicit trust boundaries and exclusions

The kernel proves refinement of the freshly exported raw CFG. Ordinary parsing,
resolution, typechecking, borrowing, Go profile/authority checking, structured
projection and Go/JSON/Lean serialization correspondence remain **tested trust
boundaries**, not hidden axioms or unconditional source-correctness theorems.
The source inventory establishes custody, not frontend semantic soundness.

No optimization preservation, machine selection, ABI, native artifact admission,
Wasm memory profile, target fuel, external ISA/Core correspondence, allocator,
general ADT framework, arbitrary module closure, or whole-compiler correctness is
claimed. Existing optimized OptIR/native selection and scalar Wasm refuse this
profile exactly as before.

## Required gate and regressions

`stateful-copy-optir` in `.github/scripts/required_backend_tests.py` requires the
fresh proof, exact child inventory, no skips, raw projection/export refusal
controls, mutations of the actual produced graph, old target refusals, and actual
CFG execution. The corpus covers the 114/174 prior corpus cases with valid
subwindow inputs, all 21 frozen offset cases, and 42 same-owner-shaped disjoint
cases. The remaining prior cases test invalid `copy_at` offsets, not valid
invocations of this whole-view copy root. Finite regressions support but do not
replace symbolic kernel refinement.

The kernel gate also typechecks changed actual generated graphs (increment,
guards, load/store ordering, loop backedge, count, call target, saved caller value
and nested error), then requires the same named `checkProjection` acceptance
theorem to fail with a decidable false verdict. Resource/import failures and
timeouts never count as rejection. These are bounded translation-validator
mutation controls, not nine replays of the entire universal refinement proof.
The saved-value control rejects a structural liveness change; it does not assert
that replacement necessarily changes every valid observation. The fresh positive
full arbitrary-input refinement remains mandatory. Existing
stateful representation, scalar memory/call-summary and backend gates are retained.
