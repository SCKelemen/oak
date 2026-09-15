# The optimization system (2026-09-15)

The goal set on 2026-09-15: the native backend at least as fast as C,
Rust, and Zig on the programs Oak is for, and faster where Oak knows more
than they do. This note is the design: what the compiler does today, what
it knows that a C compiler cannot, the gaps as measured, and the program
of increments with the gate each passes through. The normative part is
`docs/spec/90-backend.md` §16; the checklist items are
`docs/checklists/performance.md` §9.

## The doctrine, as the constitution already states it

`05-ergonomics-and-cost.md` "The mechanical backend" divides the work in
two. What a program means and roughly costs — allocation, dispatch,
numeric behavior, borrow and effect order, asymptotics — is guaranteed in
the source, and no backend transform may change it; a shape the source
did not write (autovectorization, reassociation) is not something a
program may depend on. Register allocation, instruction scheduling, and
instruction selection are the mechanical backend's, and "the whole of
what Oak asks of it". A case where C, Rust, or Zig is faster because it
expresses something Oak cannot is an expressiveness gap, filed as one.

Two consequences shape everything below.

1. **Optimization is either a proof-licensed removal or the mechanical
   layer.** The compiler removes a check, a copy, a guard, or a reload
   only when a fact it has proved licenses it (`90-backend.md` §8: a
   proved index may lose its check; an unproved one keeps its trap). It
   never speculates. Everything else — which register, which
   instruction, which order — is the mechanical layer, and is free
   because it changes nothing visible.
2. **The verifier is the gate, not the optimizer's care.** Every natively
   lowered body is checked at its seams (`asm.Check`) and executed
   symbolically against its Oak body (`asm.Verify`, `94-assembler.md`
   §9): proven equal, witnessed, trusted, or refused. An optimization
   that produces a body the verifier refuses falls back to the plain
   lowering for that function — the elided-guard fallback today
   (`compiler/native_bodies.go`). So the mechanical layer may be as
   aggressive as it likes: it is translation-validated per body, and an
   unsound rewrite is a refusal, never a wrong program. This is the
   advantage no C compiler has, and it is why the program below can
   move fast.

## What exists (survey of 2026-09-15)

**The C backend** emits C and hands it to the system compiler with
`-std=c99 -ffp-contract=off` and the one `-O` level `-opt` selects
(default 1; `cli.go`). Oak's own work before emission: proof-driven
bounds-check elimination from the extents typechecker
(`typechecker/extents.go`, `IndexProven`, consumed at every index site
of `codegen/`), source-level proof-preserving inlining of small private
helpers so caller facts prove callee accesses (`compiler/inline.go`),
forced-inline emission of the same shape and the hot codec helpers,
tail-recursion to loops and mutual tail groups to trampolines, constant
globals folded to `static const` so `/` and `%` become shifts, byte-pack
recognition, protocol tables. No expression folding, CSE, LICM, strength
reduction, or dead-code elimination of Oak's own was present in the initial
survey. The first target-independent expression increment landed on
2026-09-15: after type-driven monomorphization,
`source.canonical.bool.v1` removes redundant built-in Boolean identities for
every backend; `source.canonical.integer.v1` removes fixed-width `+ 0`, `- 0`,
`* 1`, `/ 1`, `| 0`, `^ 0`, and shifts by zero when the retained operand has
the exact checked result type. The changed program is checked again. Both
deliberately keep every non-literal operand; widening rewrites, CSE, and
dead-path removal wait for validated OptIR transformation and emission. Literal
negation also stays out of source rewriting so canonicalization never mutates a
source token that keys checked facts. The independent validation clone receives only
the concrete generic ADT declarations recorded by the specializing checker;
they are rebuilt through checked type substitution and never enter emission. `-opt
0` against `-opt 2` still measures how much generic scalar work the C compiler
has left to do.

The first target-neutral middle-end substrate now lives in `optir/`. It keeps
structured conditionals and pre-test loops with explicit loop-carried SSA
values, operation effects, attributes, and proof facts, while also projecting
deterministically to a typed block-argument CFG. `Compilation.OptIR()` projects
the checked, concrete scalar subset: fixed-width integers, Bool, unit, local
assignments, structured branches and short-circuiting, exhaustive Bool matches,
pre-test loops with explicit carried locals, value-preserving integer widening,
and effect-marked ordinary calls. Unsupported memory, method, kernel, protocol,
and richer algebraic forms produce per-function refusals rather than partial IR.
The independent verifier rejects undefined or non-dominating values, invalid
same-block order, unreachable blocks, malformed edges and terminators, non-Bool
conditions, and wrong returns.

The first analysis-only SCCP validates operation arity, types, attributes, and
cast legality, then computes exact constants and executable CFG edges with Oak's
8/16/32/64/128-bit wrapping semantics, signed division edge behavior, and
checked shift/division traps. Results are deterministic evidence and do not
rewrite the CFG. No backend consumes this IR yet; equivalence validation remains
mandatory before SCCP, GVN, or DCE can affect emitted code.

The first target-independent cleanup candidate now runs beside that evidence.
Dominance-scoped GVN assigns deterministic numbers to SSA values and shares
congruent operations only from a closed vocabulary of total pure scalar
operations. Plain copies carry their operand's number; wrapping integer
add/multiply/bitwise operations and equality use commutative operand order;
`a > b`/`a >= b` share the keys for `b < a`/`b <= a`. Result types and ordered
attributes remain part of identity, and unknown attributes disable algebraic
normalization. Sibling computations, trapping arithmetic, calls, memory,
synchronization, unknown operations, and any operation carrying an effect stay
in place. Proof facts move to the dominating definition only when all of their
values are valid there. Fixed-point DCE then removes unused chains and copies
from the same closed vocabulary, treating terminators, other operations' facts,
and function facts as roots. A definition's own fact leaves with the
definition. Both transforms clone their input and independently verify input
and output. `Compilation.OptIR()` exposes the simplified CFG and a deterministic
report, but emission still consumes neither.

The generic control-flow analysis now gives that CFG a reusable semantic loop
model. It reports reverse postorder, immediate dominators, back edges, natural
loop blocks/latches/exits, canonical preheaders, and nesting. For each header
parameter it follows only all-path-preserving block arguments and copies, then
accepts an affine recurrence only when every latch supplies the same
fixed-width `current + constant` or `current - constant` update. A unique loop
exit comparison is normalized to `induction relation bound`, independent of
operand order and which branch continues. Constant bounds produce an exact
trip count only when mathematical monotonicity and the final update prove that
no Oak fixed-width wrap occurs; otherwise the recurrence remains useful but the
count is absent. `Compilation.OptIR()` exposes these facts on the original CFG.
They authorize no emission; each consumer must still establish its own legality.

The first consumer is an analysis-only loop-invariant code-motion candidate.
It moves an operation to a canonical preheader only when every operand is
already available there and the operation is in the same closed total-pure
vocabulary as GVN/DCE. Division, remainder, shifts, calls, memory, effects,
unknown operations, and loops without a canonical preheader remain unchanged.
Relational or path-derived facts pin an operation; the one exception is the
result-local `checked.type` fact, which merely restates the typed SSA
definition. Nested loops are considered outermost first, allowing a value
invariant across both loops to move directly to the outer preheader. Input and
output are independently verified, and `Compilation.OptIR()` exposes the
post-GVN/DCE LICM candidate and a deterministic movement report. Emission still
consumes neither.

The compiler deliberately uses a hybrid pipeline/artifact architecture: source
stages and private local cleanup remain linear, while reusable, branching,
independently verifiable, proof-gating, or expensive results receive exact
artifact identities. The generic OptIR chain does. Typed artifact references
and root/unary/binary/ternary builders derive its keys and extract payloads, so
pass code no longer owns dependency indexes and type assertions. Exact-version
immutable nodes represent CFG v0,
SCCP, loop structure and recurrences, GVN/DCE, CFG v1, preservation evidence,
and LICM. Analyses declare the topology, SSA, operation, effect, type, fact,
and layout aspects they read. GVN/DCE's checked certificate proves
`CFGTopology` unchanged, so v1 reuses v0 dominance/natural-loop structure but
recomputes induction facts from the changed SSA. Certificates carry exact
artifact/content identities and per-aspect digests; they prove reuse
eligibility only, never semantic equivalence or emission permission. The
executor now supports deterministic ready waves with a fixed worker bound;
OptIR uses three workers for SCCP, loop-structure analysis, and GVN/DCE
fan-out. A failed wave publishes nothing, and traces/errors are independent of
worker completion order. Each native proposal has a canonical checked-input
recipe and materializes into typed candidate, admission, metrics, cost,
verdict, and selection nodes. Validation targets stay sequential to preserve
the proof budget and early stop; identity remains the explicit ungated
fallback. `optimizer-artifact-dag-2026-09.md` gives the full design and the
remaining persistent-cache work.

**The native backend** (`nativegen/`, AArch64 7,300 lines, RV64 4,000)
lowers a checked function directly to instructions with no IR. Scalar
locals take homes by a liveness pre-pass: a caller-saved register when
the variable never crosses a call, a callee-saved register x19–x28
(saved and restored once in the prologue and epilogue) when it does, a
caller-saved home spilled around calls past those ten, a frame slot
last; expressions run on an operand stack x9–x15, and a two-pass scheme
hands the scratch registers the expressions did not need to variables;
a register or slot is released after its last use. Vector locals of a
function that calls live in sixteen-byte slots, since AAPCS64 preserves
only the low halves of v8–v15. No scheduling, no peephole, no unrolling,
no vectorization, and no constant folding of the arithmetic the lowering
emits: a division by a constant was a zero-tested `udiv`. One proof fact is consumed: `IndexProven`
elides an element guard on AArch64 when the seam checker can read the
proof off a dominating compare; a refusal re-lowers with every guard.

**What the machine-code checks prove**: signature identity and AAPCS64
binding, width discipline, no uninitialized read, flags dominance,
frame-bounded memory, guard facts as a dataflow fixpoint, and equality
of the body to its Oak source at the bit level through canonical linear
forms and, past those, BDD and clause blasting; data-dependent loops
through loop events and affine coupling invariants; span stores as
observable effects; span borrows and derived spans as non-aliasing
facts.

**Measured** (`benchmarks/native/README.md`, `BENCHMARKS.md`): the C
backend runs the kernels at 0.84–1.10× of Rust and the JSON case at
1.1–1.4× of simdjson. The native backend against the C backend, Apple
M4 Max: `sum` 3.40×, `dot` 3.24× behind (a correct scalar loop against a
vectorized one); `search` 1.76×, `page_probe` 1.93× — read from the
lowered bodies on 2026-09-15, not frame traffic as the README had it
(the kernels make no calls and hold every local in a register) but
arithmetic: a `/ u32(2)` lowered as `movz; cbz; udiv` on the
mid-to-load critical path, a `* u32(512)` as `movz; mul`, a Bool
negation materialized before its branch; `crc32c` 5.7× (fifty-six
guarded byte loads assembled into seven words the C compiler reads with
seven loads); the UTF-8 validator 5× (calls spilling nine vector
locals); `sha256` 1.00×, `dispatch` 0.83×. Guard elision alone, measured
on the UTF-8 kernel, did not move the time: the predictor had absorbed
the branches; the time is in calls and spills.

## What Oak knows that the C compiler does not

The asymmetry the goal rests on. Each row is a fact the front end
already establishes, the transform it licenses, who consumes it today,
and the gate.

| Fact (where it is proved) | Licenses | Consumed today | Gate |
| --- | --- | --- | --- |
| An index is under its extent (`typechecker/extents.go`, `Oak.ExtentsRefinement`) | no bounds check; no guard | C backend at every site; native AArch64 through the seam checker | the checker reads the proof or refuses |
| Two live spans never overlap; a span and a view of one owner never coexist (`50-borrowing.md`, the borrow checker) | loads and stores reorder across them; loop-carried independence; `restrict` in C | nothing — the C compiler assumes aliasing; the native lane does not reorder | the verifier's span-store log (`asm/effects.go`) |
| A span is aligned (`[* align N]T`, `Oak.AlignmentFact`) | aligned vector loads, no peeling | nothing (kept representation-free by test) | the verifier's address model |
| A refinement holds of a value (`typechecker/refinements.go`) | narrower arithmetic, no overflow trap, range facts for selection | `oak prove` and the extents decider | the verifier's range facts (`asm/range.go`) |
| An operator law is declared (`OperatorLaws`, `HasOperatorLaw`) | reassociation, reduction reordering, fusion — the only permission to reorder (`performance.md` §9) | nothing | the verifier, with the law as an axiom of the equality |
| A function is pure / its effect row (`60-effects-allocation.md`) | hoisting, CSE, recomputation instead of materialization | nothing | the verifier's canonical forms already equate pure recomputation |
| A callee's extent proposition (`50-borrowing.md` `where len = N`) | constant-offset accesses in the callee need no guard | specified, not implemented | the checker, given the fact at the seam |
| A protocol's typestate (`112-protocols.md` §5a) | dead transitions dropped, table dispatch | protocol tables in C | the machine's own laws |

The C compiler recovers a fraction of the first row by its own analysis
and none of the others; Rust's borrow rules give LLVM `noalias`, which is
the second row alone. That is the whole of the information advantage, and
it is why "at least as fast" is the floor and not the ceiling.

## The layers (2026-09-15)

The system is three layers, each checked against its input
(`90-backend.md` §16). Layer A rewrites the checked body once for every
lane, each rewrite decided per site by the bit-level decider or backed
by a Lean law, and refused otherwise (`94-assembler.md` §9.ag;
`nativegen/rewrite.go`): strength reduction moved here from the AArch64
emitter and now reaches RV64; helper expansion and reduction unrolling
sit on the same footing with their obligations named. Layer B lowers and
optimizes per ISA under the seam checker and the verifier, today as a
candidate search over the lane's transforms
(`optimizer-search-2026-09.md`, another session's work). Layer C is
per-processor cost data for layer B's selection and scheduling, still to
come. The chain: source equals rewritten body (A), rewritten body equals
instructions (B), instructions mean what Arm's ASL and the RISC-V Sail
export say (the assembler's proofs); `-verified` demands all of it.

## Generic optimization coverage index

The familiar compiler-optimization taxonomy is a completeness index, not one
destructive pass order. Oak places every family at the highest semantic layer
that still has the facts needed to prove it, and leaves profitability to
candidate selection.

| Family | Techniques tracked for Oak | Placement |
| --- | --- | --- |
| Basic block and local | basic-block formation; peephole optimization; local value numbering | OptIR for semantic identities, MachineIR for representation-only peepholes |
| Data flow and SSA | available expressions; common-subexpression elimination; constant folding; dead-store elimination; induction-variable recognition/elimination; live-variable analysis; upwards-exposed uses; use-definition chains; reaching definitions; global value numbering; sparse conditional constant propagation | generic OptIR analyses; GVN/DCE and analysis-only SCCP are the first executable pieces; dead stores wait for projected memory identities and Mod/Ref/alias facts |
| Loops and parallelism | automatic parallelization; automatic vectorization; induction variables; loop fusion; loop-invariant code motion; inversion; interchange; nest optimization; splitting; unrolling; unswitching; software pipelining; strength reduction | structured OptIR before flattening, then target-neutral plans; ISA costing and scheduling only after the plan |
| Control and whole program | bounds-check elimination; compile-time function execution; dead-code elimination; expression templates/specialization; inline expansion; interprocedural optimization; jump threading; partial evaluation; profile-guided optimization | checked specialization and proof-derived facts first; bounded compile-, load-, or runtime candidate selection where facts remain dynamic |
| Functional | deforestation/fusion; tail-call elimination | semantic operation graph and structured control before physical allocation |
| Static analysis | alias, array-access, control-flow, data-flow, dependence, escape, pointer, shape, and value-range analysis | reusable proof domains feeding legality, representation choice, and costs |
| Machine code | instruction scheduling; instruction selection; register allocation; rematerialization | MachineIR and per-target backends; AArch64 first, the same contracts reused by RV64 |

## The program, in measured order

Each increment names its gap, its gate, and its measurement; none lands
without the measurement rerun on the kernels it targets and the verdict
column unchanged or improved.

1. **Strength reduction of constant arithmetic** (landed 2026-09-15,
   `94-assembler.md` §9.ac, then §9.ag). A multiplication by a power of
   two is a shift, an unsigned division or remainder by one a shift or a
   mask, a division by a nonzero constant loses its zero test. First in
   the AArch64 emitter; since layer A (§9.ag) the power-of-two sites are a
   body rewrite on every lane, each decided at the bit level before it
   applies, proposed by the `strength-reduce` transform of the candidate
   search, the plain body the identity. Read off the kernels: `search`'s
   loop three instructions shorter and without the divide, `page_probe`
   without its three divides and two multiplies; timing rows deferred to
   a quiet host.
2. **Vector locals in registers across calls** (landed 2026-09-15,
   `94-assembler.md` §9.ad): homes in v16–v31 saved around a call only
   when live after it; the checker now forgets v16–v31 at a call (a gap
   closed) and the verifier reloads a saved vector lane for lane. Read
   off the fixture, not the kernels: the helper expansion has flattened
   every calling vector body in the kernel package, so the row that
   remains is the flattened one — forty vector locals against
   thirty-two registers, where the leaf path hands out twenty homes and
   the rest spill. The next step is therefore **a liveness-based
   allocator for leaves**: registers reused across disjoint live ranges
   (the last-use release exists; the pool must be sized by simultaneous
   liveness, not by declaration count) and spills chosen by use count.
   Target: UTF-8 (5×), then inlining pays instead of hurting. **Also landed 2026-09-16
(`94-assembler.md` §9, forty-seventh increment):** the flattened
validator copied every vector operand into a scratch and every result
back — fifty `orr`s — because the vector path had none of the in-place
reads and result retargeting the scalar path has; with them and literal
splats as `movi`, the body is 330 lines from 611 and the validator 1.2×
the C backend from 1.65× in one alternated run. The five spilled locals
are the allocator's case above.
3. **A leaf's vector locals in the argument registers** (landed
   2026-09-15, `94-assembler.md` §9.af): v1–v7 past the vector
   parameters as homes, the scalar leaf scheme for the vector file. The
   validator's loop goes from forty q-register frame accesses to none,
   its body from forty-one to one, both bodies still proven. The
   liveness allocator proper — registers reused across disjoint live
   ranges beyond the last-use release, spills chosen by use count — is
   still ahead for bodies wider than twenty-seven vector locals; the
   validator no longer needs it. Target: UTF-8 (5×) measured on a quiet
   host, then inlining pays instead of hurting.
4. **Idioms the verifier can already equate**: a little-endian word
   assembled from consecutive guarded byte reads is one load under one
   guard (the verifier's memory model gains reads wider than the element;
   `asm/verify.go` refuses a width mismatch today); constant-offset
   guards under a proven length fact are redundant (extent propositions
   at the seam, row 7). Target: `crc32c` (5.7×) and every codec's word
   reads.
5. **Reductions unrolled with independent accumulators** under a declared
   associativity law (row 5) — integer `+` and `|`, `&`, `^`, `max`,
   `min` have it by the language; floats never do. Target: `sum`, `dot`
   (3.2–3.4×). Gate: the verifier's loop invariants over the unrolled
   shape; where it cannot yet couple two loop shapes, the fallback is the
   scalar loop, and the verifier's reach is the next item.
6. **Non-aliasing to the C backend** as `restrict` on span parameters and
   the local pointers loaded from them, alignment facts as
   `__builtin_assume_aligned`, refinements and extents as
   `__builtin_assume` at loop headers: the C backend "a real backend"
   (`performance.md` §9). Measured by `-opt 2` before and after on the
   kernels; the C compiler's vectorizer is the consumer. **Measured
   2026-09-16 before landing, and found neutral on clang 21:** two store
   loops over a span and a view (`dst[i] = dst[i] + src[i] * k` over
   `u32`, `dst[i] = src[i] ^ k` over bytes) vectorize identically with
   and without `restrict` base pointers (`-Rpass=loop-vectorize`: width
   4×4 and 16×4 both ways) and time the same within noise (0.10–0.15 and
   0.016–0.026 ns per element, alternated), because clang versions the
   loop on a runtime overlap check whose cost is a compare per call. The
   `restrict` emission is therefore not landed; the alignment and extent
   assumptions wait for a loop where the C compiler demonstrably peels
   or checks what Oak has proved. The native lane is where the aliasing
   fact pays (row 2's consumer is the verifier's store log), not the C
   compiler.
7. **Scheduling and selection** for the two lanes' pipelines once the
   allocator exists: load latency hidden across the loop body, `madd`
   and `csel` forms, conditional compares.

Not on the list, by doctrine: any transform the source did not license
(fast-math, speculative reassociation of floats, undefined-behavior
assumptions), any change in meaning or visible cost, and any flag that
answers a benchmark instead of an expressiveness gap.

## Measurement discipline

`benchmarks/native/emit` and `run.sh` build every kernel through both
backends; `benchmarks/kernels` times them against Go and Rust;
`BENCHMARKS.md` keeps the table. An increment reports the rows it
targets before and after, the verifier's verdict per body (proven,
witnessed, trusted, refused-and-fallen-back), and the host's load; a
row that moves without its verdict holding is not a result. The native
lane's numbers are compared to the C backend's at `-opt 2`, and the C
backend's to Rust's, so the two ratios compose into the goal's claim.
