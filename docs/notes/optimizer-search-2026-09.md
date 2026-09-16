# Candidate-search optimization for Oak

Status: design note, September 2026.

This note proposes the architecture for Oak's optimizing native backend after the first verified optimization increments in `nativegen/`: strength reduction, condition selection and if-conversion, aggregate promotion, wide-load fusion, reduction unrolling, and pair loads. It complements `docs/notes/optimization-2026-09.md`, `docs/notes/native-optimization-2026-09.md`, `docs/spec/90-backend.md` §16, and the semantic verifier in `docs/spec/94-assembler.md` §9.

Three companion catalogs feed this architecture:

- `docs/notes/llvm-optimization-catalog-2026-09.md` records conventional compiler analyses, transforms, vectorization, IPO, register allocation, scheduling, and target-cost patterns worth adapting from LLVM;
- `docs/notes/mojo-futhark-optimization-2026-09.md` records staged specialization, structured and algebraic planning, index properties, destination forwarding, storage coloring, and compile-time/runtime candidate versioning;
- `docs/notes/proof-guided-optimization-2026-09.md` records Oak-native optimizations enabled by checked type facts, ownership, effects, refinements, extents, typestate/protocol models, declared laws, proof infrastructure, and semantic verification down to the selected assembly body.

The central rule is:

> **An optimizer proposes implementations. A cost model chooses among them. Independent validation decides whether the chosen implementation is admissible.**

Optimization should therefore grow as a library of small transforms and planning rules, not as one correctness-critical sequence of mutually dependent compiler rewrites.

## 0. Status (2026-09-15): Phase A landed

The planning substrate of §16 Phase A is implemented on `specification`:

- `opt/` — the target-independent substrate: `Fact`/`Proposition`/
  `Provenance`/`Requirement` (proof-carrying facts, §4 and the
  proof-guided note §1), `Transform`/`Registry`/`Phase`/`ProofKind`
  (§2, §4), `Candidate` (§3), `Metrics`/`CostModel`/`TargetCosts` (§8,
  §9), `Report`/`Remark` (§9), and `Search` — the bounded beam search
  with checker-driven refinement, cost-ordered validation under a
  validation budget, and the identity as the last candidate (§6, §15).
  `opt/opt_test.go` covers selection, fallback, requirement gating,
  pruning of unchanged and duplicate bodies, refinement, and budgets
  against a fake lane.
- `nativegen/opt.go` — the native lane's side: the six transforms the
  lane performs (`strength-reduce`, `elide-guards`, `reuse-flags`,
  `hoist-invariants`, `vector-homes`, `unroll-reductions` — the
  unrolling first in the loop phase since 2026-09-16, so the invariant
  pass and `rotate-loops` are applied to the unrolled shape: a transform
  that fires on nothing leaves the frontier, so one that fires only on
  another's output must follow it), then
  `reallocate` and the first transform written for the registry,
  `late-cleanup` (§11 "Machine", late copy/branch cleanup:
  `nativegen/cleanup.go`, a block-local peephole under a whole-function
  register liveness, 2026-09-16), as
  `opt.Transform`s over `Lane` configurations, each with its phase,
  proof kind, and requirements; `FunctionFacts` reading the
  typechecker's proved indices and the language's integer associativity
  laws into facts; `Metrics` over a lowered body (instruction classes,
  guards, and per loop the counts, the stride read off the index
  register's increment (the register a test compares and the loop
  writes only there: a scratch register a guard compares and the body
  reloads before adding a constant is not the index), and the trip bound of a remainder loop after a
  strided one); `Registry`, `PlainLane`, `FindingLine`.
- The cost model (`opt.TargetCosts`) is static and per class: straight-line
  code at weight one, each loop body at `LoopWeight` trips divided by its
  stride and bounded by its shape's trips — and, since 2026-09-16,
  multiplied by the trips of every loop around it: a nested loop's items
  are its own (`LoopMetrics.Depth`, `Outer`), not its outer loops', and
  weigh `LoopWeight` squared at depth one, where the additive reading
  before priced the search kernel's inner-loop rotation a loss and now a
  win — so a four-way unrolled
  reduction is priced per element against the plain loop and its
  remainder loop as its expected few trips. The weights are uncalibrated
  heuristics (§8); the report's `candidates` line lists every admitted
  candidate with its cost and shape so a wrong estimate is visible. The
  first thing the report found: without the stride the static count
  priced the unrolled reduction above the plain loop, and the search
  would have verified the plain loop first.
- `compiler/native_search.go` and `compiler/native_bodies.go` — the
  hand-written fallback ladder (elide, then hoist, then reuse, then
  strength, then the plain reduction) is replaced by one search per
  body with a `Driver` that lowers, keys, measures, checks, and verifies
  through the verdict cache. The compiler's diagnostics keep their
  phrasing; `-opt-report` / `OAK_OPT_REPORT=1` print the report;
  `OAK_OPT_BEAM` overrides the beam for experiments. `-opt` keeps its
  one meaning (the C compiler's level).
- The executable-oriented source pipeline has an explicit specialization
  boundary. Conservative private-leaf inlining runs before specialization;
  built-in Bool identities and exact fixed-width integer zero/one identities
  run after concrete types are known. A fresh checker validates every changed
  monomorphic program. Its validation clone receives only generic ADT
  declarations recorded by the specializing checker, rebuilt through the same
  checked substitution used by native lowering; those declarations never enter
  emission. Source and native remarks share `opt.Report`.

Policy as landed: the identity is the fallback and is verified last, so
an admitted transformed body is preferred to the plain lowering even when
the static model prices it slightly higher (the model cannot see register
residency); among transformed bodies the model decides. The first case
where that mattered: before the vector operands moved in place (#484),
`vector-homes` on an accumulator carried through a call inside a loop
saved and reloaded it around the call exactly as the slot form stored and
loaded it, plus two moves per trip, and the search kept the hoisted slot
form; after #484 the home form is the cheaper and is selected. What a
vector move and a frame-slot round trip cost is calibration work for the
benchmarks (§8); the report's `candidates` line is where to read it. The
tie-break landed with `late-cleanup` (2026-09-16): at one cost the
candidate with more transforms applied comes first in the beam and the
validation order (`opt.cheaper`), and the loop stride is read from the
last increment of a compared register, the index's step before the back
edge, not the first.

### Phase B, first increment: `machine/`

The machine-level representation and the global allocator exist as a
lift of the emitted body rather than a new lowering target: `machine.Lift`
reads an AArch64 `asm.Function` into blocks and instructions with every
definition and use explicit (a per-mnemonic shape table; an instruction,
operand, or control shape it does not know refuses the lift), builds the
control-flow graph, computes reaching definitions and the def-use webs
that serve as virtual registers, global liveness with precise live
segments (a value saved before a call and reloaded after it is not live
across it), and recolors the webs nothing pins — entry values, the
procedure-call contract, reserved registers, dead definitions — with a
linear scan: a copy partner's register when free (the copy is then
removed), else its own, else the lowest free register of the pool, which
is the registers the lowering already wrote, so the frame, the prologue,
and the epilogue stand as emitted. Ranges crossing a call take
callee-saved registers only, wide vector webs never v8–v15 across a
call, and a copy narrower than its source's writes or its destination's
reads is never removed. A web that finds no register is pinned and
allocation restarts, so at worst every web keeps the lowering's coloring.
`nativegen`'s `reallocate` transform runs it as a machine-phase candidate;
on the vector-homes test bodies the verifier proves every reallocated
form and the search selects it, two to seventeen copies fewer per body.

Second increment: frame-slot promotion (`machine.Promote`), the inverse
of spilling. A frame slot every access of which is a plain load or store
of one width and class, that overlaps no other frame access, whose
address is never taken, that lies within the declared frame, and whose
every read a store reaches, joins the web machinery as a pseudo-register;
its value moves into a register free over its live range (a saved
callee-saved one when the range crosses a call, never v8–v15 for a wide
vector), the store and the loads become copies, and reallocation
coalesces them. The allocation pool also gains the caller-saved registers
the body never wrote, for ranges that cross no call. On the vector-homes
test bodies the general promotion now does what the hand-written
`vector-homes` transform did and the search selects the cheaper of the
two forms; the test asserts the outcome (the locals' slot traffic) rather
than the mechanism, and the compiler reports promoted slots beside kept
homes.

Two rules this increment forced. A trusted verdict is the absence of a
check, so when no candidate is judged (the verifier cannot yet follow a
body — a call returning an array, say) a transform that ships only on a
verdict (`opt.Gated`) is set aside for the cheapest form without it, at
worst the plain lowering, whatever the cost model says; the lane's
long-standing transforms ship on the checker's admission as they did
before the search, and `reallocate` is gated until it earns that standing
(`opt.Search`, docs/spec/90-backend.md §16 rule 3). The rule came
from a real miscompile the tests caught: promotion had treated a `u32`
element stored as a word inside a chunk the body reads whole as a slot of
its own, and the two affected bodies were exactly the trusted ones. The
overlap test now weighs every access at a neighboring offset at its own
width, with a regression test.

Third increment: the callee-saved pool grows. A slot live across a call
with no saved callee-saved register free takes the next of x19–x28 the
body does not write, and the promotion adds its save after the prologue's
last save and its restore before the epilogue restores the frame pair, at
the next eight-byte slot of the lowering's save area — when the prologue
and the single epilogue have the lowering's shapes, the slot lies within
the frame, and it overlaps no other frame access (`growCalleeSaved`). A
callee-saved register's own save slot is never promoted: that would only
move the obligation. The checker's save/restore obligations judge the
edited prologue and epilogue like any other body.

Fourth increment: the RV64 lane. What the package knows of a lane — the
instruction shapes, the register files and their spellings, the
procedure-call contract, the copies, the frame-slot accesses it may
promote, and the lowering's prologue and epilogue — is a target
descriptor (`machine/target.go`), and the RV64 one lifts the lowering's
`mv`/`fmv.d` copies, `ld`/`sd` and `fld`/`fsd` slots (only whole words:
`sw`/`lw` extend on the way back, which a copy would not), the `call`
contract (a0–a7 and fa0–fa7 read; ra, t0–t6, a0–a7, and the ft/fa files
written), and the `sd ra`/`sd s1`… prologue for callee-saved growth. The
vector extension's registers refuse the lift for now. The `reallocate`
transform runs on both lanes.

### Phase C, first increment: analyses and cleanups over the lifted IR

`machine.Dominators` builds the dominator tree (Cooper–Harvey–Kennedy
over a reverse postorder) and `Loops` the natural loops from its back
edges — headers, latches, bodies, preheaders, nesting — as analyses for
the passes to come (machine-level LICM and induction detection). Two
global cleanups use the webs and the liveness segments (`Simplify`, run
inside reallocation before allocation): copy propagation reads a copied
value from its source wherever the source has one definition and is
still live (so another web of the same register — a call's result, a
later assignment — cannot have taken the register in between), and
dead-code elimination removes an instruction whose every result no one
reads when the lane's table says it is pure (no store, call, branch,
compare or flag write, atomic, or system effect; loads only from the
frame) and it writes no callee-saved or reserved register (a restore).
Both refused wrong forms in their first tests — a propagation across a
call's clobber, an elided callee-saved restore — before the liveness and
the restore rule were added; the checker would have refused the bodies,
but the pass should not propose them.

Second increment: machine-level loop-invariant code motion on the loop
tree (`machine.HoistInvariants`). Innermost loop first, an instruction
moves to the loop's unique preheader when it is pure and reads no
condition flags, defines one register whose web has that single
definition and is neither pinned nor reserved, has every input defined
outside the loop, loads from the frame only when the loop neither stores
through sp nor calls, and clobbers no other web of its register anywhere
from the preheader to the loop's end — a hoisted value read inside the
loop is live around every trip, which the first refusal test caught when
the check stopped at the last use. One instruction moves at a time with
the webs and liveness recomputed, so every decision reads current
ranges; an inner loop's invariant climbs again with the outer loop in the
next round. The lowering's own hoisting (nativegen/licm.go) runs first as
its own transform; this pass takes what remains after every other
transform, inside reallocation, and the verifier judges the result.

Third increment: the recurrence analysis (`machine.Shapes`,
`LoopShapes`), Oak's ScalarEvolution scoped to what the planners need.
For each natural loop it finds the basic induction variables — a
general-register web with exactly one definition inside the loop, an
add or subtract of an immediate to itself whose block dominates every
latch, every other definition outside — with the step, the start when
its one outside definition materializes a constant, and the exit test:
a compare in a block dominating the latches between an induction and an
invariant register or an immediate. A trip bound follows only where the
arithmetic cannot wrap (a known start against an immediate bound with a
positive step, in int64, withheld otherwise), and the remainder loop
after a strided loop over the same induction web and bound runs fewer
than the stride's trips. The cost model's stride and trip hints now come
from this analysis, the register-increment heuristic standing in only
when the lift refuses a body. The first test body exposed a reaching-
definitions slip: a loop whose header is the entry block never saw its
back-edge definitions; the entry now merges its predecessors too.

Fourth increment: the lift admits the extended- and shifted-register
operands of address arithmetic (`add x9, x19, w3, uxtw #2`), which had
kept reallocation off every body with a scaled index; and the lowering
records the aggregates it places in the frame (`nativegen.FrameObjects`),
so promotion blocks only the object whose address is taken rather than
everything above it (`machine.PromoteWith`). An exit bound computed in
the header from invariants (`sub w9, w20, #16`) counts as invariant for
the recurrence analysis, and a loop the analysis cannot read keeps the
heuristic's stride rather than losing it — the vectorized reduction's
sixteen-element trips were priced at stride one for one test run.

Fifth increment: post-allocation instruction scheduling
(`machine.Schedule`, the `schedule` transform, gated). Within a block,
between barriers — calls, returns, traps, branches, memory barriers,
atomics, sp writes, system instructions, and the flag-setting compares,
which keep their place so the verifier's loop and condition shapes
survive — instructions list-schedule by critical path over a dependence
graph of register reads-after-writes at the producer's latency, writes
after reads and writes, the condition flags as a pseudo-register, and a
conservative memory order (a store against every memory instruction,
loads past loads). The cost model gains a stall term
(`machine.StallEstimate`: the latency a consumer's distance from its
producer does not cover, at most eight apart), straight and per loop, so
a better-scheduled body is priced lower; the first version without the
compare barrier scheduled bodies past the verifier's path budget, which
the vector-homes test caught. Three corrections to the measure followed
from the suite: it counts across barriers and block boundaries (a guard
branch between a divide and its consumer hides none of the latency on
the fall-through path, so the branch-free strength-reduced form was
being charged stalls the guarded form skipped), a pair whose two
instructions lie in different loops counts once and in no loop's share,
and a fall-through block without a label counts under the label before
it (the top-tested loop's body block has none, and its load's stall was
being lost while the rotated form's was charged). And one correction to
the scheduler itself: the RV64 checker reads the length normalization
`slli rX, len, 32; srli rX, rX, 32` as one definition only as adjacent
halves, so a schedule that slid a copy between them lost every guard on
the length and was refused; the target now names such *bonded* pairs
(`target.bonded`) and the scheduler moves them as one unit, after which
the RV64 binary search's scheduled form is admitted and proven.

Not in this increment: live-range splitting, vector callee-saved growth
(d8–d15, fs0–fs11), RVV bodies, a lowering that emits virtual registers
directly, and exact trip counts against register bounds.

### Phase B, sixth increment: the lift reads the vector extension

The RV64 target knows the RVV instructions the lane emits
(`machine/target.go`): the vector registers are the lift's `VEC` class at
128 bits and keep their assignment (reserved: the RVV psABI binds v8 at
the boundary and the checker's fixed configurations name registers), the
configuration `vsetivli` is a barrier no vector instruction crosses,
loads and stores carry their memory operand, the accumulating forms
(`vfmacc`, `vslideup`, `vmv.s.x`) read their destination, and every
vector register is caller-saved with v8–v23 as arguments. A frame address
(`addi tX, sp, off`) is not pure on this lane: the checker admits vector
memory through a frame address formed beside the access, and a hoisted
one written twice is no address to it. The recurrence analysis reads a
register-form stride (`li t0, 4; addw t1, t1, t0`), takes a loop's single
induction as its index when the exit test is a computed flag, and bounds
the remainder loop after such a strided loop. With that, RV64 vector
bodies lift, schedule (`vsetivli` regions), reallocate their scalar
registers, and price by stride — what the RV64 map vectorization needed
from this side (item 24 below).

### Phase B, seventh increment: peephole fusion over the lifted IR

`machine.Fuse` (the `fuse` candidate, gated like the reallocator and the
scheduler) folds two instructions the lowering spells one after the
other into the one AArch64 instruction that does both, where the lifted
webs show the intermediate register has one definition and one use in
the same block and nothing the pair reads changes in between: a shift
into an add's shifted operand (`lsr w9, w9, #1; add w25, w7, w9` → `add
w25, w7, w9, lsr #1`) and an increment into a csinc (`add w10, w25, #1;
csel w7, w10, w7, lo` → `csinc w7, w7, w25, hs`). The binary search's
inner loop — `search` and `page_probe` in `benchmarks/kernels`, the two
largest gaps left in proven or witnessed code — was eleven instructions
against clang's nine for the same source, and these two fusions are the
difference but for clang's `ccmp`, which combines the loop's two exit
tests into one branch. That fusion ships too (`machine.FuseExits`, the
`fuse-exits` candidate, gated): a bottom-tested loop's tail `b.cond exit;
cbz wR, back` becomes `ccmp wR, #0, #nzcv, !cond; b.eq back`, the
constant flags failing the branch where the first test exited, and the
loop's entry test — the same two tests, both to the exit, the mirror the
verifier's tail shape needs — becomes `ccmp wR, #0, #nzcv, !cond; b.ne
exit`, the constant flags taking it. Three readers had to learn the
form. The seam checker carries the compare's fact through the conditional
compare to the branch it feeds (`ccmpFact`), in both polarities: where
the constant flags fail the branch, the taken path knows the first
compare's fact under its condition (the back edge, so the loop body's
elided guard stands); where they take it, the fall-through knows it (the
entry test, so the loop is entered under `lo < hi` as before). The
verifier's tail shape (`tailLoopShape`) accepts a `ccmp` in the tail run
and before the back edge, so the fused loops are judged by the loop
argument rather than a path budget spent unrolling them — without it every
such form came back trusted, which is why the transform sat unregistered
for a commit. And the search's shape rule: validations were spread over
shapes with the gated transforms struck from the name, which lumped the
exit-fused form with its parent and never validated it; gated transforms
now declare whether they are shape-neutral (`opt.Neutral` — the
reallocator and the scheduler are, the fusions are not), and only the
neutral ones drop out of the shape. The exit-fused search loop is ten
instructions and one branch (clang's nine and one), priced the same as
the pair-fused form's ten and two — the model prices a branch as an
arithmetic instruction, and `ccmp` is one — so it wins on the tie-break
toward more transforms; a branch weight above one would separate them,
left for a measurement that shows the branch's cost. Measured on the clock, the two pair fusions
are neutral within noise (`search` 1.11× against 1.12× unfused,
`page_probe` 1.20× against 1.22×, native over the C backend, three
interleaved runs each): the loop is bound by its load-compare-select
chain, not its instruction count, which is the argument for the exit
fusion — one branch to resolve per trip instead of two. The seam checker had to learn
the fused midpoint: its bound arithmetic followed `sub; lsr; add` to
`mid < hi` (Oak.Assembler.midpoint_below) and read the shifted-operand
add as nothing, so the fused form kept its element guard and priced
above the unfused one until `asm/bounds_arith.go` took the halving off
the operand — the same lemma, one instruction. With that the search
selects the fused forms for both kernels (`search`'s loop 10 instructions
from 12 with the guard, cost 3732 against 4116).

### Phase D, second increment: order-preserving fold vectorization

The kernel table's `dot` at 1.31× was the last gap in proven code with a
transform behind it: clang vectorizes the products (`fmul.4s` over four
elements, sixteen a trip) and keeps the additions in source order, one
`fadd` per element, where the native loop ran scalar — two loads, a
multiply, an add, and the loop's three instructions per element. Float
addition does not reassociate, so `vectorize-reductions`' four strided
accumulators are out; but the element work vectorizes without touching
the order. `vectorize-folds` (`nativegen/vector_fold.go`) rewrites a
reduction whose element expression is lane-wise over span parameters of
one length — the map vectorization's reading of the expression, spans at
the loop's index, invariant scalars, constants, and the lane-wise
operators — into a main loop that computes one vector of element values
and adds its lanes to the accumulator in element order through
`simd.extract`, under the slack guard, with the remainder loop as written.
The license is `Oak.Fold.blocked_eq` (`spec/lean/Oak/Fold.lean`): the
blocked fold equals the sequential fold for any lane function and any
accumulation, so no law of the element type is used and the float
accumulator rounds as before. The verifier already read every instruction
the form needs (vector loads at wider lanes, `fmul` over an arrangement,
the lane move `mov sD, vN.s[k]`), so the dot products prove
(`compiler/e2e_native_vector_fold_test.go`: `f32` and `f64` dot products
and a scaled sum; a bare float sum is left scalar, a vector saving it
nothing). The first form of `bench_dot`'s loop was twenty instructions for four
elements — two vector loads, the multiply, four lane moves, four adds,
and six instructions of tests it did not need. The second span's slack
test stood although the loop sits under `len(a) == len(b)`: the vector
load decides its own guard from the enclosing loop conditions
(`provenLanes`), which name the first span only, so the lowering now
carries the conditionals' length equalities (`equalLens`, read as the
map recognizer reads an arm) and a slack fact over one span is the
fact over its equals. The checker then had to agree, in three places
where it read a length register literally: the minimum a `cmp wL, #K;
b.lo` proves (`measuresLen`), the element region an `add xE, xB, wI,
uxtw #s` derives (the bound's register substituted for the span's own
before the Lean-mirrored decision, Oak.Assembler.index_under_equal_len),
and `lenLike` — each resolving the equality through any register that
holds the same length, since the compare reads the copy (`w20`) where
the slack fact names the primary (`w1`). And with no guard left to peel,
the invariant pass hoists the condition's invariant half instead of
leaving it in the header for the rotation to copy into the tail. The
loop is sixteen instructions for four elements, one compare a trip,
priced 1789 against the identity's 5537, proven.

### Found by the harness: a miscompile in the plain lowering (2026-09-16)

The kernel harness (`benchmarks/kernels/run.py`) refuses timings until
every implementation's checksum agrees, and the night's run of the ten
kernels found `blake3` disagreeing between the C backend and the native
one. The search played no part — withholding every transform
(`OAK_OPT_SKIP`) changed nothing — so the plain lowering was wrong, in a
body the verifier trusts (an indexed load through a record argument) and
whose callers it trusts for calling it. Three debugging knobs came out of
finding it, all default off: `OAK_OPT_SKIP` withholds named transforms,
`OAK_NATIVE_ONLY` lowers only the named functions natively (the rest stay
with the C backend, so a disagreement bisects to one function), and
`OAK_NATIVE_TRACE_SLOTS` prints every frame-slot event. The defect was in
slot recycling: a scalar-replaced array's binding carries a zero offset
and none of the markers the release paths check for, so its last use
returned frame slot zero — a live array's — to the pool
(`nativegen/liveness.go`, `popScope`; the write-up is in
`benchmarks/kernels/RESULTS.md`). Two lessons for the architecture: the
verifier's trust boundary is where miscompiles live, so the harness's
checksum gate is part of the landing rule, not a benchmark nicety; and a
loop-free cut of the same body was refuted by the verifier at once, which
is the argument for keeping bodies decidable wherever the source allows.

### Phase D, first rewrite after the reductions: map vectorization

`vectorize-maps` (`nativegen/vector_map.go`; item 24 below) is the
first layer-A rewrite whose license is lane-wise semantics alone
(`Oak.Map.blocked_eq`, `spec/lean/Oak/Map.lean`: the blocked map over a
list is the element-wise map, for any function of one element), so it
carries no fact requirement and its remainder loop is the source loop
itself. It reads span parameters only, and it knows two spans have one
length only from an enclosing `len(dst) == len(a) ? { … }`, the shape
the seam checker admits for a store through one span under the other's
guard. The increment's cost was in the verifier, not the rewrite: the
hoisted form's remainder loop proved only once a premise could say that
a skipped loop leaves its variables at their header values.

Explicit builtin FMA now participates in this lane-wise map vocabulary.
Checked invocation identity/width is required; every argument must itself be
lane-wise, and the vector form keeps the scalar intrinsic's single rounding.
This is an instance of the existing map theorem, not implicit contraction,
reassociation, or a new numerical-error license. Measurements and the rejected
scalar-dot contraction experiment are in `benchmarks/native/exact_fma/README.md`.

### Phase C, checked projection and first analysis: `optir/`

The target-neutral structured representation now exists independently of
emission. It retains typed scalar operations, effects, attributes, proof facts,
conditionals, and pre-test loops with explicit loop-carried values. Its
deterministic projection introduces typed block arguments at joins, loop
headers, bodies, and exits. An independent verifier checks structured
arity/types and CFG definitions, same-block order, dominance, reachability,
terminators, exact edge types, Bool branches, and returns.

`Compilation.OptIR()` now starts from the ordinary checked semantic model and
projects each supported concrete scalar function into that representation. The
initial subset covers fixed-width integers, Bool, unit, locals, assignments,
structured branches and short-circuiting, exhaustive Bool matches, pre-test
loops, value-preserving integer widening, and effect-marked calls. Unsupported
memory and richer language forms are deterministic per-function refusals; a
projection or verification inconsistency fails the complete analysis request.

SCCP independently validates its operation vocabulary and computes exact
constants plus executable blocks and edges. Integer folding follows Oak's
fixed-width wrapping, signedness, division-overflow, and logical-shift
semantics. A separate transform consumes exact, independently recomputed SCCP
evidence to replace known closed total-pure results, select known branches,
remove unreachable blocks, and perform bounded SSA-aware block/trampoline
cleanup. The transformed CFG verifies independently and still authorizes no
emission without the ordinary candidate gates.

The analysis includes closed total constant-result identities: exact-SSA self
subtraction/XOR, reflexive integer/Bool comparisons, multiplication/AND by zero,
and OR with width-correct all-ones. Unknown operands defer an absorbing transfer
until both inputs have lattice information, keeping later phi refinement
monotone. These rules expose branch/zero-trip-loop removal through the existing
rewrite and post-memory cleanup; no target-specific pass or new search dimension
is needed. An unused call/load/trap result never licenses deleting its producer,
and two calls to the same function are not the same SSA value. Floats, division,
shifts, and attributed/effectful operations receive no such identity rule.

Before GVN, unused non-entry block parameters and their exact incoming edge
positions are removed to a bounded fixed point; proof facts count as uses. Then
trivial phi-like block parameters are removed only when every explicit incoming
edge resolves to the same dominating SSA definition (with a self loop edge
allowed for an invariant). Entry parameters are never inferred from backedges
because their ABI inputs are implicit. Edge argument positions, uses, and facts
are remapped and the CFG verifies again. GVN then runs on that CFG. It numbers
plain copies alike, canonicalizes exact commutative integer/equality operations
and inverse order comparisons, then shares a congruent expression only from a
dominating definition. DCE removes the exposed unused pure chains and copies to
a fixed point. Both are restricted to a closed vocabulary of total scalar
operations: missing effect metadata never makes calls, traps, memory, or
unknown operations removable, and an unknown attribute disables algebraic
normalization. Proof facts are remapped only where they remain valid. Input and
output pass the independent verifier, and `Compilation.OptIR()` retains each
CFG version beside deterministic SCCP-rewrite and GVN/DCE reports.

OptIR also has its semantic loop analysis: reverse postorder and immediate
dominators; natural loops with back edges, latches, exits, canonical preheaders,
parents, and depths; and typed affine recurrences over explicit loop-carried
block arguments. It normalizes the unique continuation predicate and proves an
exact constant trip count only when a monotone fixed-width recurrence reaches
the exit without wrapping. Symbolic bounds, multiple exits, latch disagreement,
and wrapping boundaries retain only the facts actually established. These
results complement MachineIR's structural loop tree: OptIR owns Oak arithmetic
meaning, while MachineIR owns eventual layout and scheduling.

Its first loop transform is LICM. After GVN/DCE it moves a closed
total-pure operation to a canonical preheader only when all operands are
available there. Potential traps, effects, calls, memory, unknown operations,
noncanonical entries, and facts other than the definition-local checked type
fact pin the operation. The checked type fact carries an opaque source/type
proof ID and is matched against immutable typechecker authority after every CFG
rewrite; transformed metadata cannot authorize itself. The cloned result passes
the independent verifier and is retained with deterministic movement evidence.
A changed final CFG enters
native search as the verifier-gated `optir-emit` candidate. Target-neutral SSA
liveness/interference coloring precedes closed AArch64 and RV64 selectors. The
RV64 selector preserves canonical sign-extended 32-bit values and explicitly
zero-extends unsigned widening. Both selectors now admit a deliberately closed
direct-call form: a known Oak body with zero through eight matching
Bool/8/16/32/64-bit scalar arguments and exactly one
matching scalar result, represented by exactly `EffectCall` plus one nonempty
`callee` attribute. Since the available colors are caller-saved, any other
non-unit value live across the call refuses the candidate. An admitted calling
function reserves a sixteen-byte save area for AArch64 `x30` or RV64 `ra`,
places the ABI register arguments as a simultaneous parallel copy whose cycles
use the selector's reserved scratch, and normalizes the result at the boundary.
A ninth or stack argument, all broader call forms, and other effects still
refuse. The independently verified abstract spill plan is materialized on
AArch64 and composed with this call frame. Spilled constants and bounded copy
chains may instead be rematerialized after independent recipe verification and
a target cost check; accepted recipes remove their physical slots, while
expensive literals stay spilled. A canonical AArch64 pre-test loop now keeps
its Bool predicate register-resident and machine-proves a loop-carried `u32`
spill through the backedge. RV64 materializes acyclic CFGs with no effect
except an admitted direct call, plus one exact call-free natural loop with a
unique preheader, conditional header, straight-line latch, and return exit.
The loop predicate remains in a register, only aligned four- or eight-byte
spill slots cross its backedge, and broader cycles refuse. Canonical scalar
slots live in a bounded 16-byte-aligned frame, at most two ordinary spilled
operands use reserved `t5`/`t6` scratches, and simultaneous register/slot copies
cover SSA edges and call arguments. Its `ra` save area sits above the spill
slots in the same frame. Width-correct stores, signed/narrow reloads,
production-pressure diamonds, spilled returns, a composed spill/call frame,
and a loop-carried `u32` spill are machine-proven. On acyclic CFGs, RV64 also
independently verifies constant-rematerialization evidence, admits only exact
Bool/integer constants whose encoded-word cost beats their store/load traffic,
compacts fully reconstructed slots, and rebuilds uses including call arguments;
wide expensive constants remain physical. Broader RV64 loops and calls,
copy-chain rematerialization, and cyclic rematerialization still refuse. The
direct lowering remains the identity,
and every selected OptIR body must pass seam admission and semantic translation
validation; refusal or a trusted verdict falls back.

The implementation topology is not yet one end-to-end pass DAG: `Stage.Then`
remains linear, and native candidate proposal enumeration still branches
internally. The generic OptIR chain is migrated. Immutable, exact-version nodes
hold CFG v0, SCCP, SCCP rewrite and CFG v1, loop structure/facts, GVN/DCE and
CFG v2, checked preservation, recomputed induction facts, and LICM. CFGs have
canonical content fingerprints.
Analyses declare a closed set of topology, SSA, operation, effect, type, fact,
and layout aspects. GVN/DCE's admission node independently compares per-aspect
digests for v1/v2; because `CFGTopology` is preserved, v2 reuses v1 dominance
and natural loops while recomputing recurrence facts from v2. SCCP's topology
changes force the first loop structure to be analyzed on v1. No certificate is
an equivalence verdict or emission license. Every native proposal has a
canonical checked-input recipe and materializes through candidate → admission
→ metrics → cost artifacts; every attempted semantic check is a verdict
artifact, and selection depends on candidate, clean admission, cost, and
verdict for every possible result. Validation stays sequential to retain the
budget and proof early-stop. The executor runs bounded deterministic ready
waves for independent analysis work. The complete design is
`optimizer-artifact-dag-2026-09.md`.

Not yet: aggregate/partial memory-region projection, multiple unavailable phi
inputs, broader load placement, partial/call-written versions, conceptual-entry
loop phis, non-affine and symbolic trip-count proofs,
unrolling and further loop transforms,
vector plans (Phase D),
and the proof-obligation service of the proof-guided note §26 beyond the
requirement/fact matching here.

## 1. Why this architecture

A conventional optimizer tends to evolve as a long destructive pipeline:

```text
source
  -> canonicalize
  -> inline
  -> strength-reduce
  -> unroll
  -> vectorize
  -> schedule
  -> allocate
  -> machine code
```

Each pass changes the input seen by every later pass. Over time the compiler accumulates ordering constraints, pass-specific canonical forms, profitability heuristics, and correctness assumptions that are difficult to reason about in isolation.

Oak does not need to make the optimizer itself part of the semantic trusted base. The native lane already checks the assembly seams and symbolically compares a generated body with the Oak body the verifier judges. A mechanical transform can therefore be treated as an **untrusted proposal generator**: if the proposed body proves equal, it may be used; if it does not, the compiler can choose another candidate or the identity lowering.

That changes the optimization problem from:

```text
which mutation should the compiler perform next?
```

into:

```text
which of these equivalent implementations should the compiler choose?
```

The identity implementation is always a candidate.

## 2. Three classes of optimization

Oak should distinguish three correctness mechanisms.

### 2.1 Mechanical candidates

These change representation or machine shape without changing the source-level evaluation law:

- register allocation;
- instruction scheduling;
- instruction selection;
- addressing-mode selection;
- pair or wide loads where the memory model equates them with the source reads;
- branch folding;
- condition selection;
- if-conversion where both arms preserve effects;
- copy propagation;
- spill placement;
- load/store reordering licensed by ownership/effects.

The transform implementation need not be trusted. The machine checker and semantic verifier validate the final candidate against its stable source reference.

### 2.2 Canonical semantic rewrites

These are local equalities whose validity follows directly from Oak's fixed-width semantics or another already-proved semantic law:

- constant folding;
- `x * 2^k` to `x << k`;
- unsigned `/ 2^k` to shift;
- unsigned `% 2^k` to mask;
- redundant masks and extensions;
- boolean and comparison simplification;
- address arithmetic canonicalization.

Where useful, these equalities should have reusable Lean theorems, as `Oak.StrengthReduction` does for the currently emitted power-of-two transforms. The optimizer still remains untrusted: the theorem or final semantic validator is the authority.

### 2.3 Law-licensed rewrites

These intentionally change source evaluation shape and therefore require an explicit source-level license:

- reassociation;
- reduction tree changes;
- reduction unrolling with independent accumulators;
- fusion that changes grouping;
- transformations whose validity depends on an operator law.

For these, the path is:

```text
original Oak
    |
    |  source theorem / declared law
    v
licensed rewritten Oak
    |
    |  native checker + semantic verifier
    v
assembly
```

Integer associative operators can use this path. Floating-point operators do not gain reassociation merely because the target can execute it faster; Oak's strict floating semantics remain unchanged unless the source explicitly selects different semantics.

## 3. Candidate plans, not destructive decisions

Every optimization scope should expose alternatives.

A loop might have:

```text
LoopPlan
  |- scalar identity
  |- scalar rotated
  |- scalar unroll2
  |- scalar unroll4
  |- vector2
  |- vector2 + unroll2
  `- target-specialized vector form
```

A call might have:

```text
CallPlan
  |- ordinary call
  |- specialize arguments
  |- inline
  `- specialize + inline
```

An expression might have:

```text
ExpressionPlan
  |- original
  |- canonical scalar form
  |- strength-reduced form
  |- fused addressing form
  `- target idiom
```

A machine region might have multiple schedules or allocation plans.

The planner does not need to materialize a complete copy of the function for every alternative. Plans can share immutable nodes or refer to edits over a common representation. Only the selected plan needs to be materialized and validated.

## 4. Transform contract

A transform should be small enough to understand and test independently. Conceptually:

```text
Transform {
    name
    scope

    match(region)
    requirements(region, semanticFacts)
    propose(region, target) -> Candidate[]

    estimate(candidate, targetCosts)
    proofKind
}
```

A requirement should name semantic facts, not rediscover them ad hoc. Examples:

```text
ReductionUnroll4
  requires:
    associative(operator)
    independent element reads
    recognized induction shape

PairLoads
  requires:
    consecutive accesses
    same memory region
    extent covers both accesses
    target has profitable pair form

HoistLoad
  requires:
    load region not modified in loop
    load has no observable effect

VectorizeMap
  requires:
    pure loop body
    non-overlapping input/output regions
    sufficient extent
    target vector support
```

Oak's checked semantic model already has authoritative homes for ownership/authority, effects, representation information, and structured propositions. Optimization should consume those facts rather than rebuild weaker aliases of them.

## 5. Stable-reference validation

The correctness basis should not be a chain of optimizer-to-optimizer equivalences:

```text
A -> B -> C -> D
```

where correctness depends on every intermediate representation remaining trustworthy.

Prefer a stable reference:

```text
                 candidate B
               /
original Oak -- candidate C
               \
                 candidate D
```

The selected machine candidate is ultimately compared with the semantic body the verifier is responsible for. Intermediate plans are construction history, not the semantic authority.

For a law-licensed source rewrite, the rewritten body becomes the stable reference only after the source theorem establishes its equivalence to the original body.

This keeps the number of semantic boundaries small even when the optimizer grows to hundreds of transforms.

## 6. Candidate search must be bounded

Independent transforms compose, so exhaustive search is impossible. Five binary choices already make 32 combinations; a mature optimizer will have far more.

Oak should use bounded search rather than a global hand-written decision tree.

A first implementation can use beam search:

```text
start with identity
    |
apply transforms legal in this scope
    |
produce candidates
    |
cheap structural costing
    |
keep best K
    |
continue with the next planning phase
```

`K` can be small. A budget of 4-8 candidates per region is enough to begin measuring whether search produces value over single-choice heuristics.

Search should also be phased so the compiler does not explore arbitrary permutations:

```text
canonicalization
    -> scalar planning
    -> loop planning
    -> vector planning
    -> machine selection
    -> allocation / scheduling
```

A transform registry can declare the phases in which it participates and the facts it may consume or produce.

## 7. Equality saturation for pure scalar regions

Pure expression regions are a good fit for equality saturation rather than ordered rewrites.

Instead of permanently choosing:

```text
a * 8 -> a << 3
```

the optimizer can retain known-equivalent forms:

```text
a * 8
  == a << 3
  == a + a + a + a + a + a + a + a
```

and extract the cheapest representation for the target.

An initial e-graph or equivalent equality-set engine should be deliberately narrow:

- integer arithmetic identities;
- constant folding;
- bitwise identities;
- shifts and masks;
- comparison simplification;
- boolean algebra;
- extension/truncation folding;
- select simplification;
- pure address arithmetic.

Do not begin with whole-program equality saturation. Loops, memory effects, calls, and control flow should use explicit planning structures until the benefit of a more general representation is demonstrated.

## 8. Cost is not correctness

The cost model chooses among candidates but is outside the trusted base. A bad estimate can make code slower; it cannot change the program's meaning if validation is sound.

The first target-cost interface should expose enough structure for the current AArch64 and RV64 work:

```text
TargetCosts {
    arithmetic(op, width)
    division(width)
    branch(kind)
    call(signature)

    load(width, alignment)
    store(width, alignment)
    pairLoad(width)
    vectorOp(op, laneType, lanes)
    reduction(op, laneType, lanes)

    spill(registerClass)
    reload(registerClass)

    latency(instructionClass)
    throughput(instructionClass)
}
```

Initial costs may be static heuristics. Later they can be calibrated from microbenchmarks and processor descriptions. The planner should record both the chosen candidate and the reason the cost model preferred it.

## 9. Optimization remarks are part of the architecture

A candidate-search optimizer needs first-class observability.

Add an optimization-report mode that can explain passed, missed, and analyzed opportunities:

```text
utf8.valid_with:
  passed  bounds        removed 8 checks
  missed  inline        check_block
                         vector pressure 37 > available 32
  missed  vectorize     loop at utf8.oak:84
                         verifier cannot yet couple lane reduction
  analysis regalloc     27 vector live ranges, 6 spills
```

For hot regions also report structural metrics:

```text
instructions:       83 -> 57
branches/iteration: 3 -> 1
loads/iteration:    8 -> 4
spill stores:       18 -> 0
max live GPRs:      14
max live vectors:   29
estimated cycles:   17.4 -> 9.1
```

An optimization that cannot explain why it was selected or rejected will be hard to tune once candidate search grows.

## 10. Intermediate representations

The candidate architecture does not require Oak to clone LLVM IR, but the native backend now needs a separation between semantic facts, optimization plans, and target allocation.

A practical shape is:

```text
Oak source
    |
    v
SemIR
  types / representation / authority / effects / propositions
    |
    v
OptIR
  typed SSA-like values
  explicit CFG and loops
  explicit memory regions
  range / extent / alias / alignment facts
    |
    v
MachineIR
  target operations
  virtual registers
  register classes
  flags
  memory operands
    |
    v
physical assembly
```

SemIR remains the semantic authority. OptIR is a compiler representation intended to make analyses and candidate planning reusable. MachineIR exists so register assignment and scheduling are no longer entangled with expression lowering.

### 10.1 MachineIR first

The highest-leverage immediate backend change is virtual registers and a global allocator, especially for vector values that cross calls. The UTF-8 benchmark already showed that source-level flattening without vector liveness can make code worse because a large flattened body spills its vector locals.

MachineIR should eventually support:

- unlimited virtual GPR and vector registers before allocation;
- register classes;
- call clobbers;
- live intervals;
- live-range splitting;
- copy coalescing;
- rematerialization;
- spill costs weighted by loop depth;
- ABI constraints;
- pair or fixed-register constraints required by instructions.

### 10.2 Canonical loops and recurrence analysis

Loops should be normalized to a reusable form with a preheader, header, latch, dedicated exits, and explicit values leaving the loop.

On that representation, build a small recurrence analysis analogous in purpose to LLVM ScalarEvolution, but scoped to Oak's needs:

```text
constant
unknown
{start,+,step}
add
mul-by-constant
known range
extensions / truncations
```

This is enough to recognize induction variables, trip counts, pointer induction, loop-invariant expressions, strength reduction, and many redundant guards without a new pattern recognizer per optimization.

### 10.3 Region-aware memory SSA

Do not flatten Oak's ownership information into one anonymous memory state.

The borrow checker and effect system often know that two live spans cannot overlap or that a function only reads one region. Preserve that identity in the optimizer.

Conceptually:

```text
A0 --load--> A0
B0 --store--> B1
```

rather than treating the store to `B` as a possible clobber of `A` and asking a later alias analysis to recover independence.

The first explicit-metadata region MemorySSA has landed. It represents each
declared region independently with deterministic entry, definition, join, and
loop versions; exact Mod/Ref must agree with the operation effects, while an
opaque call clobbers every declared region. An exact direct internal call may
instead carry positive Mod/Ref authority derived recursively from checked
OptIR projections. An empty set is `NoModRef`; a nonempty set lists exact typed
nonvolatile scalar-global `Ref`, `Mod`, or `ModRef` may-effects. Write-bearing
entries are partial definitions, never definite whole-region replacements,
because a callee may execute an assignment conditionally. Every child call has
the same evidence, and the summary fingerprint binds the exact callee CFG,
sorted child summaries, and canonical effect set. Foreign, bodyless, and
recursive graphs fail closed; absence of authority never implies an effect.
Production does not rely on those sealed records alone. One fail-closed
CFG-order projection resolves every active operation against separate
authority and supplies the same accepted records to summary construction and
the proof trace. A standalone OptIR checker then consumes a closed certificate
graph: the exact final optimized root
and the original checked CFG/authority for every reachable callee. It
reprojects every node, requires exact non-root authority coverage, recursively
recomputes the canonical Mod/Ref joins, and rejects cycles, missing, duplicate,
unreachable, stale, or under-approximated nodes. The root may keep unused
upper-bound records after a verified rewrite. A versioned length-delimited
fingerprint also binds a deterministic child-before-parent proof trace. A small
consumer checks that trace without reading CFGs or hashes: every child must
already be accepted with the exact claimed access set, every typed region effect
is joined exactly, names are unique, the root is final, and every non-root is
referenced. `Oak.OptIRMemoryAuthorityProjection` proves the preceding
structural operation/authority model has exact active membership, exact-mode
coverage, and composes with the exact summary fold.
`Oak.OptIRCallSummaryCertificate` proves the trace model over well-formed
projected accesses sound for exact reachable read/write bits, closure, and
topological acyclicity; bounded production decisions at both seams are pinned
to executable Lean examples. Concrete CFG/validator refinement and universal
Go-to-Lean correspondence remain open. The graph
fingerprint binds the whole accepted graph, and AArch64/RV64 production
region-memory selection requires and reruns that certificate exactly when an
active final call summary is interpreted by MemorySSA. A call-only `NoModRef`
CFG consumes no memory-summary fact and stays on the ordinary call path. The
certificate participates in candidate and materialization identity. It checks
the internal consistency of compiler-supplied checked projections rather than
independently re-lowering Oak or identifying the actual machine callee;
semantic translation validation remains the final independent source/body
gate.
Exact CFG and metadata fingerprints plus independent recomputation reject
stale or mutated evidence. Memory-definition liveness now takes an explicit
set of regions observable on normal return,
roots reads, volatile accesses, opaque clobbers, and those terminal versions,
and propagates through join/loop phis. Partial writes keep their predecessors
live. A verified transform deletes only a dead, whole-region, nonvolatile
`store.region`, rewrites its metadata, and rebuilds MemorySSA. A verified
load-forwarding transform then removes canonical nonvolatile region loads only
when their exact MemorySSA input identifies the same typed value from a
dominating load or whole-region store. A closed join or loop memory phi is
promoted when each real predecessor already has the exact typed value, either
from the direct whole-region nonvolatile store defining its incoming version or
from a canonical load of that version dominating the predecessor terminator.
Exactly one unavailable entry-memory input may instead be materialized on its
real incoming edge. An unconditional predecessor receives the load directly.
If exactly one conditional arm targets the phi, a new block receives only that
arm and branches onward with the arm's existing SSA arguments plus the loaded
value. The transform moves the removed canonical load's checked source/access
identity into the edge block; it does not synthesize authority or execute the
load on another arm. A fresh typed parameter in the phi block receives the edge
values, and loads in the phi block and dominated blocks can share it.
Conceptual function-entry inputs, ambiguous two-arm edges, multiple missing
inputs, partial/call definitions, type mismatches, missing edges, and value- or
block-ID exhaustion fail closed. The evidence records the original predecessor,
the insertion site, and whether the edge was split as well as removed-load
replacements. Values from loads removed later in the same transform are
resolved before edge materialization. The transform drops facts bound to
removed SSA identities, remaps every use and operation site, and rebuilds
MemorySSA. A composed regression then reprojects the checked authority and
requires both AArch64 and RV64 lowering of the split CFG to pass seam admission
with a proven semantic verdict. Multiple region phis now share the same split
block for an exact original predecessor/target pair. Every promoted input
follows that final edge, including an already-available value from a phi
planned before another region requested the split. Distinct targets stay
separate. Regressions remove both join loads and prove the resulting two-region
CFGs on AArch64 and RV64, including mixtures of moved and available inputs;
the one-missing-input limit remains per region phi. Checked Oak
Bool/fixed-integer package-global reads and whole-cell assignments now project
into it. Metadata first follows the exact structured operation identity into a
CFG site. Each projected operation then carries only an opaque access ID; a
separate immutable authority fixes its exact source, region, kind, scalar type,
whole-region contract, and volatility. The two projections must agree.
Projection rejects missing, duplicated, stale, forged, or mismatched authority
and treats every global region as live on normal return. The typed artifact DAG
runs projection, MemorySSA, liveness, combined evidence, DSE, and load
forwarding after LICM; both transforms independently verify their complete
rewrites before publishing them. One subsequent `optir.memory-cleanup` node
runs SCCP and phi/GVN/DCE cleanup to consume newly exposed scalar facts,
then recomputes checked memory projection, MemorySSA, and liveness to remove
stores made dead by forwarding or branch pruning. The existing closed DSE
transform independently verifies its rewrite; pure DCE removes unused
store-value producers while retaining effectful calls. One final pure LICM
pass consumes freshly analyzed loops for that exact DCE snapshot, allowing
scalar arithmetic exposed as invariant by memory promotion and phi cleanup
to leave the loop. It retains the existing total-pure vocabulary and does not
move memory or trapping operations. This is a bounded composition within the
same artifact, not additional global graph plumbing.
Checked access projection and MemorySSA are rebuilt for `MemoryCleanup.CFG`,
and native selection independently replays the cleanup before deriving final
bindings, active call certificates, and materialization identity. The source
global declarations needed to verify removed paths survive as arbitrary
entry-state declarations, without added machine accesses. Constant branches,
removed calls, wrapping arithmetic, and the final source-state comparison are
covered by proven AArch64/RV64 candidates and host/QEMU execution. There is no
unbounded iteration between memory and scalar passes.
Changed final CFGs can enter native search on
AArch64 and RV64 when the memory vocabulary is acyclic control flow over exact
scalar package-global reads and whole nonvolatile writes, optionally composed
with authenticated exact `NoModRef`/`Ref`/`Mod`/`ModRef` scalar calls. A `Ref`
call creates reads with no output version, so DSE retains the definitions the
callee may observe while load forwarding can cross it. `Mod` and `ModRef`
create partial output versions, retain their predecessors conservatively, and
block forwarding across the call. Selection retains callee-only globals
without emitting caller memory operations for the summary. Both targets also
admit one exact call-free canonical natural loop with a unique preheader,
conditional header, straight-line body/latch, backedge, and return exit. Its
RegionMemorySSA contains the loop-header phi joining the entry memory version
with the exact body-store definition. Selection independently rechecks that
evidence, `asm.Check` admits each selected body, and `asm.Verify` proves it
against the corresponding Oak loop, including its package-global write.
RV64's verifier requires exact `la`-derived scalar-global address provenance;
direct positive and negative tests prove the correct loop and refute an
incorrect store, removing the previous trusted boundary for package-global
loop-carried state. The production loop fixture has no synthetic source-level
preheader read: the transform moves one authenticated load to the unconditional
preheader edge, promotes the MemorySSA phi, and removes the body and exit
loads. When
the promoted value has both a result-register carrier and a global-cell
carrier, the verifier admits the extra global alias only after bounded proofs
of header equality and one-step preservation; a divergent global store is not
proven. Arbitrary and nested memory loops remain refused. Selection
reprojects immutable checked source-access authority over the exact final CFG,
independently verifies rebuilt MemorySSA, and matches every opaque region
through typechecker authority to an exact global descriptor already authorized
by the assembler template. Width- and signedness-correct code covers Bool and
8/16/32/64-bit integers. Authority and final-projection fingerprints are part
of materialization identity. Existing verified register plans and typed aligned
spill frames compose with global accesses using disjoint reserved scratches on
both targets; seam admission and semantic translation validation still decide
whether the body may ship. Aggregate/partial regions, broader memory loops,
multiple unavailable phi inputs, broader load placement, conceptual-entry loop
phis, partial/call-written versions, definite-write summaries, and calls in
memory loops remain open;
exact recursive
`NoModRef`/`Ref`/`Mod`/`ModRef` may-effect summaries, their standalone graph
checker, and composed Lean structural models of active-authority projection
and the small postorder effect core have landed. Concrete CFG/validator
refinement and universal implementation correspondence remain TCB-closure
work.

As the projection broadens, region memory SSA should power:

- multiple-missing-input and broader load placement;
- dead-store elimination;
- LICM;
- safe memory reordering;
- call Mod/Ref summaries;
- loop memory promotion.

This is one of the places Oak should be structurally simpler and more precise than a C-derived optimizer.

## 11. Initial transform library

The existing native optimizations should be migrated into the candidate interface before adding a large new catalog. They are good tests because their semantics and benchmark effects are already understood.

### Scalar / expression

- constant arithmetic folding;
- strength reduction;
- redundant mask removal;
- condition selection;
- compare-immediate selection;
- compare reuse;
- select simplification.

### Memory

- guard elimination from proven extents;
- byte-assembly to wide-load fusion;
- pair loads;
- vector block loads — **landed 2026-09-16** (`vector-blocks`,
  `nativegen/vector_blocks.go`): the vector loads of one basic block read
  off a single element address at immediate offsets, so the vectorized
  reduction's `u32` main loop is eleven instructions for sixteen elements
  where it was eighteen. The checker and the verifier already admitted
  the form, so it is a machine peephole only. Measured neutral on a
  bandwidth-bound 4 MiB stream and about eight percent on an L1-resident
  array — the instruction count is what it buys, and a core with less
  spare issue than an M4 is where that would tell;
- scalar-array element promotion;
- constant-offset addressing forms.

### Control flow

- if-conversion;
- conditional increment/select forms;
- branch chaining;
- jump threading where effects permit;
- loop rotation / bottom testing.

### Loops

- reduction unroll2/unroll4;
- address induction;
- invariant hoisting;
- integer vector reduction;
- map/zip vectorization.

### Calls

- source inlining;
- argument specialization;
- constant specialization;
- extent/alignment specialization.

### Machine

- addressing-mode selection;
- multiply-add forms — **landed 2026-09-16** (`multiply-add`,
  `nativegen/multiply_add.go`): `a + b * c` as `madd`, `a - b * c` as
  `msub`, `T(0) - b * c` as `mneg`, the verifier needing no extension.
  Integers only — `fmla` is one rounding where Oak's expression is two
  (`-ffp-contract=off`) — and a constant operand is left to the strength
  reduction's shift. Measured neutral on an integer dot product
  (seven instructions an element become six, 0.39–0.46 ns either way): the third increment in a row
  whose instruction saving an M4's spare issue slots absorb, which is
  itself worth recording — the static cost model counts instructions,
  and on this core that is not what the clock counts. A port-pressure or
  dependency-chain term (item 26) is what would tell these apart;
- select forms — **landed 2026-09-16** (`value-select`,
  `nativegen/value_select.go`): a value-position conditional as a compare
  and one `csel`, with `csinc`/`csneg`/`csinv` where the arms share a
  variable, the verifier needing no extension. The first increment in
  this run with a large measured win: 3.4 times on a clamp whose
  comparison is unpredictable, and free where it predicts. Both arms are
  evaluated before the compare, so `speculable` gates it as it gates
  if-conversion. The statement form (`nativegen/select.go`) already groups
  a chain's conditions, sharing a compare between consecutive arms that
  compare the same two operands; its real limit was that only the first
  arm's condition operand could be computed, **widened 2026-09-16**: a
  later arm's is evaluated before the chain when it is speculable, so a
  two-comparison chain converts whole instead of branching on its first
  arm and re-recognizing the rest. 1.8 times on an unpredictable
  three-arm chain in a loop. What is left there is the assignment cap —
  `maxSelectAssigns` is 4, so a chain assigning two variables across
  three arms still splits — which is a register-pressure question, not a
  recognition one;
- scheduling alternatives;
- allocation alternatives;
- late copy/branch cleanup (landed 2026-09-16: `late-cleanup`, 2.2 percent
  of the kernel package's instructions, verdicts unchanged).

## 12. Vector planning

Vectorization should be a plan search, not a single yes/no transform.

For a reduction the planner might consider:

```text
VF=1 UF=1    scalar identity
VF=1 UF=2    scalar unroll2
VF=1 UF=4    scalar unroll4
VF=2 UF=1    fixed-width vector
VF=2 UF=2    vector + interleave
scalable     SVE/RVV where target permits
```

Legality and profitability should be separate. Oak's ownership, extents, alignment, and operator-law facts decide what is legal; the target cost model decides which legal plan is worthwhile.

The current verified `u64` reduction is the prototype: the compiler already has a law-licensed four-accumulator rewrite and pair loads. A vector form of that same plan is the next natural candidate rather than a separate special-purpose compiler path.

After reductions, add pure map/zip loops, then straight-line SLP-like packing for crypto, codecs, fixed arrays, and explicit multi-accumulator code.

## 13. Inlining is a candidate after allocation exists

Inlining should not be driven by function size alone.

Its score should include:

```text
call overhead
+ constants and refinements exposed in caller
+ bounds/guard eliminations enabled
+ specialization opportunities
- code growth
- estimated register pressure
- spill cost
```

Oak has an important extra term that generic inliners often only approximate: inlining can expose already-proved extent, alignment, ownership, and effect facts that make a callee substantially cheaper.

The allocator must come first. The UTF-8 experiment showed that flattening a call tree before competent vector register allocation can increase spills and lose performance.

## 14. Optimization levels become search budgets

Optimization levels should not imply different language semantics. They can primarily control search effort:

```text
-O0   identity / minimal planning
-O1   cheap local candidates
-O2   normal bounded search
-O3   larger candidate and costing budget
```

All levels preserve Oak semantics. A verified build additionally requires the selected native body to meet the verified profile's verdict requirements.

Over time a high-effort mode can try more schedules, allocations, vector widths, or inlining combinations without introducing a second correctness regime.

## 15. Verification and candidate ordering

Validation can be expensive, so do not fully prove every candidate before costing it.

A practical order is:

```text
1. generate legal-looking candidates from semantic requirements
2. reject structurally invalid candidates cheaply
3. estimate cost
4. keep the best small set
5. run checker/verifier on candidates in cost order
6. take the cheapest candidate that proves
7. fall back to identity if none does
```

Where a transform depends on a source theorem, establish that theorem/license before machine candidate validation.

Step 5 spends the validation budget one *shape* at a time (2026-09-16,
`opt/search.go`): a candidate's shape is its transforms without the
verifier-gated ones (`reallocate`, `schedule`), which move and rename but
change nothing the verifier reads. Once a shape has been validated without
a proof, the next validation goes to the cheapest candidate of a shape not
yet judged, and only when every shape has been judged does the budget
return to cost order. The case that forced it: the vectorized map's three
cheapest forms were one hoisted shape under different gated transforms,
each witnessed on the same remainder-loop obligation, and the plain
vectorized shape, which proves, never got a validation.

The optimizer should cache verdicts using the same dependency-aware mechanism already used for native verdicts so candidate search does not make incremental builds re-prove unchanged implementations.

## 16. Roadmap

The roadmap is dependency-driven rather than a list of isolated peepholes.

### Phase A: planning substrate

1. candidate/plan abstraction;
2. transform registry;
3. semantic-requirements API;
4. target-cost API;
5. optimization remarks and structural metrics;
6. bounded candidate pruning / beam search;
7. migrate current transforms into the registry and the landed immutable,
   selectively invalidated, bounded-parallel artifact-DAG executor.

### Phase B: machine substrate

8. MachineIR with virtual registers;
9. global scalar and vector liveness;
10. register allocation with splitting/spilling (**deterministic abstract spill
    plan, verifier-gated AArch64 scalar insertion, and the first closed RV64
    loop-carried insertion landed; RV64 acyclic constant rematerialization also
    landed; splitting, broader MachineIR/RV64 loops, copy-chain
    rematerialization, and RV64 splitting remain**);
11. call-aware vector allocation;
12. late copy and branch cleanup (**target-independent loop-biased block layout
    and AArch64/RV64 fallthrough cleanup landed; edge-copy cleanup remains**);
13. simple pre/post-allocation scheduling.

This phase targets the measured UTF-8 call/spill gap directly.

### Phase C: middle-end substrate

14. OptIR CFG/SSA-like values;
15. dominators and canonical loops;
16. explicit loop outputs;
17. recurrence/trip-count analysis;
18. region-aware memory SSA / Mod-Ref summaries (**explicit analysis substrate,
    checked scalar-global projection, and one verifier-proved canonical memory
    loop on both targets landed; exact recursive
    `NoModRef`/`Ref`/`Mod`/`ModRef` call summaries plus a standalone closed-DAG
    certificate checker and composed Lean structural models of active-authority
    projection and its small postorder effect core also landed, while concrete
    CFG/validator refinement, universal implementation correspondence, broader
    loops, aggregate regions, and definite-write summaries remain**);
19. worklist scalar canonicalizer;
20. SCCP/CSE/GVN/DCE/DSE;
21. LICM (**verifier-gated AArch64/RV64 OptIR candidate landed**), loop rotation, address
    induction, loop strength reduction.

### Phase D: vector planning

22. vector-plan representation;
23. fixed-width integer reduction vectorization — **landed 2026-09-16**
    (`vectorize-reductions`, `nativegen/vector_reduction.go`): four
    vector accumulators, sixteen elements an iteration over `simd.U32x4`
    lanes and eight over `simd.U64x2`, licensed by
    `Oak.Reduction.vector16_eq` and `vector8_eq`, proven by the verifier,
    2.6× the scalar unrolling on `u32` and 1.4× on `u64`. Three findings
    came out of it, all in `benchmarks/native/README.md`: one vector
    accumulator is *slower* than four scalar ones, so the plan table's
    UF matters more than its VF; the combine belongs in the vector
    domain, since storing every accumulator into a wider frame array is
    witnessed where folding them pairwise first is proven; and the cost
    model's assumed trip count had to be calibrated before it agreed
    with any of it (item 26 below);
24. map/zip vectorization — **landed 2026-09-16** (`vectorize-maps`,
    `nativegen/vector_map.go`, `spec/lean/Oak/Map.lean`): an element-wise
    map or zip over span parameters — `dst[i] = E(a[i], b[i], …)` with `E`
    over the elements at `i`, invariant scalars, and constants under
    `+ - & | ^` for `u8`/`u16`/`u32`/`u64` lanes and `+ - * /` for
    `f32`/`f64` lanes,
    in place or under an enclosing conjunction of `len(x) == len(y)`
    guards (closed transitively) — runs one vector a trip (the `ldr q`s,
    the lane-wise operations, `str q`) under the slack guard with the
    scalar remainder as written, licensed by `Oak.Map.blocked_eq`
    (lane-wise semantics alone: no law of the element type, so no fact of
    the body is required and floats vectorize where a reduction's cannot),
    and proven by the verifier with the span memory it writes. Measured
    over 2^20 elements (`benchmarks/native/README.md`, "Map
    vectorization"): 2.8–3.0× on a `u32` map, 3.2–3.6× in place, 2.6–2.8×
    on an `f32` multiply-add map, 2.2–2.3× on a zip. Two
    verifier increments made it provable: the store-loop split (§0,
    "loops that never ran keep the entry memory") proved the hand-written
    shape that the 2026-09-16 survey found *witnessed*; and the hoisted
    form — a guard peeled around the vector loop skips it when `len(a) <
    4`, carrying the index's header value into the remainder loop where
    the Oak side carries the loop symbol — needed the scalar counterpart,
    "loops that never ran keep their variables" (`notRunPins` in
    `asm/loops.go`: a loop ran, or each of its symbols is its header
    value, in every premise that can read an earlier sibling's symbols).
    Still to do: integer multiplication (no integer `mul` lane in v1) and
    shifts, signed lanes, spans bound in the body (tried 2026-09-16: the
    rewrite is easy, but the seam checker admits no vector access at a
    variable index through a span bound over a frame array — "memory
    operands go through the declared sp frame or a bound span base" — so
    the checker's frame idiom has to learn the element address first),
    and the RV64 lane (2026-09-16: the machine lift now reads the RVV
    instructions the lane emits — a vector register class that keeps its
    assignment, `vsetivli` a barrier, register-form strides `li t0, 4;
    addw t1, t1, t0`, a single induction standing in for an unread exit
    test, the remainder bounded after it — so the vectorized form is
    priced 3822 against the scalar loop's 7451 under `reallocate`; but
    the verifier on that lane does not yet model a vector store in a
    data-dependent loop body ("a span store in a data-dependent loop
    body"), so the form comes back trusted and the proven scalar loop
    keeps winning; the transform stays AArch64 only until the RV64
    verifier takes `vse` in loops), elements at `i ± k`
    (stencils), and more than one vector a trip;
25. SLP-like straight-line packing;
26. vector-aware cost model — **first calibration landed 2026-09-16**:
    `LoopWeight`, the trips a data-dependent loop is assumed to run, was
    32, which charged a sixteen-element main loop's fifteen-trip
    remainder half the work and kept every strided form out of the
    selection. It is 256 now, from the reduction microbenchmark's three
    `u32` rows, which the model then orders as measured (`opt/cost.go`).
    Still static and per class: no lane throughput, no dependency-chain
    term (the finding that sent the rewrite to four accumulators is one
    the model cannot yet express), no port pressure;
27. SVE/RVV scalable plans where semantics and verifier support permit.

### Phase E: interprocedural planning

28. cost-driven inlining;
29. constant/range/extent/alignment specialization;
30. effect-summary propagation;
31. pure-call CSE and dead call/result elimination;
32. call-graph-level candidate planning.

### Phase F: advanced search

33. profile-guided candidate costs and block placement;
34. software pipelining for suitable streaming loops;
35. loop fusion/interchange when legality is explicit;
36. larger equality-saturation regions;
37. measured superoptimization for small hot regions.

Advanced phases should not block the high-value allocator, loop, memory, and vector foundations.

## 17. Landing rule for an optimization feature

A new optimization should land with all of:

1. a named transform or planning rule;
2. explicit semantic requirements;
3. a conservative identity fallback;
4. validation at the correct semantic boundary;
5. an optimization remark for both success and rejection;
6. structural before/after evidence;
7. benchmark evidence on the workload it targets;
8. unchanged or stronger verified-profile verdicts for affected bodies.

An optimization that wins a benchmark by weakening a verdict is not a result.

## 18. Non-goals

This architecture does not license:

- fast-math or floating reassociation not selected by the source;
- speculative undefined-behavior assumptions;
- hidden allocation or runtime machinery;
- target-specific semantic changes;
- unbounded compile-time search;
- trusting an optimizer pass merely because it is well tested.

The optimizer may search aggressively only inside the semantic envelope Oak defines.

## 19. End state

The desired native compiler is not a smaller copy of LLVM. It should exploit facts Oak knows earlier and more precisely:

- ownership gives non-aliasing;
- effects give Mod/Ref and purity;
- extents give bounds and trip-count facts;
- alignment is a checked type fact;
- refinements give ranges;
- operator laws license otherwise-illegal reordering;
- per-body semantic validation lets proposal algorithms remain outside the trusted base.

The long-term shape is:

```text
semantic facts
    |
    v
many legal candidate implementations
    |
    v
bounded target-aware search
    |
    v
cheapest candidate
    |
    v
independent semantic validation
    |
    +-- proven  -> keep
    `-- refused -> next candidate / identity
```

That is the optimizer architecture to preserve as Oak grows: **many discrete transforms, explicit semantic requirements, bounded candidate search, and a small independent proof gate instead of one globally trusted optimization decision.**
