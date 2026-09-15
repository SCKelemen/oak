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

Not in this increment: live-range splitting, vector callee-saved growth
(d8–d15, fs0–fs11), RVV bodies, a lowering that emits virtual registers
directly, scheduling, and exact trip counts against register bounds.

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

Analysis-only SCCP independently validates its operation vocabulary and computes
exact constants plus executable blocks and edges. Integer folding follows Oak's
fixed-width wrapping, signedness, division-overflow, and logical-shift semantics;
it does not rewrite the CFG or authorize emission.

The first generic transformation candidate is also connected. GVN numbers
plain copies alike, canonicalizes exact commutative integer/equality operations
and inverse order comparisons, then shares a congruent expression only from a
dominating definition. DCE removes the exposed unused pure chains and copies to
a fixed point. Both are restricted to a closed vocabulary of total scalar
operations: missing effect metadata never makes calls, traps, memory, or
unknown operations removable, and an unknown attribute disables algebraic
normalization. Proof facts are remapped only where they remain valid. Input and
output pass the independent verifier, and `Compilation.OptIR()` retains the
original CFG beside the simplified candidate and its deterministic report.

OptIR also has its semantic loop analysis: reverse postorder and immediate
dominators; natural loops with back edges, latches, exits, canonical preheaders,
parents, and depths; and typed affine recurrences over explicit loop-carried
block arguments. It normalizes the unique continuation predicate and proves an
exact constant trip count only when a monotone fixed-width recurrence reaches
the exit without wrapping. Symbolic bounds, multiple exits, latch disagreement,
and wrapping boundaries retain only the facts actually established. These
results complement MachineIR's structural loop tree: OptIR owns Oak arithmetic
meaning, while MachineIR owns eventual layout and scheduling.

Its first loop transform is analysis-only LICM. After GVN/DCE it moves a closed
total-pure operation to a canonical preheader only when all operands are
available there. Potential traps, effects, calls, memory, unknown operations,
noncanonical entries, and facts other than the definition-local checked type
fact pin the operation. The cloned result passes the independent verifier and
is retained with deterministic movement evidence; emission consumes neither.

The implementation topology is not yet one end-to-end pass DAG: `Stage.Then`
remains linear, and native candidate proposal enumeration still branches
internally. The generic OptIR chain is migrated. Immutable, exact-version nodes
hold CFG v0, SCCP, loop structure/facts, GVN/DCE, CFG v1, checked preservation,
recomputed induction facts, and LICM. CFGs have canonical content fingerprints.
Analyses declare a closed set of topology, SSA, operation, effect, type, fact,
and layout aspects. GVN/DCE's admission node independently compares per-aspect
digests for v0/v1; because `CFGTopology` is preserved, v1 reuses v0 dominance
and natural loops while recomputing recurrence facts from v1. No certificate is
an equivalence verdict or emission license. Every native proposal has a
canonical checked-input recipe and materializes through candidate → admission
→ metrics → cost artifacts; every attempted semantic check is a verdict
artifact, and selection depends on candidate, clean admission, cost, and
verdict for every possible result. Validation stays sequential to retain the
budget and proof early-stop. The executor runs bounded deterministic ready
waves, and OptIR uses three workers for its independent analysis fan-out. The
complete design is `optimizer-artifact-dag-2026-09.md`.

Not yet: equivalence-validated emission of the candidate, join/loop-parameter
value congruence, region-aware memory SSA and the dead stores it would license,
non-affine and symbolic trip-count proofs,
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

A region-aware memory SSA or equivalent def-use representation should power:

- load CSE;
- store-to-load forwarding;
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
- multiply-add/select forms — **in progress (2026-09-16, the oak session
  at ~/oakmcu/oak)**: `a + b * c` lowers to `mul` then `add` where
  `madd` is one instruction, `a - b * c` to `mul` then `sub` where
  `msub` is one, and `0 - b * c` where `mneg` is one; the verifier
  already models all three. Integers only — `fmla` is one rounding where
  Oak's `a + b * c` is two (`-ffp-contract=off`);
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
10. register allocation with splitting/spilling;
11. call-aware vector allocation;
12. late copy and branch cleanup;
13. simple pre/post-allocation scheduling.

This phase targets the measured UTF-8 call/spill gap directly.

### Phase C: middle-end substrate

14. OptIR CFG/SSA-like values;
15. dominators and canonical loops;
16. explicit loop outputs;
17. recurrence/trip-count analysis;
18. region-aware memory SSA / Mod-Ref summaries;
19. worklist scalar canonicalizer;
20. SCCP/CSE/GVN/DCE/DSE;
21. LICM (**analysis-only OptIR candidate landed**), loop rotation, address
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
24. map/zip vectorization — **surveyed 2026-09-16, blocked on the
    verifier**: a hand-written vector map (`simd.store_u32x4(dst, i,
    simd.add_u32x4(simd.load_u32x4(a, i), kv))` under
    `len(dst) == len(a)` and the slack guard) is admitted by the seam
    checker and modeled by the verifier lane by lane, but comes out
    *witnessed*: "the memory of the span dst after the loops was not
    proven equal". The scalar map is proven with its span memory, so
    what is missing is coupling a span's memory across two loops — the
    vector main loop and the scalar remainder. Two notes for whoever
    takes it: an index guarded against two spans keeps only the last
    bound, so the equal-length shape (`len(dst) == len(a)`) is the one
    the checker admits; and a map needs no reassociation at all, so the
    law is far weaker than the reduction's and floats vectorize too;
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
