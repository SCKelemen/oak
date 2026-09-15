# Candidate-search optimization for Oak

Status: design note, September 2026.

This note proposes the architecture for Oak's optimizing native backend after the first verified optimization increments in `nativegen/`: strength reduction, condition selection and if-conversion, aggregate promotion, wide-load fusion, reduction unrolling, and pair loads. It complements `docs/notes/optimization-2026-09.md`, `docs/notes/native-optimization-2026-09.md`, `docs/spec/90-backend.md` §16, and the semantic verifier in `docs/spec/94-assembler.md` §9.

Two companion catalogs feed this architecture:

- `docs/notes/llvm-optimization-catalog-2026-09.md` records conventional compiler analyses, transforms, vectorization, IPO, register allocation, scheduling, and target-cost patterns worth adapting from LLVM;
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
- `nativegen/opt.go` — the native lane's side: the five transforms the
  lane already performed (`strength-reduce`, `elide-guards`,
  `reuse-flags`, `hoist-invariants`, `unroll-reductions`), then
  `vector-homes` and the first transform written for the registry,
  `late-cleanup` (§11 "Machine", late copy/branch cleanup:
  `nativegen/cleanup.go`, a block-local peephole under a whole-function
  register liveness, 2026-09-16), as
  `opt.Transform`s over `Lane` configurations, each with its phase,
  proof kind, and requirements; `FunctionFacts` reading the
  typechecker's proved indices and the language's integer associativity
  laws into facts; `Metrics` over a lowered body (instruction classes,
  guards, and per loop the counts, the stride read off the index
  register's increment, and the trip bound of a remainder loop after a
  strided one); `Registry`, `PlainLane`, `FindingLine`.
- The cost model (`opt.TargetCosts`) is static and per class: straight-line
  code at weight one, each loop body at `LoopWeight` trips divided by its
  stride and bounded by its shape's trips, so a four-way unrolled
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

Not in this increment: spilling and live-range splitting (the pool never
grows the frame), a lowering that emits virtual registers directly,
scheduling, and the RV64 lane.

Not yet: OptIR and the analyses (Phase C), OptIR and the analyses
(Phase C), vector plans (Phase D), and the proof-obligation service of
the proof-guided note §26 beyond the requirement/fact matching here.

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
- multiply-add/select forms;
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
7. migrate current transforms into the registry.

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
21. LICM, loop rotation, address induction, loop strength reduction.

### Phase D: vector planning

22. vector-plan representation;
23. fixed-width integer reduction vectorization;
24. map/zip vectorization;
25. SLP-like straight-line packing;
26. vector-aware cost model;
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