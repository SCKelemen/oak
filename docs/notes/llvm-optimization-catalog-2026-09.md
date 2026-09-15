# LLVM-derived optimization catalog for Oak

Status: research/design note, September 2026.

This is the exhaustive companion to `docs/notes/optimizer-search-2026-09.md`. The architecture note says how Oak should organize optimization: discrete transforms propose candidates, semantic facts define legality, a target cost model ranks candidates, and independent validation decides whether a candidate may enter verified output. This catalog records the LLVM ideas surveyed while designing that system: the reusable analyses, canonical forms, transformation families, machine-code patterns, planning techniques, and diagnostics worth adapting to Oak.

It is deliberately not a prescription to reproduce LLVM. Some LLVM machinery exists because C/C++ and LLVM IR have weak aliasing, lifetime, and semantic information; Oak often knows those facts directly from borrowing, effects, extents, refinements, representations, and operator laws. The goal is to copy the durable architectural lessons and optimization techniques while replacing inference with Oak's stronger checked facts where possible.

The standing principle is:

> **Copy the optimization idea, not the accidental constraints of LLVM's source languages or IR.**

## 1. The large architectural lessons

### 1.1 Separate semantic IR, optimization IR, and machine IR

LLVM's optimizer and code generator become manageable because different representations answer different questions. Oak should keep the same separation while retaining SemIR as the semantic authority:

```text
Oak source
    |
    v
SemIR
  type / representation / authority / effects / propositions
    |
    v
OptIR
  SSA-like values / CFG / loops / regions / facts
    |
    v
MachineIR
  generic or target operations / virtual registers / register banks
    |
    v
physical assembly
```

SemIR remains the source of truth. OptIR exists to make reusable analyses and candidate planning cheap. MachineIR exists so instruction selection, register allocation, scheduling, and late machine optimization are no longer entangled with AST lowering.

Do not put target register choices into OptIR and do not put language semantics into MachineIR.

### 1.2 Canonical forms before sophisticated transforms

LLVM repeatedly simplifies the problem before optimizing it. Loop Simplify gives a loop a preheader, one latch/backedge, and dedicated exits; LCSSA makes loop outputs explicit. SSA construction turns mutable locals into def-use chains. InstCombine/SimplifyCFG continuously restore canonical forms after other transforms.

Oak should adopt the same doctrine:

```text
canonicalize -> analyze -> transform -> canonicalize again
```

Canonical forms are infrastructure, not optional cleanup. A new optimization should consume a small number of stable forms rather than inventing its own pattern language over arbitrary source shapes.

### 1.3 Analyses are reusable products, not private pass helpers

LLVM transformations share dominators, loop structure, recurrence facts, alias/ModRef information, MemorySSA, branch probabilities, target costs, liveness, and call-graph information. The pass manager caches analyses and invalidates only what a transformation actually destroys.

Oak should have analysis objects with explicit dependency and preservation contracts. A transform should say which analyses it reads and which remain valid after the candidate is materialized.

Examples:

```text
Dominators
PostDominators
LoopInfo
LoopForest
RecurrenceInfo
RangeFacts
KnownBits
RegionAlias
RegionMemorySSA
CallEffects
BlockFrequency
Liveness
LiveIntervals
TargetCosts
```

Avoid having strength reduction, vectorization, LICM, and bounds elimination each rediscover the same induction or extent fact independently.

### 1.4 Separate legality, profitability, planning, and execution

LLVM's VPlan makes the distinction explicit:

```text
legal?
  -> construct candidate plans
  -> cost / optimize / prune plans
  -> choose
  -> execute only the chosen plan
```

Oak should generalize this beyond vectorization.

Legality comes from Oak semantics and checked facts. Profitability comes from a cost model. Candidate construction is untrusted search. Execution materializes the chosen plan. Verification is a separate final gate.

### 1.5 Target cost information is a first-class service

LLVM has target cost interfaces because an optimization that is profitable on one processor may regress another. Oak needs the same idea for AArch64, RV64, NEON, SVE, RVV, and future lanes.

Cost is never correctness. A poor estimate is a performance bug, not a semantic bug.

### 1.6 Diagnostics are part of an optimizer, not an afterthought

LLVM's optimization remarks distinguish `Passed`, `Missed`, and `Analysis`. That is worth copying almost directly.

Every Oak transform should be able to explain:

- why it matched;
- which semantic requirement was missing;
- which candidate was chosen;
- why another candidate lost;
- whether verification rejected a candidate;
- structural before/after metrics.

### 1.7 Fallback is a feature

LLVM GlobalISel historically used fallback paths while gaining coverage. Oak has a stronger version: identity/conservative lowering is always a legal candidate, and a candidate that cannot be proved can be skipped without trusting the optimization.

A failed optimization should be:

```text
candidate refused -> try next candidate -> identity
```

not:

```text
compiler correctness now depends on the pass having been right
```

## 2. Pass scopes and optimizer organization

LLVM organizes work at several scopes. Oak should do the same so transforms can be local and composable.

Suggested scopes:

```text
Module / package
Call-graph SCC
Function
Loop nest
Loop
Basic block / control region
Pure expression region
Memory region
Machine function
Machine block
Machine scheduling region
```

A transform declares its scope. A function pass should not secretly require module-global rewriting; a loop transform should not need to rediscover the call graph.

The analysis manager should cache per-scope analyses and invalidate them selectively after a chosen candidate is materialized.

## 3. Core control-flow and SSA analyses

These are prerequisites for a maintainable middle end.

### 3.1 Dominator tree

Needed by:

- SSA construction;
- guard/fact dominance;
- LICM;
- GVN/CSE;
- loop recognition;
- safe sinking/hoisting;
- branch simplification;
- bounds-fact availability.

Oak already reasons about dominating guard facts in the assembler checker; OptIR should have the same concept explicitly.

### 3.2 Post-dominator tree

Useful for:

- control dependence;
- sinking;
- if-conversion legality;
- dead control-flow removal;
- loop exits;
- tail merging.

### 3.3 SSA and PHI-like values

Use SSA-like values for compiler temporaries and scalar locals so def-use chains are explicit. Mutable source state can lower into SSA without changing source semantics.

Benefits:

- cheap CSE;
- easy constant propagation;
- clear liveness;
- simple DCE;
- explicit merge points;
- easier vector planning.

### 3.4 LoopInfo / loop forest

Recognize natural loops once, retain nesting information, and expose headers, latches, preheaders, exits, parents, children, and depth.

Loop depth should feed spill costs and block frequency estimates even before PGO exists.

### 3.5 Loop Simplify form

Normalize optimizable loops to:

- one preheader;
- one latch/backedge;
- dedicated exits.

This directly simplifies LICM, unswitching, vectorization, unrolling, recurrence reasoning, and scheduling.

### 3.6 Loop-closed SSA

Values defined in a loop and used outside should have explicit exit values. This prevents every loop transform from needing special cases for arbitrary escaping definitions.

## 4. Scalar recurrence and value analyses

### 4.1 Oak ScalarEvolution-like recurrence analysis

LLVM ScalarEvolution is one of its highest-leverage analyses. Oak should build a deliberately smaller version first.

Initial expression language:

```text
constant
unknown
{start,+,step}
add
sub
mul-by-constant
min/max bound
zext / sext / trunc
```

Questions it should answer:

- is this an induction variable?;
- what is its start and step?;
- what is the loop trip count or bound?;
- is this expression loop invariant?;
- what is the address recurrence?;
- can multiplication be replaced by induction?;
- can two induction expressions be compared statically?;
- is an access within a known extent for every iteration?;
- can a loop guard be represented as slack from an extent?;

This analysis should consume Oak's checked range/extent propositions instead of reconstructing all facts from instructions.

### 4.2 Known bits

LLVM uses known-zero/known-one information widely in simplification and selection. Oak should expose a reusable known-bits lattice for integer values.

Applications:

- redundant masks;
- shift simplification;
- narrowing instruction selection;
- compare simplification;
- proving alignment from low zero bits;
- avoiding sign/zero extensions;
- selecting immediate forms.

### 4.3 Integer range analysis

Consume refinements, extents, branch conditions, and arithmetic to maintain ranges.

Applications:

- prove traps impossible;
- eliminate bounds checks;
- choose narrower operations;
- simplify comparisons;
- prove division nonzero;
- prove shift counts legal;
- select cheaper addressing forms.

### 4.4 Constraint propagation

Propagate relational facts, not just intervals:

```text
x < y
y <= len(a)
=> x < len(a)
```

and equalities such as:

```text
len(a) == len(b)
```

This generalizes the checker facts already used to remove guards in `dot`, search, and page-probe shapes.

## 5. Alias, effects, and memory analyses

### 5.1 Do not copy LLVM alias analysis literally

LLVM must often answer `NoAlias / MayAlias / MustAlias` from weak pointer information. Oak should preserve ownership identity and borrow relations before lowering destroys them.

Prefer explicit facts such as:

```text
region(a) != region(b)
unique-write(a)
shared-read(b)
view-of(owner)
subregion(x, owner, offset, len)
aligned(region, N)
```

Then alias queries become a projection from semantic facts rather than a speculative pointer analysis.

### 5.2 Mod/Ref summaries from effects

LLVM infers `readonly`, `readnone`, `nocapture`, and call Mod/Ref properties. Oak should derive stronger summaries from effect rows and authority.

For each function/call, expose:

```text
reads(region set)
writes(region set)
allocates?
atomics?
I/O?
may trap?
returns alias of argument?
escapes argument?
```

These summaries power LICM, GVN, load forwarding, pure-call CSE, inlining, and scheduling.

### 5.3 Region-aware MemorySSA

LLVM MemorySSA versions one logical memory state and uses alias queries to find real clobbers. Oak should preserve independent regions:

```text
A0 --load--> A0
B0 --store--> B1
```

instead of making the store to `B` appear to clobber `A` and asking an alias analysis to undo the damage later.

Required node classes are analogous to MemorySSA:

```text
RegionUse
RegionDef
RegionPhi
```

but partitioned by semantic region where possible.

Use it for:

- load CSE;
- store-to-load forwarding;
- redundant-load elimination;
- dead-store elimination;
- LICM of loads;
- store sinking;
- loop memory promotion;
- call clobber queries;
- reordering independent accesses;
- vectorization dependence checks.

### 5.4 Escape/capture analysis

Oak should often know capture from authority and closure rules, but retain a compiler analysis for representation-level escapes.

Uses:

- scalar replacement;
- stack promotion;
- argument promotion;
- call specialization;
- proving private memory cannot alias extern state.

## 6. Scalar expression and local optimization catalog

### 6.1 InstSimplify-style identities

Cheap canonical equalities with no speculative behavior:

- `x + 0 -> x`;
- `x - 0 -> x`;
- `x * 1 -> x`;
- `x & all_ones -> x`;
- `x | 0 -> x`;
- `x ^ 0 -> x`;
- `x << 0 -> x`;
- comparison with known identical values;
- select with identical arms;
- nested conversions that cancel;
- redundant bool materialization.

Fixed-width Oak semantics make many of these easier to state precisely than in a UB-heavy IR.

### 6.2 InstCombine-style worklist canonicalization

Build a worklist combiner rather than one-off peepholes scattered through lowering.

Families:

- constant folding;
- strength reduction;
- fold nested adds/subtracts;
- fold nested shifts;
- combine masks;
- comparison canonicalization;
- convert compare+boolean patterns;
- fold extension/truncation chains;
- fold select of constants;
- canonical address arithmetic;
- choose constants on one side consistently;
- combine multiply/add into forms later machine selection can recognize.

After any rewrite, enqueue affected users for reconsideration.

### 6.3 Sparse conditional constant propagation

SCCP combines control-flow reachability with constant propagation.

Oak uses:

- remove unreachable match arms after specialization;
- propagate compile-time protocol tags;
- simplify branches from refinement facts;
- specialize constant arguments;
- fold feature/target-known values;
- remove dead paths exposed by inlining.

### 6.4 Early CSE

Cheap dominator-based common-subexpression elimination before expensive GVN.

Targets:

- repeated pure arithmetic;
- repeated `len`;
- repeated address computations;
- repeated immutable loads when RegionMemorySSA proves no clobber;
- repeated pure calls where arguments and effects permit.

### 6.5 GVN / value numbering

Global value numbering should recognize equivalent values across blocks, not merely textual duplicates.

Oak-specific opportunity: canonical semantic terms and refinements can make equivalence stronger than syntax alone.

### 6.6 Dead code elimination

DCE removes pure instructions whose values are unused.

ADCE-style logic starts from observable roots and retains only instructions/control needed to produce them. Observability in Oak must include traps, effects, atomics, resource transitions, protocol-visible operations, and host I/O.

### 6.7 Reassociation

Only law-licensed.

Integer wrapping operators with declared associativity can be reassociated where Oak semantics permit. Strict floating operations cannot.

Potential wins:

- shorter dependency chains;
- vector reductions;
- better constant folding;
- more parallel scheduling.

### 6.8 Copy propagation

Eliminate redundant moves at OptIR and MachineIR levels. Do it again after register allocation because allocation introduces new copies.

### 6.9 Select simplification and if-conversion

Current Oak work is already in this family. Generalize it:

- branch assigning one or more pure values -> selects;
- boolean increments -> conditional increment/select forms;
- min/max idioms -> target min/max or compare+select;
- absolute-value idioms where exact semantics match;
- nested selects simplification.

Effects must prevent unsafe conversion.

### 6.10 Code sinking

Move pure work into successor blocks when it is not needed on every path. This reduces executed work and can shorten live ranges.

Cost model must balance duplication against reduced execution and register pressure.

## 7. Control-flow optimization catalog

### 7.1 SimplifyCFG

Continuously clean CFG shape:

- remove empty blocks;
- merge blocks with single predecessor/successor;
- fold constant branches;
- invert conditions to remove jumps;
- simplify switch/match chains;
- remove unreachable blocks;
- canonicalize diamonds;
- retarget branch chains.

### 7.2 Jump threading

If facts on a predecessor determine the outcome of a later branch, bypass the redundant test.

Oak opportunity: refinements and typestate often make conditions known on one incoming path.

### 7.3 Correlated-value propagation

Use earlier relational checks to simplify later comparisons and guards. This is especially relevant to extents and binary-search bounds.

### 7.4 Branch chaining / branch folding

Retarget unconditional branch-to-branch sequences; merge equivalent tails; remove redundant condition inversions.

### 7.5 Tail duplication

Duplicate small blocks to remove branches and expose local scheduling/selection opportunities. Cost code size carefully.

### 7.6 Tail merging

Merge identical suffixes when code-size benefit exceeds branch cost.

### 7.7 Switch/match lowering candidates

Treat match lowering as a plan:

- compare chain;
- binary decision tree;
- jump table;
- bit test;
- lookup table;
- protocol table/shift DFA where semantics permit.

Cost depends on density, hotness, target branch behavior, and code size.

## 8. Aggregate and memory-local optimization catalog

### 8.1 Mem2Reg-style promotion

Promote local scalar memory that exists only because of source mutability into SSA values.

### 8.2 Scalar replacement of aggregates

LLVM SROA breaks stack aggregates into independent scalars. Oak should do this aggressively when representation and escape facts allow.

Examples:

- `[8]f32` accumulator -> eight virtual registers;
- small records -> field values;
- tuple/record temporaries -> independent values;
- by-value aggregate arguments -> scalar chunks.

This is already paying off in the tiled benchmark; make it systematic.

### 8.3 Dead store elimination

Remove a store when another store overwrites the same region before any observable read.

RegionMemorySSA should make this straightforward.

### 8.4 Store-to-load forwarding

Forward the most recent dominating store into a later load of the same region/offset when no intervening clobber exists.

### 8.5 Redundant load elimination

Reuse a prior load when RegionMemorySSA proves the region unchanged.

### 8.6 Store sinking

Move stores to exits when only the final value is observable. LICM-style memory promotion can turn loop-carried memory into SSA values and emit one final store.

### 8.7 Load combining / wide-load fusion

Generalize the landed byte-assembly fusion:

- adjacent bytes -> wider word load;
- adjacent scalar lanes -> vector load;
- pairable loads -> pair load;
- repeated subfield loads -> one aggregate load plus extracts when profitable.

Requires alignment/endianness/extent facts.

### 8.8 Store combining

Merge adjacent stores into wider scalar/vector stores when representation and alignment permit.

### 8.9 Memcpy/memmove/memset recognition

Recognize loops or store sequences implementing standard memory idioms and lower to the best target/library/runtime form allowed by Oak's runtime policy.

For freestanding verified profiles, the implementation may be an Oak/native body rather than libc.

### 8.10 Loop idiom recognition

LLVM recognizes patterns such as memset/memcpy and some bit/strlen loops. Oak should have a typed, verified idiom library.

Candidate idioms:

- zero/fill loops;
- copy loops;
- equality/first-difference scans;
- strlen/terminator scan where representation permits;
- population count;
- count leading/trailing zeros;
- byte swap;
- CRC forms;
- byte-pack/unpack;
- shift-until-zero/bit-test loops.

Each idiom maps to an intrinsic/native unit only when semantics match exactly.

## 9. Loop optimization catalog

### 9.1 LICM: loop-invariant code motion

Hoist invariant pure computations to the preheader and sink loop-invariant results where profitable.

Use effects/RegionMemorySSA for loads and calls.

Oak examples:

- constant table base;
- `len(span)`;
- invariant extent subtraction;
- invariant address base;
- pure conversion;
- immutable load from a disjoint region;
- pure helper call with invariant arguments.

Be register-pressure aware. Machine-level rematerialization can undo harmful hoists later.

### 9.2 Loop rotation / bottom-tested loops

Convert top-tested loops where profitable so the steady-state iteration has fewer branches and duplicated tests are reduced.

This directly matches the current native `sum`/search analysis.

### 9.3 Induction-variable simplification

Normalize equivalent induction variables, choose canonical widths, eliminate redundant counters, and rewrite exit comparisons into simpler forms.

### 9.4 Loop strength reduction

Replace repeated index arithmetic with recurrences/pointer induction.

Example:

```text
base[i * 8]
```

can become:

```text
p = base
loop:
    load [p]
    p += 8
```

where target addressing and overflow semantics permit.

### 9.5 Loop unrolling

Candidate factors should be planned and costed, not hard-coded.

Benefits:

- less branch overhead;
- more ILP;
- exposes pair/wide loads;
- exposes SLP;
- multiple independent accumulators.

Costs:

- code size;
- register pressure;
- verifier complexity;
- instruction-cache footprint.

### 9.6 Unroll-and-jam

Unroll an outer loop and fuse the duplicated inner bodies. Useful when inner-loop work can share loads or constants.

Potential Oak domains:

- matrix/tensor tiles;
- codec block processing;
- hash/compression rounds.

### 9.7 Loop peeling

Peel one or a few iterations to establish alignment, remove boundary checks, or simplify the main loop.

Oak can often avoid runtime peeling when alignment is a checked type fact.

### 9.8 Loop unswitching

Move a loop-invariant branch outside the loop, creating specialized loop versions.

Use only with cost/code-size limits. Candidate search is a natural fit because the unswitched and original loops can coexist as alternatives.

### 9.9 Loop deletion

Delete loops with no observable effects and no used result when termination is established by the semantic model.

### 9.10 Loop fusion

Fuse adjacent loops over compatible iteration spaces when dependence/effect analysis proves safety.

Benefits:

- less loop overhead;
- better temporal locality;
- exposes producer-consumer forwarding;
- may reduce intermediate storage.

Oak's region/effect information should make legality easier than pointer-based dependence analysis.

### 9.11 Loop distribution / fission

Split a loop when separating independent work improves vectorization, cache behavior, or register pressure.

This is the inverse of fusion and should be cost-driven.

### 9.12 Loop interchange

Swap nested loop order to improve memory locality or vectorization when dependence analysis permits.

Useful for matrix/tensor kernels, but later than allocator/vector fundamentals.

### 9.13 Loop flattening

Combine nested loops into one induction space when it removes overhead or exposes vectorization and semantics are simple.

### 9.14 Loop versioning

LLVM sometimes emits a fast loop guarded by runtime checks plus a conservative loop. Oak should prefer static semantic facts, but versioning remains useful when a property is not statically known.

Examples:

- runtime alignment;
- dynamic non-overlap at an unsafe/FFI boundary;
- minimum trip count;
- CPU feature path.

Versioning is a candidate plan, never a semantic assumption.

## 10. Vectorization catalog

### 10.1 Plan representation: Oak VPlan

Adopt the durable VPlan idea:

```text
Legal
  -> Plan candidate VF/UF shapes
  -> Optimize plans
  -> Cost plans
  -> Prune
  -> Materialize best
```

Planning must not mutate input OptIR.

### 10.2 Vectorization factor and interleave/unroll factor

Treat VF and UF as coupled decisions.

For a `u64` sum on NEON:

```text
VF=1 UF=1
VF=1 UF=4
VF=2 UF=1
VF=2 UF=2
VF=2 UF=4
```

The existing verified four-accumulator reduction is already one point in this search space.

### 10.3 Map-loop vectorization

Start with pure elementwise loops over nonaliasing spans:

```text
out[i] = f(a[i], b[i])
```

Oak's borrow checker can often prove the no-alias condition LLVM must discover or guard at runtime.

### 10.4 Reduction vectorization

Support integer reductions whose operator law licenses reassociation:

- add;
- multiply where semantics/law permit;
- xor;
- and;
- or;
- min/max where defined.

Keep strict floating reductions ordered unless source semantics explicitly license reassociation.

### 10.5 Ordered floating reductions

LLVM can emit ordered reductions on some targets. Oak should eventually model this separate from reassociated tree reductions.

An ordered vector reduction must preserve Oak's exact operation order; if target/vector semantics cannot do that profitably, retain scalar order.

### 10.6 First-order recurrences

Vectorize loops where iteration `i` consumes a value from `i-1` when a correct shuffle/rotation plan exists.

Later milestone; requires stronger vector-plan representation.

### 10.7 Interleaved access groups

Recognize strided structures such as AoS fields and combine them into wide loads/stores plus shuffles when target supports it.

### 10.8 Gather/scatter

Use target gathers/scatters for non-contiguous accesses only when their cost beats scalarized alternatives. SVE/RVV may make this more attractive than NEON.

### 10.9 Predicated / masked vectorization

Convert control inside loops to masks when safe and profitable.

Requirements:

- masked operation has exact semantics for inactive lanes;
- traps/effects cannot happen on inactive lanes;
- target supports efficient predicate/mask form or scalarization is still profitable.

### 10.10 Runtime pointer checks

LLVM creates overlap checks when aliasing is unknown. Oak should avoid these for safe spans whose ownership already proves non-overlap.

Runtime checks remain appropriate for raw/unsafe/FFI pointers.

### 10.11 SLP / superword-level parallelism

Pack independent scalar operations into vectors even outside loops.

High-value Oak targets:

- crypto rounds;
- fixed-array arithmetic;
- codec field transforms;
- hash state updates;
- record field operations;
- unrolled reductions;
- pixel/audio/DSP operations.

Use bottom-up packing from common stores or results, with cost-based pack formation.

### 10.12 Re-vectorization

Eventually allow plans to consume already-vector code and combine/narrow/widen it when the target cost model prefers another shape.

### 10.13 Scalable vectors

SVE and RVV require plans parameterized by vector length rather than one fixed lane count.

Keep fixed-width and scalable vector abstractions distinct in MachineIR, while sharing legality/planning where possible.

## 11. Interprocedural optimization catalog

### 11.1 Cost-driven inlining

Inlining score should include more than call overhead and code size:

```text
benefit:
  call overhead removed
  constants exposed
  refinements exposed
  extents exposed
  alignment exposed
  noalias facts exposed
  branch folding enabled
  vectorization enabled
  specialization enabled

cost:
  code growth
  instruction-cache pressure
  scalar register pressure
  vector register pressure
  estimated spills
  verifier complexity
```

Do not aggressively inline before vector register allocation exists.

### 11.2 Partial inlining

Split a small hot path from a large cold body and inline only the hot region. Particularly useful for validation/error slow paths.

### 11.3 Interprocedural SCCP

Propagate constants and unreachable paths through the call graph.

### 11.4 Argument promotion

If an internal callee only reads fields/elements of a by-reference aggregate and does not capture it, consider passing the values directly.

Oak's authority/capture model should make legality precise.

### 11.5 Dead argument elimination

Remove internal arguments that are never observed, including mutually recursive dead-argument chains.

### 11.6 Function property deduction / Attributor-like fixpoint

LLVM's Attributor deduces interacting properties across functions. Oak already knows many properties semantically, but still needs a fixpoint layer for optimization-derived facts.

Candidate properties:

```text
pure
readonly(regions)
writeonly(regions)
nocapture(arg)
returns-noalias
non-null
alignment(arg)
range(result)
willreturn / finite under stated conditions
cold / hot
```

Semantic facts dominate inferred facts; optimizer inference may strengthen but never contradict the checked model.

### 11.7 Function specialization

Clone internal functions for profitable constants/ranges/lengths/alignment/CPU features.

Examples:

- fixed span length;
- known enum variant;
- constant codec mode;
- known block size;
- aligned buffer;
- processor feature path.

Candidate search should compare specialized vs generic call paths.

### 11.8 Pure-call CSE

If a function is semantically pure and arguments are equal, common repeated calls.

### 11.9 Dead call/result elimination

Remove unused pure calls and unused result components while preserving effects/resource semantics.

### 11.10 Global constant merging

Merge identical immutable global data when identity is not observable.

### 11.11 Global dead-code elimination

Remove unreachable internal functions, tables, types/realizations, and constants after specialization and dispatch resolution.

### 11.12 Merge equivalent internal functions

If two specialized functions lower to semantically identical bodies and symbol identity is unobservable, share one implementation or emit thunks where ABI identity matters.

### 11.13 Whole-package / link-time planning

Long term, use package/link visibility to specialize cross-module calls, delete dead realizations, and choose dispatch forms. Keep this separate from the language semantic model.

## 12. Generic machine IR and instruction-selection patterns

LLVM GlobalISel contains several ideas worth adapting even if Oak does not copy its implementation.

### 12.1 Generic machine operations

MachineIR should initially contain target-neutral operations such as:

```text
G_ADD
G_SUB
G_MUL
G_LOAD
G_STORE
G_ICMP
G_SELECT
G_BUILD_VECTOR
G_EXTRACT
G_CALL
```

with virtual registers and types.

### 12.2 Legalization

Each target declares which operation/type combinations are legal and how illegal forms are transformed.

Examples:

- split unsupported wide integer;
- widen narrow integer;
- scalarize unsupported vector width;
- lower generic operation to helper/native sequence;
- materialize target-specific intrinsic.

Legality must be queryable before materializing a plan so candidate search can avoid impossible shapes.

### 12.3 Register-bank selection

Separate broad register bank from final physical register allocation.

AArch64 examples:

- GPR;
- FP/SIMD vector bank;
- flags/condition state as special machine state.

RV64 may distinguish integer, floating, and vector banks.

Cost bank-crossing copies and cluster related operations accordingly.

### 12.4 Instruction selection

Select target instructions after generic MachineIR has been legalized.

Support multi-instruction combining/folding across use-def chains rather than only one-node-at-a-time selection.

### 12.5 Machine combiners

Run target-independent and target-specific pattern combines before/after selection:

- `mul + add -> madd` where semantics allow;
- compare + select -> `csel` family;
- increment-under-condition -> `cinc/csinc`;
- shifts folded into addressing/ALU operands;
- load plus extension -> extending load;
- store of truncated value -> narrow store;
- constant materialization folding;
- address base+offset folding.

## 13. Register allocation catalog

### 13.1 Unlimited virtual registers before allocation

Do not force source locals into physical homes during lowering.

### 13.2 Live intervals

Compute liveness over MachineIR and represent intervals/segments so allocation can reason globally.

### 13.3 Greedy global allocation

LLVM's default allocator is greedy with global live-range splitting. That is a good model for Oak's first production allocator.

Core behavior:

- prioritize expensive live ranges;
- assign available physical register;
- split around pressure/calls if needed;
- spill only when cheaper than alternatives.

### 13.4 Live-range splitting

Split one virtual value so hot portions remain in registers while cold/call-crossing portions spill or move banks.

This directly addresses the UTF-8 vector problem better than storing every call-crossing vector local in a frame slot.

### 13.5 Coalescing

Prefer allocations that eliminate copies between virtual registers without creating harmful interference.

### 13.6 Rematerialization

Recompute cheap values instead of spilling/reloading them:

- small constants;
- simple addresses;
- target constants;
- immutable length values.

### 13.7 Spill-cost model

Weight spills by:

- loop depth/frequency;
- register class;
- vector width;
- memory latency;
- whether value is rematerializable;
- call frequency.

### 13.8 Caller/callee-save planning

Treat calling convention costs explicitly rather than statically pinning classes of locals.

### 13.9 Allocation candidates

Candidate search can try a few alternative splits/allocation priorities in hot functions and retain the cheapest verified result.

## 14. Instruction scheduling catalog

### 14.1 Pre-register-allocation scheduling

Reorder independent instructions to hide latency while controlling register pressure.

Examples:

- issue loads before dependent arithmetic;
- overlap independent multiply/hash lanes;
- separate long-latency division from dependent chain;
- schedule multiple accumulators.

### 14.2 Post-register-allocation scheduling

After physical allocation, reorder within constraints to improve pipeline use and avoid structural hazards.

### 14.3 Latency vs register pressure

The scheduler must trade parallelism against longer live ranges. This is why scheduling belongs after a real liveness model exists.

### 14.4 Software pipelining / modulo scheduling

LLVM's MachinePipeliner uses Swing Modulo Scheduling to overlap iterations. Later Oak target for:

- DSP loops;
- streaming codecs;
- fixed-latency arithmetic pipelines;
- ML inner loops.

It should run on machine loops before register allocation or with allocation-aware planning, with explicit prolog/kernel/epilog candidates.

## 15. Late machine optimization catalog

### 15.1 Machine copy propagation

Remove redundant copies after allocation/selection.

### 15.2 Peephole optimization

Target-local cleanup:

- redundant moves;
- immediate folding;
- compare/test simplification;
- extension elimination;
- zero-register forms;
- load/store addressing folds;
- branch inversion.

### 15.3 Branch folding

Merge common branch destinations/tails and remove redundant jumps.

### 15.4 Tail duplication

Duplicate short blocks to improve fallthrough and scheduling when code-size cost is acceptable.

### 15.5 Machine block placement

Order blocks so likely paths fall through and hot chains are contiguous.

Needs static or profile branch probabilities.

### 15.6 Prolog/epilog optimization

After stack size and spills are known:

- save only used callee-saved registers;
- eliminate frame pointer where ABI/debug policy allows;
- pack stack slots;
- shrink-wrap saves/restores around paths that actually need them;
- pair stack loads/stores where profitable.

### 15.7 Constant islands / literal placement

For targets that require range-limited literals or branches, treat layout as a late machine concern with verifier-visible semantics.

## 16. Branch probability, frequency, and profile-guided optimization

### 16.1 Static branch probability

Before PGO, derive priors from semantics/shape:

- loop backedge usually hot;
- trap/error edge cold;
- assertion failure cold;
- match default may be cold if semantic profile says so;
- bounds failure cold;
- explicit likely/unlikely annotation if Oak ever adds one.

### 16.2 Block frequency

Propagate edge probabilities into relative block frequencies. Feed:

- inlining;
- code-size tradeoffs;
- spill costs;
- block placement;
- unswitching;
- tail duplication;
- vectorization minimum-trip decisions.

### 16.3 Instrumentation PGO

Optional future mode:

- instrument edges/calls/value sites;
- run representative workload;
- merge profile;
- feed candidate cost model.

### 16.4 Sample PGO

Later support profiles derived from sampled instruction addresses if toolchain ecosystem warrants it.

### 16.5 Hot/cold splitting

Move rare error/validation paths out of hot functions to reduce instruction-cache pressure and improve inlining of hot regions.

Oak has many explicit trap/error paths that are good candidates.

### 16.6 Profile-driven candidate search

PGO should not bypass semantics. It only changes profitability:

```text
same legal candidate set
+ better frequency/cost information
= better choice
```

## 17. Vector and scalar cost model details

The target cost interface should grow toward:

```text
TargetCosts {
  arithmetic(op, type)
  cast(op, from, to)
  compare(type)
  select(type)
  division(type)

  load(type, alignment, addressingMode)
  store(type, alignment, addressingMode)
  pairLoad(type)
  pairStore(type)
  gather(type, lanes)
  scatter(type, lanes)

  vectorOp(op, laneType, lanes/scalable)
  shuffle(mask)
  reduction(op, laneType, lanes, ordered)
  scalarization(type)

  call(signature)
  branch(probability)
  switch(shape)

  spill(registerClass)
  reload(registerClass)
  bankCopy(from, to)

  latency(instructionClass)
  reciprocalThroughput(instructionClass)
  codeSize(instructionClass)
}
```

Keep separate objectives for speed and size; a future `-Os`/`-Oz` style mode can rank the same legal candidates differently.

## 18. Optimization remarks and records

Mirror LLVM's three useful categories:

```text
Passed
Missed
Analysis
```

Examples:

```text
passed vectorize loop@sum: VF=2 UF=2, est 0.52x scalar
missed vectorize loop@dot: strict FP reduction is ordered
missed inline utf8.check_block: est vector pressure 38 > 32
analysis regalloc utf8.valid_with: 27 vector intervals, 4 splits, 1 spill
passed licm page_probe: hoisted len(keys) and page count
missed pair-load foo: alignment 8 < required 16
```

Serialized optimization records should include:

- source position;
- transform name;
- requirements considered;
- cost alternatives;
- selected candidate;
- structural metrics;
- verifier verdict;
- fallback reason.

This becomes the performance-debugging API for users and for Oak itself.

## 19. Analysis preservation and invalidation

Every transform should declare preserved analyses.

Example:

```text
StrengthReduceExpression
  preserves:
    CFG
    Dominators
    LoopInfo
    RegionMemorySSA
  invalidates:
    KnownBits(value users)
    CostEstimate(region)
```

A loop rotation may preserve semantic region identities but invalidate dominators, loop canonical form, recurrence caches, and block frequencies.

Selective invalidation is essential for compile-time scalability once candidate search grows.

## 20. Phase structure: simplification and optimization alternate

A durable pipeline pattern from LLVM is that cleanup is repeated between major transforms.

Oak's candidate planner can still be phased:

```text
SemIR projection
    -> canonical SSA / CFG simplify
    -> scalar simplify
    -> call specialization / inline candidates
    -> scalar simplify
    -> loop canonicalize
    -> LICM / induction / loop candidates
    -> scalar simplify
    -> vector planning
    -> scalar / CFG cleanup
    -> generic MachineIR
    -> legalize / combine
    -> instruction select
    -> machine combine
    -> schedule
    -> register allocate
    -> post-RA cleanup / schedule
    -> block placement
    -> emit
    -> semantic validate selected body
```

Candidate search means this is not one irreversible sequence for every decision, but phase boundaries still bound combinatorial explosion.

## 21. Transform registry proposed for Oak

A practical directory taxonomy:

```text
optimizer/
  analysis/
    dominators
    loops
    recurrences
    ranges
    known_bits
    regions
    memory_ssa
    call_effects
    frequency

  scalar/
    inst_simplify
    inst_combine
    sccp
    early_cse
    gvn
    dce
    adce
    reassociate
    constraint_propagation

  cfg/
    simplify
    jump_thread
    if_convert
    tail_duplicate
    branch_fold

  memory/
    scalar_replace
    load_forward
    dse
    store_combine
    wide_load
    idioms

  loop/
    canonicalize
    licm
    rotate
    indvars
    strength_reduce
    peel
    unroll
    unroll_jam
    unswitch
    delete
    fuse
    distribute
    interchange
    flatten

  vector/
    plan
    loop_vectorize
    reduction
    slp
    interleave
    predicate
    gather_scatter

  ipo/
    inline
    partial_inline
    specialize
    ipsccp
    arg_promote
    dead_args
    infer_properties
    global_dce
    merge_functions

  machine/
    legalize
    reg_bank
    select
    combine
    schedule
    regalloc
    copyprop
    peephole
    branch_fold
    block_place
    pipeline
```

Names need not mirror LLVM in implementation, but each concept should remain discrete enough to test and cost independently.

## 22. Oak-specific replacements for LLVM inference

This is where Oak should outperform a generic C-derived optimizer structurally.

| LLVM often has to infer | Oak should consume directly |
| --- | --- |
| pointer non-aliasing | borrow/authority facts |
| readonly/readnone | effect rows |
| nocapture | ownership/closure capture facts |
| bounds | extent proofs |
| alignment | type/representation fact |
| integer range | refinement proposition |
| reduction associativity | declared operator law |
| enum/tag range | ADT semantics |
| call side effects | checked effect summary |
| runtime overlap checks | usually unnecessary for safe disjoint spans |
| loop memory independence | region identities + borrow facts |

Do not throw these facts away and then rebuild weaker approximations from MachineIR.

## 23. LLVM techniques Oak should deliberately not copy blindly

### 23.1 Undefined-behavior-based optimization

Oak's safe semantics are explicit. Never introduce optimizations that rely on C/C++ undefined behavior, poison, or assumptions absent from Oak.

### 23.2 Unlicensed fast-math

No reassociation, contraction, distributivity, reciprocal approximation, or signed-zero/NaN weakening unless the Oak source semantics explicitly select it.

### 23.3 One anonymous memory universe when regions are known

Region identity is valuable semantic information. Preserve it.

### 23.4 Runtime alias checks where static borrowing already proves disjointness

Do not pay at runtime for a question the type checker has answered.

### 23.5 Giant hand-ordered global pass dependence

The architecture should prefer discrete candidate transforms, shared analyses, phase-local canonicalization, and final validation.

### 23.6 Trusting pass correctness

Tests are necessary but not the semantic gate. A candidate must satisfy the relevant proof/check/verification boundary.

## 24. Suggested priority from the LLVM survey

The dependency order matters more than the sheer number of optimizations.

### P0: observability and machine substrate

1. optimization remarks + structural metrics;
2. generic/target MachineIR;
3. virtual GPR/vector registers;
4. liveness/live intervals;
5. global allocator with splitting/rematerialization;
6. vector locals across calls;
7. machine combiner and basic scheduler.

This attacks the measured UTF-8 spill/call gap.

### P0: reusable middle-end analyses

8. OptIR SSA/CFG;
9. dominators/post-dominators;
10. loop forest + canonical loop form + explicit exits;
11. recurrence/ScalarEvolution-lite;
12. known bits + range/constraint propagation;
13. region-aware MemorySSA + call Mod/Ref.

### P1: high-value scalar/loop transformations

14. worklist InstCombine-style canonicalizer;
15. SCCP / EarlyCSE / GVN / DCE;
16. LICM;
17. loop rotation;
18. induction simplification / address induction;
19. generic unroll planning;
20. store/load forwarding and DSE;
21. idiom recognition.

### P1: vector planning

22. VPlan-like representation;
23. integer reduction vectorization;
24. map/zip vectorization;
25. SLP;
26. interleaved access groups;
27. vector-aware target costs;
28. scalable SVE/RVV plans.

### P1: interprocedural

29. cost-driven inlining;
30. constant/range/extent/alignment specialization;
31. IPSCCP;
32. property/effect fixpoint;
33. argument promotion/dead arguments;
34. pure-call CSE and global DCE.

### P2: machine throughput and layout

35. richer scheduling;
36. post-RA scheduling;
37. branch/tail optimization;
38. machine block placement;
39. hot/cold splitting;
40. software pipelining.

### P3: advanced loop/search work

41. loop fusion;
42. loop distribution;
43. interchange;
44. flattening;
45. runtime versioning at unsafe boundaries;
46. larger equality saturation;
47. profile-guided candidate search;
48. superoptimization of small hot regions.

## 25. Relationship to candidate search

Every item in this catalog should fit the optimizer-search architecture.

Example: integer reduction.

```text
source reduction
    |
    +-- identity scalar
    +-- rotate scalar loop
    +-- unroll2
    +-- unroll4
    +-- unroll4 + pair loads
    +-- NEON VF2
    +-- NEON VF2 + UF2
    `-- SVE scalable

legal facts:
  associativity
  extents
  nonalias regions

target cost:
  loads / vector ops / branches / spills

validation:
  source-law theorem where reassociated
  machine semantic equivalence for final body
```

Example: call-heavy UTF-8 block checker.

```text
call tree
    |
    +-- calls, vector values split around calls
    +-- calls, callee-saved/vector spill strategy
    +-- inline leaves
    +-- inline whole block checker
    +-- inline + SLP/vector combine
    `-- mixed plan

cost includes:
  call overhead
  code growth
  vector pressure
  spill count
  schedule length
```

The optimizer is therefore a search over discrete, understandable techniques rather than one opaque global rewrite.

## 26. Verification rules per family

| Family | Primary correctness gate |
| --- | --- |
| constant/bit identities | reusable theorem and/or semantic validator |
| CFG simplification | semantic validator |
| bounds/check removal | checked semantic fact + validator |
| load/store motion | ownership/effects/RegionMemorySSA + validator |
| LICM | invariance + Mod/Ref + validator |
| allocation/scheduling | machine semantic validator |
| instruction selection/combine | machine semantic validator / ISA bridge |
| unrolling without reassociation | validator |
| reassociated reduction | declared law / Lean rewrite theorem + validator |
| vector reduction | law or ordered semantics + validator |
| inlining | source call-expansion law + validator |
| specialization | source substitution/refinement law + validator |
| PGO/layout | same semantics; profile affects cost only |

The optimizer implementation remains outside the trusted base wherever practical.

## 27. Landing checklist for a new transform

A transform is complete only when it has:

1. a discrete name and implementation boundary;
2. a declared scope;
3. explicit semantic requirements;
4. explicit analysis dependencies;
5. a conservative identity fallback;
6. a target-cost model entry if profitability is target-dependent;
7. `Passed`, `Missed`, and useful `Analysis` remarks;
8. structural before/after tests;
9. negative legality tests;
10. verifier/proof coverage at the correct boundary;
11. benchmark evidence on the intended workload;
12. no degradation of verified-profile verdicts for the claimed result.

## 28. Sources surveyed

Primary LLVM documentation used for this catalog:

- LLVM Loop Terminology and canonical forms: <https://llvm.org/docs/LoopTerminology.html>
- LLVM analysis and transform passes: <https://llvm.org/docs/Passes.html>
- MemorySSA: <https://llvm.org/docs/MemorySSA.html>
- Alias Analysis: <https://llvm.org/docs/AliasAnalysis.html>
- Auto-Vectorization: <https://llvm.org/docs/Vectorizers.html>
- Vectorization Plan / VPlan: <https://llvm.org/docs/VectorizationPlan.html>
- Target-independent code generator: <https://llvm.org/docs/CodeGenerator.html>
- GlobalISel overview: <https://llvm.org/docs/GlobalISel/index.html>
- GlobalISel pipeline: <https://llvm.org/docs/GlobalISel/Pipeline.html>
- GlobalISel legalizer: <https://llvm.org/docs/GlobalISel/Legalizer.html>
- GlobalISel instruction selection: <https://llvm.org/docs/GlobalISel/InstructionSelect.html>
- Generic Machine IR: <https://llvm.org/docs/GlobalISel/GMIR.html>
- New Pass Manager: <https://llvm.org/docs/NewPassManager.html>
- Optimization remarks: <https://llvm.org/docs/Remarks.html>
- Block frequency terminology: <https://llvm.org/docs/BlockFrequencyTerminology.html>
- Loop fusion: <https://llvm.org/docs/LoopFusion.html>
- Machine software pipeliner / Swing Modulo Scheduling: LLVM `MachinePipeliner` documentation/source.

The specific LLVM implementation will continue to evolve. The durable ideas recorded here are the separation of analyses from transforms, canonical forms, explicit legality and cost modeling, multiple candidate planning, virtual-register machine IR, region/dependence reasoning, and reusable optimization families.

## 29. End state

The target is not "Oak implements every LLVM pass." The target is:

```text
strong checked Oak facts
    |
    v
reusable analyses
    |
    v
large library of discrete candidate transforms
    |
    v
bounded search over combinations
    |
    v
target-aware cost model
    |
    v
best candidate
    |
    v
independent proof / semantic validation
```

LLVM supplies decades of optimization techniques and architectural lessons. Oak's opportunity is to combine them with semantic facts LLVM usually has to infer and with a validation boundary that lets the proposal machinery remain aggressive, replaceable, and maintainable.

## 30. Wikipedia's taxonomy, mapped

Wikipedia's compiler-optimization navbox names the classical passes by
their textbook names. Each maps to a section above, or is named here as
not applicable to Oak's lanes, so a reader arriving with the textbook
vocabulary finds the catalog's entry.

| Wikipedia | Catalog | Note |
| --- | --- | --- |
| Basic block | §2, §3.1–3.2 | the unit of the dominator and post-dominator trees; the verifier's `joinPoints` is the post-dominator computation on the emitted items |
| Peephole optimization | §15.2 | the late machine peepholes; the checker's rewrite rules are the landed instances |
| Local value numbering | §6.4, §6.5 | Early CSE is the block-local numbering, GVN the global one |
| Automatic parallelization | — | not applicable: v1 has no threads in the verified subset; the vector lane (§10) is the parallelism Oak offers |
| Automatic vectorization | §10 | Oak VPlan, map-loops, reductions, SLP |
| Induction variable | §9.3, §4.1 | recognition is the recurrence analysis; elimination is IV simplification and loop strength reduction (§9.4) |
| Loop fusion | §9.10 | |
| Loop-invariant code motion | §9.1 | landed as hoisting on the native lane |
| Loop inversion | §9.2 | loop rotation: the bottom-tested form the backend already emits for counted loops |
| Loop interchange | §9.12 | |
| Loop nest optimization | §9.6, §9.13 | unroll-and-jam and flattening; tiling waits for a cache model (§17) |
| Loop splitting | §9.7, §9.11, §9.14 | peeling, distribution, and versioning are its three forms |
| Loop unrolling | §9.5 | landed as reduction unrolling, law-backed (`Oak.Reduction.unrolled4_eq`) |
| Loop unswitching | §9.8 | |
| Software pipelining | §14.4 | |
| Strength reduction | §9.4 | landed for constant arithmetic (`Oak.StrengthReduction`) |
| Available expression | §6.4 | the dataflow name for what Early CSE computes |
| Common subexpression elimination | §6.4, §6.5, §11.8 | local, global, and across pure calls |
| Constant folding | §6.1 | the term constructors fold today (`asm/verify.go`), the rewrite layer will |
| Dead store elimination | §8.3 | |
| Induction variable recognition and elimination | §9.3 | |
| Live-variable analysis | §13.2 | live intervals; `nativegen/liveness.go` is the landed instance |
| Upwards exposed uses, use-define chain, reaching definitions | §3.3 | the SSA form makes the three implicit: a use names its one definition |
| Global value numbering | §6.5 | |
| Sparse conditional constant propagation | §6.3, §11.3 | intra- and interprocedural |
| Instruction scheduling | §14 | |
| Instruction selection | §12.4 | |
| Register allocation | §13 | the machine IR's reallocator is a candidate (`nativegen/machine`) |
| Rematerialization | §13.6 | |
| Deforestation | §9.10 | the functional name for fusing a producer loop into its consumer; Oak's map-loops over spans are the case |
| Tail-call elimination | §7, verifier | the backend emits loops for Oak's tail recursion where it can; the verifier reads a tail-recursive body as its loop (`tailRecursionAsLoop`) |
| Interprocedural optimization | §11 | |
| Bounds-checking elimination | §4.3, §4.4 | the checker's proven-extent elision (`Lane.ElideProven`) and the loop facts are the landed forms; the range and constraint analyses generalize them |
| Compile-time function execution | §6.1, §11.7 | folding a pure call with constant arguments, and specialization for the rest |
| Dead-code elimination | §6.6, §11.11 | |
| Expression templates | — | a C++ idiom for fusing operator chains at the source level; Oak's helper expansion (§9.y of the assembler spec) and reassociation (§6.7) are the compiler-side forms |
| Inline expansion | §11.1, §11.2 | landed as verified helper expansion, law-backed as substitution |
| Jump threading | §7.2 | |
| Partial evaluation | §11.7 | function specialization on constant arguments |
| Profile-guided optimization | §16 | |
| Alias analysis, pointer analysis | §5 | not LLVM's: regions and borrows give the disjointness statically (§5.1, §23.3–23.4) |
| Array-access analysis, dependence analysis | §4.1, §10.7, §10.10 | recurrences over the index, interleaved groups, and the runtime pointer checks that remain |
| Control-flow analysis | §3 | |
| Data-flow analysis | §3.3, §4, §5.3 | over SSA and MemorySSA rather than bit-vector frameworks |
| Escape analysis | §5.4 | |
| Shape analysis | — | heap shapes; not applicable while the verified subset has no heap pointers — regions (§5.3) carry what shape analysis would infer |
| Value range analysis | §4.3 | |

