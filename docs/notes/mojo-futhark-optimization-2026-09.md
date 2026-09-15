# Mojo and Futhark optimization lessons for Oak

Status: design survey, September 2026.

This note complements:

- `docs/notes/optimizer-search-2026-09.md`, which defines Oak's candidate and
  validation architecture;
- `docs/notes/llvm-optimization-catalog-2026-09.md`, which surveys conventional
  middle-end and machine-optimizer engineering;
- `docs/notes/proof-guided-optimization-2026-09.md`, which records the
  optimizations Oak can license from checked semantic facts.

LLVM remains the main reference for general optimizer infrastructure. Mojo and
Futhark add different lessons:

| System | Most useful lesson for Oak |
| --- | --- |
| Mojo | optimize on both sides of specialization and express optimization shapes as parameterized plans |
| Futhark | preserve algebraic/parallel structure, then optimize fusion, placement, representation, and memory globally |
| Oak | combine both with proof-derived legality and independent validation of the selected implementation |

This is a source survey and an Oak proposal. Descriptions of Mojo and Futhark
below are observations from their public documentation, papers, and compiler
source. Names such as `PlanFamily`, `IndexProperties`, and
`DestinationForwarding` are proposed Oak concepts, not claims about either
compiler's API.

## 1. Mojo: optimize across the specialization boundary

Mojo's compiler uses MLIR dialects at multiple abstraction levels. Its public
compiler walkthrough separates source-level LIT, pre-elaboration KGEN/POP/HLCF,
elaboration/monomorphization, post-elaboration optimization, and LLVM lowering.
The pre-elaboration pipeline includes SROA, Mem2Reg, canonicalization,
parametric inlining, SCCP, apply inlining, and dead-symbol removal. After
parameters become concrete, the pipeline performs more aggressive inlining,
loop recognition/unrolling, argument promotion, control-flow simplification,
and dead-argument elimination.

The lesson is not to copy this pass list mechanically. Oak should make the
specialization boundary explicit:

```text
generic SemIR / structured OptIR
        |
        v
cheap canonicalization
dead parameter/result removal
scalar/aggregate promotion
conservative inlining
        |
        v
specialize / elaborate
types, values, extents and target facts become concrete
        |
        v
aggressive candidate planning
loop, vector, layout and machine search
        |
        v
MachineIR
```

Doing all aggressive work before specialization hides constants and target
facts. Doing it all afterward needlessly multiplies large generic bodies. The
pre-specialization stage should reduce the program without eagerly destroying
useful cache and sharing boundaries. The post-specialization stage can spend a
larger search budget because it has concrete facts.

The first executable slice landed on 2026-09-15. Private-leaf inlining remains
pre-specialization. Type checking then creates concrete generic functions, and
`source.canonical.bool.v1` runs over those functions before backend selection.
Its first laws remove redundant built-in Boolean operators while retaining each
non-literal operand exactly once; `source.canonical.integer.v1` does the same
for fixed-width zero/one identities while excluding floats, widening
expressions, and user-defined operators. The retained operand must have the
same exact checked fixed-width type as the result. A fresh type check over a clone validates the result without
overwriting specialization provenance. Boolean literal negation waits for typed
OptIR rather than changing a source token that keys specialization facts. More aggressive SCCP and dead-path
removal wait for structured OptIR to carry effects, traps, borrows, and protocol
obligations explicitly.

Oak should record the stage on every transform and reject invalid scheduling:

```text
PreSpecialization
Specialization
PostSpecialization
Machine
PostAllocation
```

The distinction is an optimizer scalability rule, not a semantic rule.

## 2. Parameterized plan families

Mojo makes compile-time types and values available to specialization. Its
compile-time loops can expand during elaboration, and its algorithm library
expresses tiling and unswitching with static parameters.

Oak can use the same idea internally without requiring the same source syntax:

```text
ReductionPlan[
    vectorWidth,
    unrollFactor,
    aligned,
    tailStrategy,
    targetFeatures,
]
```

This should be one `PlanFamily`, not separate hard-coded passes named
`vectorize2`, `vectorize4`, `unroll2`, and every combination of those choices.
The family:

1. declares finite parameter domains;
2. uses target legality and semantic facts to prune impossible combinations;
3. estimates remaining combinations without materializing all of them;
4. admits a bounded set into candidate search;
5. validates the selected materialization against the stable semantic
   reference.

This gives Oak a compact transform library while still exploring target-specific
shapes.

## 3. Optimization combinators and boundary unswitching

Mojo's standard algorithm library exposes static tiling, functional
unswitching, vectorization, parallelization, and reductions. Its
`tile_middle_unswitch_boundaries` abstraction separates a left boundary, a
middle tiled region, and a right boundary. Boundary predicates remain enabled
where needed, while the middle work can be specialized for the proved interior.

Oak should model this as a general loop plan:

```text
prologue
  guarded scalar or narrow work

proved interior
  no per-access bounds checks
  selected alignment strategy
  wide/vector work

epilogue
  guarded remainder work
```

Extent, alignment, and index proofs should derive the largest legal interior.
The plan family can compare scalar, peeled, masked, and
prologue/interior/epilogue candidates. This is proof-driven unswitching: a
single outer decision replaces repeated inner checks, and a theorem can remove
the outer decision entirely when the precondition is already known.

## 4. Preserve structured control and semantic graphs

Mojo retains structured high-level control flow in HLCF until late lowering and
even has a `RaiseForLoops` pass that recognizes loop patterns before loop
optimization. Oak should avoid discarding structure and then relying on every
transform to rediscover it.

OptIR should preserve first-class structured objects where available:

```text
Region
Loop
If
Match
Reduction
ParallelMap
ProducerConsumerGraph
```

This does not prohibit SSA or CFG analyses. Structured regions should have an
explicit projection to canonical CFG/SSA, with invalidation rules in both
directions. Fusion, tiling, flattening, and reduction planning should run while
their algebraic structure is still explicit. Arbitrary machine control flow is
introduced only when those transformations no longer need the structure.

## 5. Ownership must remain optimizer information

Mojo's origin design uses ownership/origin information for lifetime checking,
but its current design strips origins during `LowerLIT`. Oak should not copy
that lifetime. Oak's authority, borrow, escape, and effect facts are more
valuable if they survive as proof-carrying optimizer facts.

Those facts can license:

- no-alias scheduling and vectorization;
- destination forwarding;
- scalar replacement across calls;
- exact read/write summaries;
- storage reuse;
- removal of overlap checks.

The frontend remains the authority for these facts. OptIR should reference
their provenance rather than invent a second, weaker ownership analysis.

## 6. Futhark: optimize algebra before lowering parallelism

Futhark's current public pipeline repeatedly alternates simplification with
inlining, CSE, fusion, and AD before parallel lowering. The GPU pipeline then
extracts kernels and applies reduction optimization, tiling, histogram
optimization, unstreaming, CSE, sinking, device-synchronization reduction,
GPU-body merging, and layout optimization. Explicit allocations are introduced
after that high-level work; the memory pipeline then applies entry-point memory
handling, double buffering, allocation lifting/lowering, array
short-circuiting, memory-block merging, and more simplification/CSE.

Two rules transfer directly:

1. alternate enabling cleanup with major transformations;
2. delay irreversible physical storage decisions until algebraic, parallel,
   and layout opportunities have been considered.

Oak's pipeline remains candidate-based, but candidate search does not remove
the need for phases. Phase boundaries keep analysis invalidation and search
growth tractable.

## 7. Fusion as bounded graph reduction

Futhark's fusion pass constructs a dependency graph and performs horizontal and
vertical fusion of second-order array combinators. Its implementation retains a
`gas` budget that bounds fusion attempts.

Oak should represent producer/consumer alternatives as graph candidates:

```text
producer -> temporary -> consumer

producer+consumer
       |
       `-> no temporary
```

Legality must include effects, authority, dependencies, extents, operator laws,
and index properties. Profitability must include removed traffic, duplicated
work, lost parallelism, register pressure, code size, and verification cost.
Fusion search consumes an explicit budget; it must not be an unbounded fixed
point over the whole program.

For array/tensor/data-parallel code, prefer:

```text
semantic operation graph
    -> bounded fusion/restructuring
    -> parallelization/flattening plan
    -> loop/vector plan
    -> memory/layout plan
```

over immediately lowering every semantic operation to ordinary loops and then
trying to rediscover the graph.

## 8. Multi-versioning at the correct decision time

Futhark's incremental flattening generates multiple semantically equivalent
parallel implementations and selects at runtime based on input shape and
tuning thresholds. This is strong evidence for Oak's candidate architecture,
but runtime retention should be deliberate.

Oak needs three selection times:

| Selection time | Suitable facts | Result |
| --- | --- | --- |
| compile time | constants, proofs, fixed target profile | emit one implementation |
| load/startup time | detected CPU/accelerator features | resolve once, keep hot loops direct |
| runtime | dynamic extents, workload shape, data distribution | guarded choice among a small version set |

Runtime versioning is justified only when:

- the deciding fact is unavailable earlier;
- the expected gain pays for dispatch, instruction-cache, and code-size costs;
- the candidate count and thresholds are bounded;
- every retained implementation is independently admissible;
- an identity or conservative implementation remains available.

Thresholds belong to the cost/autotuning layer, never the correctness layer.
Profiles may change which valid implementation is selected but cannot license
one.

## 9. Proofs should select representations

Futhark's size analysis and 2026 full-flattening work distinguish uniform from
nonuniform nested parallelism. Uniform sizes permit simpler rectangular
representations; nonuniform sizes require segmented or irregular
representations.

Oak should generalize that rule:

```text
fixed_extent(a, 16)
  -> fixed/unrolled representation candidate

equal_extent(a, b)
  -> zipped/vector representation candidate

uniform(inner_extent)
  -> rectangular representation candidate

not_proved_uniform(inner_extent)
  -> segmented or guarded candidate
```

Proofs are therefore not merely check-elimination tokens. They can determine
which representation family is legal and profitable.

## 10. An index-property proof domain

The PLDI 2026 Futhark work implements a compiler analysis over a deliberately
small property set: equivalence, range, injectivity, bijectivity,
monotonicity, filtering, and partitioning. It infers index functions and uses
those properties to reason about bulk-parallel programs, including nonlinear
indexing, scatters, FFTs, graph algorithms, and irregular flattened programs.

Oak should add a shared proof domain rather than teaching every transform its
own index solver:

```text
IndexProperties {
    equivalent
    range
    injective
    bijective
    monotonic
    filtering
    partitioning

    // useful derived propositions
    disjoint
    covers
    permutation
}
```

The first seven are the compact primitive vocabulary supported by the Futhark
work. `disjoint`, `covers`, and `permutation` are proposed Oak derived facts,
not additions attributed to that paper.

Consumers include:

- bounds and trap elimination;
- gather/scatter parallelization;
- proving total overwrite and dead initialization;
- destination forwarding and in-place updates;
- vectorization and fusion;
- layout transformation;
- dependence analysis and buffer reuse.

The domain should be deterministic and incomplete. Difficult propositions can
fall back to the ordinary solver/certificate path, while failure to prove a
property merely retains the conservative candidate.

## 11. Destination forwarding

Futhark's array short-circuiting proves that a producer can construct a value
directly in its destination memory. This removes an intermediate allocation and
turns the final copy/update into a no-op. The analysis uses memory blocks,
index functions, and read/write overlap reasoning; the project also explored
Z3 before removing that dependency from the merged compiler.

Oak should make this a first-class transform family named
`DestinationForwarding`:

```text
tmp = produce(...)
write(dst[slice], tmp)

        becomes

produce_into(dst[slice], ...)
```

Required facts can include:

```text
destination authority is unique or otherwise writable
producer result has no observable storage identity
destination mapping covers the produced value
producer reads do not conflict with forwarded writes
alignment and extent obligations hold
all aliases and effects are accounted for
```

This applies beyond arrays:

- return-value construction;
- codecs and serialization;
- packet and protocol-message assembly;
- tensor intermediates;
- database/page construction;
- concatenation and builder pipelines.

The high-level API may still expose ordinary value construction. An explicit
low-level `produce_into` API remains useful where the programmer wants stable
allocation control; the optimizer can prove when the high-level form lowers to
the same implementation.

## 12. Storage allocation as coloring

Futhark's current memory-block merger runs interference analysis over
kernel-level allocations and applies greedy graph coloring. Allocations with the
same color share one physical block sized to the maximum member requirement.

Oak should reuse a common storage-allocation framework:

```text
logical storage values
    -> exact/proved lifetimes
    -> interference graph
    -> target/space-compatible coloring
    -> physical storage assignment
```

Possible clients:

- register allocation;
- stack-slot coloring;
- scratch-buffer reuse;
- local array storage;
- accelerator local/shared memory;
- fixed arena slots on freestanding/embedded targets.

Color compatibility includes address space, alignment, size, escape, lifetime,
and target constraints. Ownership may give Oak more exact logical lifetimes,
but the final assignment is still a costed candidate and must preserve the
observable memory/resource contract.

## 13. Host/device placement as graph optimization

Futhark's `ReduceDeviceSyncs` constructs a data-flow graph and finds a minimum
vertex cut separating device-produced scalar reads from uses that must remain
on the host. It then migrates selected computations to the device to reduce
blocking host/device transfers.

For future heterogeneous Oak targets, placement should be an explicit graph
problem:

```text
nodes: computations
node costs: execution/resource cost per device
edges: value/control dependencies
edge costs: transfer, conversion and synchronization
constraints: supported operations, effects, authority, memory spaces
```

Candidate partitions can target CPU, GPU, DSP, or another accelerator. A graph
cut is one useful algorithm, not the permanent universal cost model. The proof
obligation includes value equivalence, effect order, synchronization, and
memory-space transitions.

## 14. Relationship to `SCKelemen/ml`

The `SCKelemen/ml` project is already a domain-specific instance of much of
this architecture:

- lazy tensors build a small semantic operation graph;
- movement operations compose views instead of copying data;
- the scheduler forms and fuses kernels;
- horizontal fusion combines compatible reductions;
- `realize_into` directs construction into caller-provided storage;
- kernel forms carry tile, lane, reduction, epilogue, and layout decisions;
- captured launches and structural kernel caches separate planning from replay;
- Lean specifications cover view algebra, fusion legality, and canonical
  reduction scheduling, while C remains the conformance oracle for generated
  kernels.

The important separation is:

```text
ml graph / kernel semantics
    -> domain-specific candidate and obligation generation
    -> generic Oak PlanFamily / target-cost / validation services
    -> CPU, Metal, or future accelerator implementation
```

Oak's core OptIR should know about regions, reductions, index functions,
authority, effects, layouts, and target operations. It should not know about
attention, layer normalization, GPT-2, or any other ML-specific operation.
Those stay in `ml` and decompose into the generic vocabulary.

`ml` is therefore a useful forcing function for the general optimizer:

1. its current lane, tile, split, epilogue, and backend choices become explicit
   plan parameters;
2. its scheduler reports the candidates considered, requirements used, and
   reason selected;
3. its `realize_into` path becomes the first end-to-end destination-forwarding
   case;
4. its horizontal reductions become the first bounded producer/consumer graph
   fusion cases;
5. its benchmark corpus measures whether general planning matches or improves
   the existing hand-shaped kernels before the mechanism is generalized.

The current C/Metal generation and differential oracle remain valuable. A plan
does not gain Oak's native assembly-validation claim until its selected kernel
is inside the corresponding checked lowering path.

## 15. Priority for Oak

These additions are ordered by dependency and near-term value.

| Priority | Workstream | Depends on |
| --- | --- | --- |
| P0 | explicit pre-/post-specialization stages | transform registry, SemIR facts |
| P0 | structured loop/control/region OptIR | OptIR, canonical CFG projection |
| P0 | parameterized plan families | bounded candidate selector, target legality |
| P1 | index-property proof domain | ranges/extents, proof provenance |
| P1 | proof-derived interior/boundary loop planning | canonical loops, index properties |
| P1 | graph-based producer/consumer fusion | structured OptIR, effects/dependencies |
| P1 | destination forwarding | region memory form, authority, index properties |
| P1 | storage interference coloring | explicit logical allocations, liveness |
| P1 | compile/startup/runtime candidate selection model | plan families, dispatch ABI |
| P2 | uniform/segmented representation planning | shape/extent propositions |
| P2 | block/register tiling and double-buffer plans | loop/vector/storage planning |
| P2 | layout planning | index functions, target costs |
| P2 | nested-parallel flattening planner | semantic parallel regions, fusion |
| P2 | profile/autotuned runtime thresholds | measurements, bounded versioning |
| P3 | heterogeneous graph placement | accelerator IRs, transfer/sync model |

`P0` means the representation and phase contracts must account for the feature;
it does not mean all algorithms must be implemented before the nearer measured
MachineIR and allocator work. In particular, heterogeneous placement should
not complicate the first native CPU optimizer.

## 16. Landing rules

Each transform family from this survey must still satisfy Oak's ordinary
landing rule. In addition:

1. record whether selection occurs at compile, startup, or runtime;
2. name every proof/property consumed and its provenance;
3. retain a conservative or identity candidate;
4. measure candidate count, generated code size, compile/proof time, and runtime;
5. use explicit gas/budgets for graph and parameter-space search;
6. validate each implementation that can be selected;
7. never infer reassociation, race freedom, allocation freedom, or host/device
   legality from a cost model.

## 17. Sources surveyed

Mojo:

- compiler phases and pass summaries:
  <https://github.com/modular/modular/blob/main/Mojo/docs/compiler/MojoCompilerWalkthrough.md>
- passes and intermediate representations:
  <https://github.com/modular/modular/blob/main/Mojo/docs/compiler/manual/PassesAndIR.md>
- compile-time evaluation:
  <https://docs.modular.com/mojo/manual/metaprogramming/comptime-evaluation>
- generic parameters and specialization:
  <https://docs.modular.com/mojo/manual/generics/>
- static tiling:
  <https://docs.modular.com/mojo/std/algorithm/backend/tile/tile/>
- unswitching:
  <https://docs.modular.com/mojo/stdlib/algorithm/functional/unswitch/>
- middle/boundary tiling:
  <https://docs.modular.com/mojo/std/algorithm/backend/unswitch/tile_middle_unswitch_boundaries/>
- origin design:
  <https://github.com/modular/modular/blob/main/Mojo/proposals/origin-design.md>

Futhark:

- current compiler pipelines:
  <https://github.com/diku-dk/futhark/blob/master/src/Futhark/Passes.hs>
- graph-reduction fusion implementation:
  <https://github.com/diku-dk/futhark/blob/master/src/Futhark/Optimise/Fusion.hs>
- graph-reduction fusion paper:
  <https://futhark-lang.org/publications/fhpc13.pdf>
- incremental flattening:
  <https://futhark-lang.org/publications/ppopp19.pdf>
- full flattening and uniformity:
  <https://futhark-lang.org/blog/2026-07-31-full-flattening.html>
- array representation and index functions:
  <https://futhark-lang.org/blog/2024-03-06-array-representation.html>
- array short-circuiting:
  <https://futhark-lang.org/blog/2022-11-03-short-circuiting.html>
- memory-block merging implementation:
  <https://github.com/diku-dk/futhark/blob/master/src/Futhark/Optimise/MemoryBlockMerging.hs>
- device-synchronization migration implementation:
  <https://github.com/diku-dk/futhark/blob/master/src/Futhark/Optimise/ReduceDeviceSyncs/MigrationTable.hs>
- index-property verification:
  <https://futhark-lang.org/publications/pldi26.pdf>

Oak ML forcing function:

- specified tensor compiler and kernel planner:
  <https://github.com/SCKelemen/ml>
- existing Futhark comparison:
  <https://github.com/SCKelemen/ml/blob/main/docs/notes/futhark-learnings.md>
- current kernel-form obligations:
  <https://github.com/SCKelemen/ml/blob/main/docs/notes/kernel-forms.md>

## 18. Synthesis

The durable architecture is:

```text
semantic and structured program
        |
        v
cheap generic simplification
        |
        v
bounded specialization
        |
        v
fusion / representation / parallel candidates
        |
        v
loop / vector / destination / storage candidates
        |
        v
MachineIR candidates
        |
        v
cost at the earliest valid decision time
        |
        v
independently validate every selectable implementation
```

Mojo contributes the staged and parameterized shape. Futhark contributes the
algebraic graph, multi-version, index, placement, and memory algorithms. Oak's
contribution is to expose stronger authority, extent, effect, law, and proof
facts to those planners and to keep profitability outside the semantic trust
boundary.
