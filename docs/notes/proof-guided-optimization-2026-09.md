# Proof-guided optimization for Oak

Status: research/design note, September 2026.

This note is the Oak-native companion to:

- `docs/notes/optimizer-search-2026-09.md` — candidate-search architecture;
- `docs/notes/llvm-optimization-catalog-2026-09.md` — conventional optimization techniques worth adapting;
- `docs/notes/optimization-2026-09.md` and `docs/notes/native-optimization-2026-09.md` — current implementation and benchmark program;
- `docs/spec/90-backend.md` §16 and `docs/spec/94-assembler.md` §9 — normative backend and native verification rules.

The LLVM-derived catalog answers:

> Which optimization techniques have decades of compiler engineering shown to be useful?

This note answers a different question:

> **Which optimizations become possible, simpler, or substantially stronger because Oak has checked semantic facts, formal models, declared algebraic laws, and a native lane whose selected machine body is independently checked against the Oak body?**

The distinction matters. Oak should not stop at becoming a smaller LLVM. Its strongest optimizer advantage is that many facts a conventional compiler must guess, infer conservatively, or guard at runtime are already part of the language's checked meaning.

The core shape is:

```text
formal Oak semantics
      |
      v
checked facts / proofs / models / laws
      |
      v
untrusted candidate generators
  /       |        |        \
scalar   SIMD    tables   machine search
  \       |        |        /
      target cost search
            |
            v
     selected machine body
            |
            v
 seam checker + semantic verifier
        /             \
    proven           refused
      |                 |
     use          next / identity
```

For a body admitted by the verified native profile, optimization success means the selected implementation has a `proven` verdict at the existing native verification boundary. This does **not** mean every frontend, checker, planner, or proof-search implementation is itself fully formally verified; the purpose of the architecture is precisely to keep proposal machinery out of the trusted base wherever possible.

## 1. Proofs are optimizer inputs, not comments

Oak's checked semantic representation already has authoritative homes for:

- types and representations;
- ownership/authority;
- resources and typestate;
- capabilities;
- required and forbidden effects;
- structured propositions;
- proof status;
- protocol states and transitions.

Optimization should carry useful facts forward with provenance rather than collapse them to booleans such as `known=true`.

Conceptually:

```text
Fact {
    proposition
    provenance
    scope
    dependencies
}
```

Possible provenance includes the proof statuses already present in SemIR:

```text
specified
checked
proved-smt
proved-kernel
model-checked
tested
refined
```

A transform can then say not only:

```text
requires aligned(p, 16)
```

but, where policy demands it:

```text
requires aligned(p, 16) with proof >= checked
```

or:

```text
verified profile requires theorem/certificate accepted by the relevant proof boundary
```

This makes optimization assumptions inspectable and prevents optimizer-only inferred guesses from silently acquiring the same authority as language proofs.

## 2. Proof-directed trap and guard elimination

The most direct optimization family is turning proved impossibility into absent machine work.

Candidate facts:

- `index < extent` -> remove bounds branch/trap;
- divisor `!= 0` -> remove divide-by-zero guard;
- signed division cannot be the trapping/min-overflow case where applicable;
- shift amount is within the language-defined admissible range -> remove normalization/guard where the operation semantics permit;
- conversion result fits target width -> remove narrowing trap/check;
- arithmetic is proved in range -> remove checked-overflow branch;
- pointer/span is aligned -> remove dynamic alignment path;
- ADT tag belongs to a known subset -> remove impossible tag checks;
- protocol transition is legal -> remove runtime transition validation;
- UTF-8/codec state invariant -> remove repeated state-range guards;
- non-null/refinement fact -> remove null branch at a checked boundary;
- resource is live in this typestate -> remove liveness assertion.

The important difference from ordinary range optimization is provenance:

```text
heuristic says probably safe   -> never sufficient
analysis derives safe          -> useful candidate fact
checked theorem says safe      -> semantic license
```

The final native body still passes the ordinary seam checker and semantic verifier.

## 3. Proof-carrying optimization IR

OptIR should be able to attach semantic evidence to values, regions, edges, and loops.

Examples:

```text
%p : span<u8>
  fact len(%p) >= 64
  fact aligned(%p, 16)
  fact region(%p) disjoint region(%q)

%i : u32
  fact %i < len(%p)

loop L
  invariant i <= n
  invariant p == base + i
  effect read(region(p))
```

A transform consumes these facts and may produce new derived facts.

Examples:

```text
len(p) >= 64
+ i <= 48
=> i + 16 <= len(p)
```

or:

```text
aligned(base, 16)
+ i % 16 == 0
=> aligned(base + i, 16)
```

The proof object/provenance should remain reachable from the optimization record so a missed or selected transform can explain exactly which proposition licensed it.

## 4. Solver-generated optimization invariants

Conventional compilers mostly derive invariants from syntax and abstract interpretation. Oak can additionally ask its proof machinery to establish candidate invariants.

A transform can propose:

```text
candidate invariant: i <= n
candidate invariant: len(out) == len(in)
candidate invariant: p == base + 8*i
candidate invariant: state != Error
candidate invariant: accumulator <= MAX
```

and ask the relevant prover/decision procedure to establish it from checked preconditions and loop transitions.

If proved, the invariant becomes optimizer input.

Uses:

- eliminate loop-body bounds checks;
- prove an address induction safe;
- prove a loop runs at least one/vector-width iteration;
- hoist checks to a preheader;
- license vector loads/stores;
- prove a loop's memory regions remain disjoint;
- prove a typestate cannot reach an error state;
- prove a branch is unreachable;
- prove a narrowing operation safe for every iteration.

This creates a useful division:

```text
optimizer proposes a useful theorem
prover decides whether it is true
optimizer exploits it only if established
```

The theorem search can remain heuristic and untrusted.

## 5. Proof-mined dead paths

SCCP and range propagation remove paths that are syntactically or abstractly unreachable. Oak can go further when a solver or formal model proves a condition cannot occur under the current specialization.

Targets:

- impossible match variants;
- impossible protocol states/transitions;
- impossible error returns;
- impossible integer comparison outcomes;
- impossible bounds/trap arms;
- unreachable resource states;
- feature/target paths excluded by a checked deployment contract;
- codec/state-machine cases ruled out by an invariant.

Once a path is proved unreachable, ordinary DCE/CFG simplification can erase the dependent code.

Important distinction:

```text
cold != unreachable
```

A branch is deleted only from a proof, never because profiling says it did not happen.

## 6. Typestate- and protocol-guided specialization

Oak's protocols and typestate are not merely safety checks; they define reachable state space.

Possible optimizations:

### 6.1 State-specialized functions

If a call site proves a resource is in state `Open`, generate:

```text
read_open(...)
```

with branches for `Closed`, `Uninitialized`, or invalid transitions absent.

### 6.2 Transition-check elimination

A proved legal transition needs no runtime legality branch.

### 6.3 State representation reduction

Inside a region where only a subset of states is reachable, the machine representation may use a smaller local discriminant or no discriminant at all, provided observable representation contracts are preserved.

### 6.4 Protocol implementation selection

The existing protocol-table/shift-DFA lowering is the prototype: one declarative formal machine can admit multiple equivalent implementations:

```text
branch tree
lookup table
shift-packed table
specialized per-state code
vector batch transition
```

The model proves the representation implements the declared transition relation; the target cost model chooses the implementation.

### 6.5 Batched validation

If the formal machine proves that a sink/error marker summarizes exactly the first illegal transition, a loop can defer checks until after a batch rather than branch per element.

This is an example of a performance transformation derived from the formal model rather than from local instruction patterns.

## 7. ADT- and refinement-guided representation optimization

Formal knowledge of values can simplify representations.

### 7.1 Variant specialization

If a theorem proves an ADT value at a point is always `Some`, remove the tag test and expose the payload directly.

### 7.2 Locally dead discriminants

If all uses in a region agree on one proved constructor, avoid materializing/reloading the tag inside that region.

### 7.3 Narrow value representation

A proved range may allow a narrower temporary/register representation when widening at observable boundaries preserves the declared representation.

Example:

```text
x : u32
proof x < 256
```

may use an 8-bit/narrow machine operation or packed vector lane where profitable, without changing the external `u32` type.

### 7.4 Compact table/index representations

Proved state/range bounds can choose narrower table entries, offsets, indices, and vector lane types.

### 7.5 Niche/compact ADT representations

Where Oak's representation contract allows backend choice and an injective mapping can be proved, candidate representations can exploit unused values/niches. This must never silently change an explicitly stable FFI/wire/persisted layout.

## 8. Ownership-guided memory elimination

Ownership can license transformations that a conventional compiler approaches through alias analysis.

### 8.1 Proven no-alias scheduling

Independent unique/shared regions allow loads/stores to move without runtime alias checks.

### 8.2 Defensive-copy elimination

If unique ownership proves no observer can see mutation, avoid temporary copies/snapshots introduced by conservative lowering.

### 8.3 Reload elimination across calls

If the callee's checked effects cannot write a region, values loaded from that region remain valid across the call.

### 8.4 Store elimination under uniqueness

If a unique region is overwritten before any permitted observer can read it, the earlier store is dead.

### 8.5 Borrow-aware scalar replacement

A record/array can remain decomposed into SSA values across calls as long as authority/capture facts prove no escaping alias observes its physical storage.

### 8.6 No runtime overlap versioning

Safe disjoint spans can vectorize directly rather than generating LLVM-style pointer-overlap tests plus fast/slow loop versions.

Runtime overlap checks should remain mainly for raw/unsafe/FFI boundaries where Oak lacks a proof.

## 9. Effect-proof optimization

Effect rows can provide exact motion and elimination licenses.

### 9.1 Pure-call CSE

Two calls with the same arguments and no observable effects can share one result.

### 9.2 Pure-call hoisting

A loop-invariant pure call can move to the preheader.

### 9.3 Call reordering

Calls whose effect sets are proved independent can be reordered for scheduling or register pressure when evaluation-order semantics permit the transformation.

### 9.4 Dead call elimination

A call with no effects and unused result can disappear.

### 9.5 Effect-local scheduling

Machine scheduling can move ordinary instructions around calls more aggressively when exact clobber/effect summaries prove the relevant state untouched.

### 9.6 Resource/effect-aware fusion

Adjacent operations may fuse only when the combined operation has exactly the allowed effect semantics; the effect system supplies the proof obligation explicitly.

## 10. Refinement-guided specialization

A conventional optimizer often clones functions for constants. Oak can specialize for richer proved predicates.

Candidate specialization keys:

- exact value;
- numeric range;
- nonzero;
- power-of-two;
- span extent;
- minimum slack;
- alignment;
- non-alias relation;
- ADT constructor;
- protocol/typestate state;
- effect subset;
- representation property;
- target feature proved by deployment/dispatch path.

Example:

```text
parse(span)
```

can produce candidates such as:

```text
parse_len_at_least_64_aligned16
parse_ascii_only
parse_known_variant
```

when those preconditions are already proved by the caller. No runtime guard is required when specialization follows a theorem.

The cost model must still prevent specialization explosion.

## 11. Proof-guided loop optimization

Loop transforms can carry explicit theorem obligations rather than rely solely on syntactic dependence tests.

### 11.1 Bounds-free main loops

Prove once that an entire vector/unrolled iteration remains inside all extents, then remove per-access checks.

### 11.2 Verified address induction

Prove:

```text
p_i == base + i * stride
```

and replace repeated index arithmetic with pointer induction while retaining source-level bounds meaning.

### 11.3 Verified fusion

Prove no forbidden dependence/effect ordering exists between two loops, then fuse.

### 11.4 Verified distribution

Prove separating statements preserves all data/effect dependencies, then split to improve vectorization/register pressure.

### 11.5 Verified interchange

Prove dependence order is invariant under loop permutation, then choose the order with better locality/vector shape.

### 11.6 Verified unroll-and-jam

Use induction/dependence theorems to combine outer iterations without hand-coded special cases.

### 11.7 Verified software pipelining

Prove the overlapped iteration schedule preserves dependence distances and observable effect order; validate the final machine kernel/prolog/epilog against the same source loop.

### 11.8 Proof-driven loop deletion

Delete a loop only when it has no observable effects/results and termination/finite execution is established under Oak semantics.

## 12. Proof-directed vectorization

Vectorization can consume proof premises directly.

Typical vector plan requirements:

```text
extent >= VF * UF
alignment >= required
regions disjoint
body pure / effects lane-independent
operator associative if reduction tree changes
inactive lanes cannot trap or perform effects
```

Those can come from the type checker/prover rather than speculative runtime checks.

### 12.1 Integer reductions

The current verified reduction-unrolling work is the seed. Extend candidate plans to:

```text
scalar
scalar unroll2
scalar unroll4
pair-load unroll4
NEON reduction
NEON + interleave
SVE scalable
RVV scalable
```

A source-level associativity theorem licenses grouping changes; the machine verifier checks the selected body.

### 12.2 Ordered floating reductions

Strict floating semantics remain ordered. A vector plan is legal only if it preserves the exact Oak operation order or the source explicitly selects a relaxed/reassociated law.

### 12.3 Proof-eliminated vector guards

A proof of alignment/extent/non-overlap can remove vector prolog checks and alias versioning entirely.

### 12.4 Typestate vectorization

If a protocol/model proves all elements are in a state admitting the same transition, batch/vector transition code can replace per-element dynamic dispatch.

## 13. Formal memory-model optimization

Oak's explicit atomics/memory model plus ISA semantics can support machine choices that are normally trusted backend lore.

Potential candidates:

- select the weakest machine ordering that still implements the Oak ordering;
- eliminate redundant fences when surrounding operations already establish the required ordering;
- combine adjacent fences;
- choose acquire/release instruction forms vs explicit barriers;
- exploit architecture-specific dependency/order guarantees only when captured in the formal ISA/memory model;
- prove a sequentially consistent operation sequence equivalent to a cheaper target realization where the model allows it.

These optimizations must be conservative about the current formal coverage. AArch64/RV64 proofs should only license the portions actually represented in the model; unsupported memory-system behavior remains outside the optimization claim.

## 14. Model-derived implementation synthesis

Protocols show a general pattern:

```text
declarative formal object
      |
      v
multiple implementation representations
      |
      v
proof each representation refines the object
      |
      v
cost model chooses target form
```

Apply the same idea to other finite/formal structures.

Candidates:

### 14.1 Codecs

From a formal codec schema generate:

- branch implementation;
- table implementation;
- wide-load implementation;
- SIMD implementation;
- specialized fixed-width form.

### 14.2 Quorum/threshold logic

From the declared model derive:

- scalar count;
- bitset/popcount;
- lookup table for small domains;
- SIMD mask count.

### 14.3 Dispatch

From closed target/feature alternatives derive direct branches, tables, one-time resolved function choice, or compile-time selection.

### 14.4 Bitsets and finite sets

From domain cardinality derive scalar word, multiword, vector, or table representation.

### 14.5 State machines

From formal transitions derive branch trees, direct tables, compressed tables, perfect hashes, shift DFAs, or vector batch machines.

The compiler is choosing among **proved implementations of the same model**, not guessing at equivalent code after the fact.

## 15. Verified instruction synthesis and superoptimization

The strongest consequence of Oak's assembler/verifier is that target code generation can increasingly be search.

For a small hot region, generate many candidate instruction sequences:

```text
addressing-mode alternatives
constant-materialization alternatives
branch vs select
mul/add vs madd
scalar vs pair load
scalar vs vector
shuffle alternatives
register assignment alternatives
instruction schedules
unroll factors
```

Then:

```text
1. reject illegal encodings/ABI shapes cheaply
2. estimate target cost
3. keep a small best set
4. run semantic verification in cost order
5. retain the cheapest proven sequence
```

The candidate generator may be heuristic, evolutionary, enumerative, equality-saturation based, or target-specific. It does not need to be trusted if the proof gate is sound.

### 15.1 Bounded local superoptimization

Begin with straight-line regions of perhaps 3-20 operations and a bounded target instruction grammar.

Good first targets:

- bit manipulation;
- constant multiply/divide sequences;
- address calculations;
- compare/select idioms;
- byte pack/unpack;
- small reductions;
- fixed shuffles.

### 15.2 Proof-backed peephole discovery

Search can discover a useful sequence first. Once it repeatedly wins, promote it to a named deterministic transform with a reusable theorem/certificate path.

This reverses the usual workflow:

```text
search discovers optimization
proof confirms it
engineering turns it into a cheap standard recipe
```

## 16. Verifier-guided candidate search

Verification refusal should not merely be a terminal error; it is information for search.

A refusal can be classified:

```text
unsupported verifier construct
missing semantic fact
seam checker rejection
semantic mismatch
proof budget exceeded
ISA bridge unavailable
```

The planner can respond differently:

- unsupported vector op -> try scalar candidate;
- proof budget exceeded -> try structurally simpler equivalent;
- missing alignment fact -> keep unaligned candidate;
- seam rejection -> choose another allocation/addressing form;
- semantic mismatch -> discard candidate permanently for this input;
- unavailable ISA bridge under verified profile -> choose an instruction inside the proved subset.

Longer term, counterexamples from an equivalence checker can guide candidate repair.

This makes the verifier part of optimization search without making it part of profitability heuristics.

## 17. Proof cost is a legitimate secondary optimization objective

For verified builds, compile/proof time matters.

If two candidates have essentially equal runtime cost:

```text
A: verifies in 20 ms
B: verifies in 4 s
```

prefer A.

Candidate score can be lexicographic or weighted:

```text
runtime estimate
code size
verification cost estimate
cacheability / proof reuse
```

Runtime performance should remain the primary goal for speed-oriented builds, but proof cost can break near-ties and prevent search from making verified builds unusable.

Possible proof-cost predictors:

- instruction count;
- loop nesting;
- number of symbolic memory regions;
- number of branch couplings;
- vector lane complexity;
- calls requiring summaries;
- prior cached verification timings for the transform shape.

## 18. Proof-result caching as optimizer infrastructure

Candidate search makes caching more important.

Cache keys should include all semantics that matter:

- stable semantic reference/body;
- candidate MachineIR/assembly;
- target/CPU/features;
- reachable callee summaries;
- declarations/tables;
- verifier/checker identity;
- proof-relevant configuration.

Cache values can retain:

```text
verdict
certificate/proof object where available
verification time
refusal class
structural metrics
```

This allows repeated candidate shapes to become cheap across incremental builds.

## 19. Cross-ISA semantic synthesis

A source theorem should not force mirrored handwritten lowering across AArch64 and RV64.

Instead:

```text
same Oak semantic reference
       /             \
AArch64 search      RV64 search
     |                  |
NEON/SVE choices      RVV/scalar choices
     |                  |
AArch64 proof         RV64 proof
```

The implementations may look very different while sharing one semantic contract.

This is particularly attractive for:

- reductions;
- crypto/CRC;
- byte scans;
- table lookups;
- atomics;
- bit manipulation;
- codec kernels.

Target parity then means "both targets can produce a competitive proven candidate," not "both targets duplicate the same lowering algorithm."

## 20. Proof-guided representation selection

Where representation is not externally fixed, selection itself can be candidate search.

Possible choices:

- scalar vs packed bitset;
- dense vs sparse transition table;
- record fields vs packed word;
- tag+payload vs proved compact/niche encoding;
- fixed vector vs scalable vector intermediate;
- array-of-struct vs decomposed local registers when storage identity is unobservable.

Proof obligations can include:

```text
mapping is injective over observable values
encode/decode round trip
field projection preserved
alignment/size constraints
FFI/wire contract unchanged where applicable
```

This should remain conservative: explicit stable layouts are contracts, not optimization suggestions.

## 21. Proof-guided ABI and call optimization

For internal functions with no externally fixed ABI, semantic facts can drive call representation.

Candidates:

- scalarize small record arguments/results;
- omit semantically dead fields;
- specialize away a known tag;
- pass a proved constant implicitly by specialization rather than as a register argument;
- choose by-value vs borrowed internal representation when authority/effects prove equivalence;
- tail-call when frame/resource obligations are proved satisfied.

External/FFI ABI remains fixed by its contract.

## 22. Proof-guided devirtualization and dispatch elimination

Closed generics, protocol/typestate facts, and dispatch declarations can eliminate dynamic choice.

Examples:

- concrete generic specialization -> direct call;
- proved ADT variant -> direct implementation;
- protocol state -> state-specific direct transition;
- CPU dispatch path after one-time resolution -> direct selected body in hot loop;
- finite closed method set -> decision tree/table/direct specialization depending cost.

The proof/model establishes that no omitted implementation can be selected in the scope.

## 23. Resource-lifetime optimization

Resource types provide more than safety.

Potential optimizations:

- remove repeated live/consumed state checks once typestate proves the path;
- sink cleanup/release to the last path that owns the resource;
- eliminate cleanup on paths that prove the resource was moved/consumed;
- merge adjacent state transitions when no observation occurs between them;
- specialize wrappers around always-live resources;
- omit representation of compile-time-only resource state.

These require exact agreement with Oak's eventual destruction/drop/resource semantics; no optimization should run ahead of the normative lifetime contract.

## 24. Quantifier- and theorem-guided finite-domain optimization

Oak's finite quantifiers and theorem machinery can sometimes compile a proof/query into a finite constant structure.

Examples:

- `forall` over a small enum proved true -> constant true;
- `exists` with a unique witness known at compile time -> constant/witness specialization;
- finite predicate over byte/state pairs -> precomputed table/bitset;
- verified classification predicate -> 256-entry byte table, bitset, or SIMD range test candidate.

The cost model decides between recomputation and table representation.

## 25. Proof-producing analysis vs proof-consuming optimization

Keep these roles separate.

### Proof-producing analyses

Examples:

- range prover;
- non-alias/authority projection;
- recurrence invariant prover;
- protocol reachability;
- effect summarizer;
- algebraic law registry;
- SAT/SMT/kernel theorem path.

They output propositions/evidence.

### Proof-consuming transforms

Examples:

- bounds elimination;
- vectorization;
- LICM;
- specialization;
- representation selection;
- state elimination;
- memory reordering.

They should not contain their own private theorem provers when a shared proof service can establish the same fact.

## 26. Proof obligations as a transform API

A transform should be able to request facts declaratively.

Conceptually:

```text
Transform VectorizeReduction {
  match reduction(loop)

  obligations:
    extent_multiple_or_tail_plan(loop, VF)
    noalias(inputs, output)
    associative(op)
    no_lane_visible_effects(body)

  propose:
    scalar
    vector(VF)
    vector(VF, UF)
}
```

The planner asks available proof providers to discharge obligations.

This is preferable to hard-coding:

```text
if checkerThingA && solverThingB && specialCaseC ...
```

inside every transform.

The optimizer becomes a consumer of a uniform semantic fact service.

## 27. Proof strength and build profiles

Different build profiles may require different evidence without changing language semantics.

Example policy:

```text
normal native build:
  checked semantic fact + successful final verifier is sufficient

-verified profile:
  every reachable native body must receive required proven verdict;
  no witnessed/trusted/fallback body is accepted
```

As certificate-backed native verification grows, the policy can become stricter without redesigning transforms.

Transforms should therefore depend on abstract evidence requirements, not hard-code one prover implementation.

## 28. End-to-end examples

### 28.1 Sum reduction

Source:

```text
sum = fold(+, values)
```

Semantic facts:

```text
+ on u64 is associative under Oak's wrapping law
values extent known
reads are independent
```

Candidates:

```text
scalar
scalar rotated
unroll2
unroll4
unroll4 + ldp
NEON reduction
NEON + UF2
SVE scalable
```

Proof chain:

```text
reassociation/unroll source theorem
        +
selected assembly semantic verification
```

### 28.2 UTF-8 validator

Semantic/model facts:

```text
state machine transition relation
valid block extent
vector alignment/slack
helper effects are pure/read-only
```

Candidates:

```text
call tree
state-specialized helpers
inline leaf helpers
full inline
NEON block predicate
shift/table DFA
mixed vector + table plan
```

Register allocator/cost model decides whether inlining helps after accounting for vector pressure. Formal model decides whether table/state specializations are legal. Final native body must still prove.

### 28.3 Database page probe

Facts:

```text
page size fixed
key/value regions disjoint
index < slot_count
alignment known
table immutable during probe
```

Optimizations:

```text
remove bounds guards
hoist page metadata
promote repeated loads
vector compare keys
branchless mask/select
prefetch/schedule loads
specialize fixed slot count
```

No runtime alias/alignment checks are necessary when the caller proof already establishes them.

### 28.4 Protocol transition

Formal model proves:

```text
state S + event E -> S'
```

Candidates:

```text
branch tree
state-specialized direct code
dense table
compressed shift table
batch/vector table
```

The model/refinement proof establishes all candidates implement the same declared transition. Cost chooses the machine shape.

## 29. Research roadmap unique to Oak

### P0: make proofs consumable by the optimizer

1. optimizer fact/provenance representation;
2. uniform obligation/query API;
3. propagate authority/effects/extents/refinements/alignment into OptIR;
4. expose protocol/typestate facts;
5. optimization remarks name the proof/fact that licensed a transform.

### P1: turn existing proofs into immediate wins

6. generalized proof-directed guard/trap elimination;
7. range/nonzero/alignment specialization;
8. exact effect-based load/call CSE and LICM;
9. ownership-driven noalias vectorization;
10. typestate/protocol branch elimination;
11. proof-guided integer reduction vectorization.

### P1: proof-producing optimization analysis

12. solver-assisted loop invariant discovery;
13. theorem-backed dependence queries for loop transforms;
14. proof-mined unreachable-path elimination;
15. proof-derived alignment/slack propagation;
16. optimization-specific theorem/certificate caching.

### P2: model synthesis

17. generalized finite-state/table representation planner;
18. codec/table/SIMD candidate synthesis;
19. bitset/quorum representation synthesis;
20. representation selection with encode/decode/injectivity proofs.

### P2: verifier-guided machine search

21. bounded straight-line superoptimizer;
22. multiple schedule/allocation candidates for hot regions;
23. verifier refusal classification fed back into search;
24. proof-cost-aware tie breaking;
25. promote frequently winning search results into named transforms.

### P3: cross-layer proof-guided optimization

26. verified loop fusion/distribution/interchange;
27. verified software pipelining;
28. atomic/fence minimization from formal memory models;
29. cross-ISA candidate synthesis;
30. larger search regions/equality saturation plus final proof gate.

## 30. Landing rule for proof-guided optimizations

In addition to the ordinary optimizer landing checklist, a proof-guided transform should record:

1. the exact proposition(s) it consumes;
2. the provenance/evidence requirement for each proposition;
3. the source-level law if evaluation shape changes;
4. which semantic observations are preserved;
5. which verifier/checker boundary validates the final candidate;
6. the conservative candidate when proof is unavailable;
7. a negative test showing the transform does **not** fire without the proof;
8. an optimization remark naming the missing/used obligation;
9. benchmark and structural evidence;
10. verified-profile verdicts for affected bodies.

A proof-guided optimization is not "an optimization whose author believes a theorem applies." The compiler must be able to point to the fact or evidence that licensed it.

## 31. What not to do

Do not turn formal verification into a reason for reckless global search.

Avoid:

- proving huge optimized functions from scratch when compositional facts suffice;
- duplicating theorem logic inside every transform;
- hiding assumptions inside cost models;
- using model-checked/tested evidence as if it were a kernel theorem when policy distinguishes them;
- deleting checks because final machine testing happened to pass;
- weakening floating, atomic, resource, or evaluation-order semantics for speed;
- letting proof search make ordinary incremental builds unpredictably unbounded.

The architecture should make proofs **more reusable and local**, not make every optimization a giant theorem-proving problem.

## 32. End state

The long-term Oak optimizer should have two complementary sources of strength:

```text
LLVM-derived compiler engineering
  canonical IR
  reusable analyses
  vectorization
  allocation
  scheduling
  IPO
          +
Oak-native semantic knowledge
  ownership
  effects
  refinements
  extents
  alignment
  typestate/protocols
  declared laws
  formal models
  proof/certificate infrastructure
  assembly semantic verification
          =
optimizer as search over proved implementations
```

The distinctive goal is not merely "use proofs to remove bounds checks." It is:

> **Let formal semantics define a space of legal implementations, let untrusted optimization machinery search that space aggressively, and let a small independent proof/checking boundary decide which machine implementation is allowed to ship.**

That is the optimization architecture that can make Oak both more aggressive and easier to trust as the transform library grows.
