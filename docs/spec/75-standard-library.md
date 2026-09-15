# Oak Standard Library Architecture

Status: normative architecture; the v1 package cut and migration from the
bootstrap prelude are direction until their entries in `STABILITY.md` say
otherwise.

## 1. Purpose

The standard library is Oak's common vocabulary for values, algorithms,
storage, text, data formats, effects, and host capabilities. It follows the
language priorities in order:

1. correctness;
2. performance;
3. simplicity.

The order is operational. An API does not become acceptable by being small if
it loses a failure, ownership, progress, or validity fact. An optimization does
not become acceptable by being fast if the equality it relies on is unstated or
false under Oak's machine semantics. After the required facts and costs are
visible, Oak chooses the smallest orthogonal API.

The library is not a second language. Records, ADTs, pattern matching,
constraints, effects, borrowing, propositions, protocols, and ordinary
functions remain its building blocks. A library concern receives syntax only
when ordinary composition cannot preserve its semantics or cost.

## 2. Design ancestry

Oak adapts ideas; it does not promise source compatibility with another
standard library.

| Tradition | What Oak takes | What Oak does not inherit |
| --- | --- | --- |
| Go and Deno | Small packages, explicit imports, concrete APIs, readable names, narrow interfaces, portable service boundaries | Multiple returns, ambient global services, interface values where static structure is sufficient |
| Zig, Rust, and Odin | Visible allocation and storage, value semantics, explicit errors, predictable machine shape, unsafe boundaries | Allocator use hidden behind an innocent operation; unchecked behavior as the ordinary fast path |
| Standard ML, OCaml, F#, Elm, and Roc | ADTs as everyday vocabulary, exhaustive matching, pure functions, local inference, compositional transformations | A mandatory garbage collector or persistent allocation for ordinary collection use |
| Haskell | Laws, separation of pure description from effects, folds and traversals as reusable algebras | A universal hierarchy whose effects, allocation, evaluation order, or specialization are not evident at a call |
| Scala, Swift, and weePickle | Discoverable fluent APIs, builders, collection-preserving operations, protocol-oriented reuse, direct source-to-destination transforms | Deep inheritance/implicit-resolution towers, mandatory intermediate trees, or abstraction whose runtime representation is unclear |
| Futhark | Shape-aware data parallelism, fusion justified by semantics, explicit reduction laws | Implicit reassociation or parallel execution of ordinary sequential code |
| Coq, Lean, and Z3 | Machine-checked local laws, refinement obligations, proof-producing or proof-checked discharge | Treating a model as proof of its implementation |
| TLA+ and Apalache | State-machine and temporal validation of concurrent protocols | Replacing implementation correspondence and executable testing with model checking alone |

These precedents are design input. This chapter and the other files in
`docs/spec/` are the authority.

## 3. One coherent library, several environments

The compiler and standard library ship as one tested release unit through v1.
Packages are namespace and dependency boundaries, not independently selected
versions. A dotless first import segment remains reserved for this library as
specified by `83-modules.md`.

Every package belongs to one of three environments:

- **freestanding** packages require no operating system, allocator, scheduler,
  thread runtime, or global mutable state;
- **capability** packages perform effects only through values or ports that
  grant the required authority;
- **target** packages expose a named ABI, architecture, or host realization and
  never become a transitive requirement of a portable package.

Portable packages may select target-specific realizations internally when both
implement one semantic contract. A caller must not import an architecture
package merely to obtain the portable operation.

### 3.1 Portability matrix

Portability is proved and tested against profiles rather than inferred from one
successful host build. The standard library is designed for at least these
classes:

| Profile | Environment | Governing constraints |
| --- | --- | --- |
| Hosted desktop/server | macOS and Linux across supported 64-bit architectures | OS services exist only behind capabilities; target dispatch preserves portable semantics |
| Oak OS | Freestanding kernel, hypervisor, and userland on modern ARM machines | No libc or host OS assumption; bounded storage, explicit authority, static/realtime paths |
| Microcontroller | STM32-class and similar 32-bit freestanding systems | Small memory/code budgets; heap, FPU, threads, wide atomics, SIMD, and unaligned access may be absent |
| Portable model | Host/interpreter/Lean semantics independent of one ABI | Fixed-width machine arithmetic, explicit endian conversion, no assumed pointer width |

A portable package must not assume:

- a heap, filesystem, process, environment, thread runtime, or wall clock;
- 64-bit pointers or `usize`-sized data interchange;
- host byte order, permissive unaligned access, or a particular C ABI;
- floating-point hardware, SIMD, or lock-free atomics;
- one address space, or that all address spaces are coherent ordinary RAM.

Required target features are part of package/build admission. When a semantic
capability is unavailable, the build rejects it with a located explanation or
selects an explicitly documented portable realization. It does not link a stub
that fails only when called. A fallback that changes a material cost, timing,
atomic-progress, or side-channel guarantee is a distinct profile or contract.

Optimized realizations may be selected by build target or checked runtime CPU
dispatch. Each realization implements the same portable semantics and is tested
against the same corpus. Cross-compilation proves only that a program builds;
emulation, target hardware, and the Oak OS/STM32 consumers provide execution
evidence appropriate to the package.

## 4. API character

Oak's default public API has the shape of a good Go package: a short package
name, a small set of concrete types, functions whose names describe their work,
and interfaces no larger than the behavior a consumer needs. Oak expresses the
same ideas with ADTs, exhaustive matching, static constraints, effects, and
borrows.

The following rules apply:

- Prefer a concrete parameter when the operation requires a concrete semantic
  type.
- Prefer a structural record or operation constraint for a small, local,
  statically dispatched requirement.
- Give a constraint a named interface when it is shared across packages and has
  a stable semantic meaning or laws.
- A structural constraint and a named interface are compile-time predicates by
  default. Both specialize without boxing, a vtable, or dynamic dispatch.
- Existential or dynamically dispatched values require an explicit type and
  representation; an interface annotation alone never introduces them.
- Do not add a universal abstraction until at least two consumers need to be
  generic over at least three materially different implementations.

Package APIs use qualified names. Fluent calls are appropriate when they retain
the same clear ownership, effect, failure, and cost contract as the qualified
function. Fluent syntax must not make allocation or mutation disappear.

## 5. Bootstrap core and imports

The v1 core import contains only canonical types required across otherwise
independent packages:

```oak
pub Optional[T]: type = Some: T | None
pub Result[T, E]: type = Ok: T | Err: E
pub Ordering: type = Less | Equal | Greater
pub Overflow: type = | Overflow
```

`Optional[T]` represents ordinary absence. `Result[T, E]` represents an
operation that either produces a value or reports a recoverable cause. The
types have one nominal identity throughout a compilation so compiler-generated
checked arithmetic, derivation, and library packages agree.

Oak has no multiple-return feature. When success contains several meaningful
fields, an API returns a named record. When progress and status coexist, it
returns a named domain outcome rather than discarding one fact to fit
`Result`. Anonymous tuple conventions must not become a second multiple-return
mechanism.

The current bootstrap implementation spells `Optional[T]` as `Option[T]` and
also exports byte and collection operations unqualified. That is implementation
history, not the v1 boundary. Byte sequences, bounded bitsets, fixed-width
byte-order conversion, contiguous byte queues/builders, and bounded array lists
now have qualified `bytes`, `bitset`, `endian`, `buffer`, and `array_list`
packages specified by `76-bytes.md` through `81-array-list.md`, with flat
spellings derived only for compatibility.
Migrating
the canonical type name, removing those spellings, and cutting the remaining
operations into qualified packages are explicit pre-v1 work; documentation
must not claim the complete migration is already done.

No filesystem, network, clock, entropy, environment, formatting, collection,
or text service enters every program through the core import.

## 6. Dependency layers

Exact package names in this table are directional until stabilized. The layer
boundaries and dependency direction are normative.

| Layer | Responsibilities and likely packages | May depend on |
| --- | --- | --- |
| Core | `std`: `Optional`, `Result`, `Ordering`, `Overflow` | language primitives only |
| Pure foundation | comparison, numeric helpers, `bits`, `bytes`, `endian`, portable `math` | core |
| Storage and algorithms | `buffer`, array lists, rings, deques, heaps, bitsets, intrusive structures, slabs, arenas, `sort`, deterministic hashes | pure foundation and caller-provided storage |
| Text and data | `strings`, `unicode`, normalization, graphemes, `encoding`, `json`, `url`, `path`, `uuid`, pure calendar/time values | pure foundation and storage algorithms |
| Parallel and machine-portable | `reduce`, `shape`, `tensor`, concurrent rings, portable `simd` consumers | lower freestanding layers and explicit law/memory-model facts |
| Service contracts | I/O, files, networking, clocks, entropy, processes, object storage | lower layers plus explicit capabilities/effects |
| Realizations | simulated, native, freestanding, and target-specific implementations of service contracts | the contract they implement and target packages they name |
| Verification | `testing`, generators, shrinking, deterministic scheduling, simulated storage/time/network faults | public contracts; production packages never depend on test runners |

Dependencies point downward. A cycle indicates a missing lower-level concept or
an overly broad package. In particular:

- pure time values and calendar arithmetic do not depend on a clock;
- deterministic pseudorandom algorithms do not depend on entropy;
- paths do not perform filesystem access;
- codecs do not perform I/O;
- ordinary hashing is separate from cryptographic and constant-time claims;
- portable algorithms do not expose a target ABI in their public signatures.

## 7. The public contract

Every exported operation documents the following facts. A fact enforced by the
type/effect system may be referenced rather than repeated, but it may not be
omitted from the contract.

| Dimension | Required statement |
| --- | --- |
| Meaning | Inputs, result, ordering, canonicalization, and success postconditions |
| Failure | Every recoverable cause; which failures trap; whether failure is atomic |
| Storage | Owners, borrowed regions, pointer provenance/address space/alignment/nullability, mutation authority, initialization, copies, and invalidation |
| Effects | Complete checked effects, including transitive callback or implementation effects |
| Cost | Time/work, span when parallel, auxiliary storage, allocation, copies, blocking, syscalls, and bounds |
| Determinism | Which inputs, seeds, clocks, target facts, or schedules may change the result |
| Concurrency | Required synchronization, permitted callers, memory ordering, progress guarantee, and reclamation rule |
| Security | Input limits, validation boundary, side-channel claim if any, and authority consumed |
| Evidence | Specified, implemented, tested, modeled, proved, and refined status without conflating the stages |

Names reinforce the contract. Use names such as `copy_into`, `encode_into`,
`sort_in_place`, `collect_in`, and `open_with` when they expose material work or
policy. A good name is not a substitute for an effect or cost fact.

## 8. Absence, failure, and progress

Use the smallest result that preserves the semantics:

- `Optional[T]` for search misses, empty-container observations, and other
  ordinary absence with no failure cause;
- `Result[T, E]` for recoverable failure where success and failure are
  disjoint;
- a named ADT for a domain state machine;
- a named record/ADT outcome when progress can accompany end-of-input,
  blocking, cancellation, or failure.

External input, capacity exhaustion, invalid encodings, unavailable resources,
and operating-system failures are recoverable values. A statically knowable
mistake is a compiler diagnostic. A violated internal/programmer invariant may
trap through an attributable assertion. APIs never turn a recoverable failure
into a plausible zero, empty value, sentinel index, or default object.

Failure is atomic by default: observable caller-owned state is unchanged. An
operation that intentionally commits a prefix returns the exact committed or
consumed count on every outcome and documents the resumability rule. It must not
report only the terminal error after losing progress.

Length and offset validation is performed without wrapping the expression being
validated. Prefer subtraction after establishing an ordering, checked
arithmetic, or a proved bound. Untrusted sizes are bounded before allocation,
iteration, indexing, and decompression.

## 9. Pointers, storage, and allocation

Pointers are a first-class part of Oak's systems model. `*T`, views/spans,
owned arrays, foreign pointers, and resource handles are different contracts,
not competing spellings for one value:

- an owned value establishes storage lifetime and destruction/custody policy;
- a view/span establishes a bounded borrow with provenance and read/write
  authority;
- a raw pointer identifies an address but does not by itself establish extent,
  lifetime, initialization, uniqueness, address space, or ownership;
- a handle identifies a resource through its issuing authority and may not be a
  memory address at all.

Pointer-oriented APIs are appropriate for allocators, intrusive structures,
kernels, FFI, DMA, shared memory, memory-mapped devices, boot code, and other
machine boundaries. The standard library must not add an allocation, copy, or
indirection merely to hide a pointer that is part of the domain's real machine
contract.

Raw pointer creation, arithmetic, reinterpretation, and dereference require the
relevant checked derivation or a visible `unsafe` assumption as specified by
`50-borrowing.md`. Converting a pointer and extent into a view/span establishes
a temporary borrow only after alignment, initialization, lifetime, aliasing,
and access authority are proved or explicitly assumed. A pointer is never
treated as an owner merely because it is non-null.

Phantom and GADT indices should define zero-overhead typed pointer/handle
wrappers when they can carry address space, mutability, nullability, alignment,
device, allocation domain, provenance, access width, or custody state. A static
fact erases to the underlying pointer bits; a dynamic fact is represented and
checked honestly. Pointer-to-integer conversion is target-specific and does not
make a pointer a portable serialized value.

Freestanding APIs prefer views for read-only input, spans for caller-authorized
mutation, raw/typed pointers where an extent cannot truthfully be promised, and
explicit state records over caller-owned storage. The ordinary operation does
not grow storage.

An operation that creates or grows storage must identify its storage policy in
its type or arguments and carry `Memory.Allocate`. Suitable policies include a
caller-supplied destination, arena, slab, pool, or explicit allocator
capability. A convenience wrapper may choose a policy only when its name and
effect make that choice visible.

Collection families remain distinct:

1. non-owning algorithms over views/spans;
2. fixed-capacity or caller-backed collections;
3. growable collections parameterized by explicit storage policy;
4. persistent collections only with an explicit owner and measured copying or
   sharing policy.

No single `List` type stands for all four. APIs state whether values are copied,
moved, borrowed, or retained and which mutations invalidate positions, views,
handles, or iterators. Zeroed bytes are not assumed to initialize an arbitrary
`T`.

## 10. Composition without an abstraction tower

Oak takes folds, traversals, builders, and laws from functional libraries, but
introduces them in cost-visible increments.

Sequence algorithms over views/spans come first. A general iterator protocol is
admitted only after its borrow provenance, per-step effects, completion value,
worst-case work per yield, and specialization shape are specified. `map` or
`filter` never implies a new collection: APIs say `map_into`, return a lazy view
with known storage, or accept an explicit builder/storage policy.

A reusable abstraction is admitted only when it has:

- a minimal complete operation set;
- stated algebraic laws where applicable;
- at least three useful implementations and two generic consumers, unless it is
  a fundamental language/compiler contract;
- one predictable specialized machine shape;
- no hidden allocation, blocking, copying, scheduling, or dynamic dispatch;
- tests that apply the same laws to every implementation.

Named laws are semantic claims, not comments. `10-syntax.md` permits an author
to state a law and records an open proof obligation. The supported standard
library applies a stricter release gate: an open obligation may be modeled and
tested, but it does not justify a published optimized realization. A fact used
for optimization is discharged by checked types/refinements, exhaustive
decision, SMT/Lean proof, or another explicit machine-checked artifact.

### 10.1 Low-level and high-level elevations

Important domains should expose two elevations over one semantic engine when
both have real consumers:

- the **low-level API** exposes the incremental machine: explicit state,
  events/visitors, pointers or caller-owned buffers where the domain requires
  them, limits, partial progress, suspension, and exact failures;
- the **high-level API** derives or composes typed whole-value operations over
  that machine: encode/decode, parse/format, collect/build, or direct
  source-to-destination transformation.

The high-level API is not a second implementation. Both elevations share the
same state transitions, errors, validation rules, and proofs. A conformance test
must show that the high-level result is the completed low-level machine result.
Low-level does not mean unchecked: pointer preconditions and unsafe assumptions
remain explicit, and a checked low-level API is preferred whenever its facts are
available.

As in weePickle's visitor-shaped transforms, a source may drive a destination
directly without materializing an intermediate value tree. Oak's version keeps
the source and destination types, effects, storage, and failure in the
signature. `71-codecs.md` supplies the phantom-typed producer/consumer basis for
this shape. A dynamic value/AST remains an explicit useful package for programs
that need inspection or rewriting; it is never a mandatory toll for typed
conversion.

Phantom parameters should distinguish facts such as format, encoding,
validation, ownership domain, endian policy, schema, and protocol phase without
adding runtime fields. GADT result indices may make only legal transitions
constructible and distinguish incomplete, failed, and completed machines.
These facts erase or specialize when static; they must not introduce boxes,
tags, or dispatch that the represented domain does not require.

The high-level elevation remains honest about storage. A caller-buffer form is
the portable baseline. A collecting convenience names and accepts an arena,
pool, allocator, or other storage policy and carries its allocation effect. The
word `high-level` never means ambient allocation, exception throwing, or loss of
partial-progress information.

## 11. Proof-directed performance

Correctness facts are a primary source of performance. Oak prefers making a
fact available to the compiler over adding an unchecked fast API.

```text
reference semantics
  -> checked type/effect/proposition/protocol fact
  -> optimized realization permitted by that fact
  -> correspondence evidence against the reference
```

Examples include:

- a bounds proof removes a bounds check;
- an alignment fact selects aligned loads;
- unique borrows establish non-aliasing;
- validated UTF-8 enables block decoding without revalidation inside the
  validated region;
- exact shape facts select tiled/vector kernels;
- associativity permits regrouping, and commutativity permits reordering;
- a protocol invariant removes an impossible state branch;
- a fixed capacity gives a loop and memory bound.

The optimized path and portable path implement one public semantics. Hardware
dispatch is not permission for different values. Property, differential, and
conformance tests compare realizations; proof or extraction relates the
load-bearing ones to their model.

An `unsafe` assumption is not a proof. A benchmark is not a proof. A proof of a
hand-written model is not implementation refinement. Floating-point arithmetic
does not acquire mathematical associativity because reassociation is faster.

## 12. Authority, nondeterminism, and services

There is no ambient standard-library authority. Filesystem roots, sockets,
clocks, entropy, processes, environment access, devices, and host output enter
through explicit capability values or selected ports with checked effects.

Nondeterminism is likewise explicit:

- a pseudorandom generator is deterministic from its complete state;
- entropy acquisition is a separate effectful service;
- calendar and duration operations are pure;
- reading a clock requires a clock capability and states its error/ordering
  model;
- testing substitutes simulated realizations without changing consumer source;
- iteration order that affects output is specified or parameterized by an
  explicit seed/policy.

Simulation realizations implement the same contract as native realizations and
add controlled faults, schedules, and observations. They must not weaken the
consumer's production contract merely to make a test convenient.

## 13. Text, data, and I/O

Bytes, encoded text, Unicode scalars, and grapheme clusters remain different
semantic levels. Validation is fallible and preserves the input borrow's
provenance. Byte slicing does not manufacture valid text. Normalization,
case-mapping, scalar iteration, and grapheme segmentation state their Unicode
version and expansion/storage bounds.

Codecs are pure transformations over supplied input and output storage. They
report exact consumed/written progress when streaming, reject malformed and
non-canonical forms according to an explicit policy, and never perform I/O.
Canonicalization does not grant filesystem or URL authority and is not a
substitute for application validation.

I/O contracts preserve progress and status together. A read can produce bytes
and reach end-of-input or failure in the same operation; a write can accept a
prefix and then block or fail. Zero progress on a non-empty request has a named
meaning so retry helpers cannot spin forever. `write_all`-style helpers require
an explicit waiting, cancellation, and cumulative-count overflow policy.

## 14. Concurrency and parallelism

A sequential collection is not thread-safe by implication. Concurrent variants
are separate types or packages with an explicit memory model, participant roles,
and progress guarantee such as blocking, lock-free, wait-free, or bounded retry.
Index links alone do not establish liveness, membership, ABA safety, or safe
reclamation.

Ordinary algorithms remain sequential. Parallel execution is requested through
an explicit API or order block whose laws permit its grouping and ordering. The
contract states total work, dependency span, storage, synchronization, numeric
semantics, cancellation, and deterministic-result policy.

## 15. Security posture

Safe standard-library operations have no undefined behavior. Unsafe and foreign
operations are narrow, visible, and state the exact assumption they introduce.
Raw pointers crossing such a boundary state provenance, extent, alignment,
initialization, aliasing, lifetime, address-space, and retention requirements as
applicable; no one pointer property is inferred from another.

Parsers and decoders are designed for hostile inputs: bounded work and storage,
checked size arithmetic, located errors where useful, canonical-form policy,
and no partial mutation unless progress is part of the result. Resource handles
carry identity and generation/liveness facts; wrapping a generation into renewed
validity is forbidden.

Cryptographic, secret-dependent, and constant-time APIs live behind an explicit
contract. An ordinary equality, hash, sort, encoding, or memory operation makes
no side-channel promise. Randomized hashing is not an entropy API, and a digest
is not authentication.

## 16. Package admission and maturity

A package or major API enters the supported standard library only when it has:

1. a focused responsibility and downward-only dependency placement;
2. a complete public contract from section 7;
3. a portable or reference semantics;
4. execution tests for boundaries and failure-state guarantees;
5. property/model/differential tests appropriate to the domain;
6. hostile-input and overflow tests for parsers, codecs, storage, and services;
7. benchmarks for material hot paths, including allocation and code-size data;
8. machine-checked discharge of every fact used to justify a supported
   optimization, plus formal targets for remaining semantic laws;
9. builds and appropriate execution evidence across its declared portability
   profiles;
10. documentation and one representative low-level and high-level consumer when
    the package exposes both elevations;
11. an honest maturity entry using specified, implemented, tested, modeled,
    proved, and refined independently.

Small foundational packages receive the strongest correspondence effort first.
Large catalogs do not become trustworthy merely by accumulating unit tests.

## 17. v1 design sequence

The architecture is applied in this order:

1. settle the `Optional`/`Result`/`Ordering` core identity and migrate
   `Option`;
2. cut the flat bootstrap bytes and collections into qualified freestanding
   packages without changing semantics;
3. publish the public-contract template in generated package documentation and
   make omissions reviewable;
4. stabilize view/span algorithms, bounded storage, text, and codecs;
5. stabilize structural and named constraint vocabulary from real consumers;
6. add allocator-backed conveniences only after the allocation capability and
   failure contracts are complete;
7. validate the freestanding foundation in Oak OS and an STM32-class profile,
   beside macOS and Linux host builds;
8. grow hosted services through replaceable capabilities and simulation;
9. freeze a package only after its proofs, benchmarks, and at least two external
   consumers agree with its shape.

The existing bootstrap implementations are evidence and migration input. They
do not force v1 to preserve an accidental unqualified namespace.

## 18. Required architectural laws

- A freestanding package has no transitive dependency on a capability or target
  realization package.
- A portable operation has one result semantics across all selected target
  realizations.
- A package admitted to a portability profile has no undeclared dependency on a
  target feature or hosted service.
- A structural or named static constraint introduces no runtime representation
  or dispatch by itself.
- A pointer becomes a safe bounded borrow only under proved or explicitly
  assumed extent, lifetime, alignment, initialization, and aliasing conditions;
  the conversion does not manufacture ownership.
- An allocation-free operation performs no transitive allocation, including in
  callbacks selected by its contract.
- Failure atomicity holds unless the result type reports the committed prefix.
- Optimization from a proposition or algebraic law is admitted only after the
  relevant fact is machine-checked, and preserves the reference semantics under
  exactly that fact's hypotheses.
- Simulation substitution preserves the service contract observed by the
  consumer.
- A high-level operation agrees with completion of its low-level machine and
  introduces no storage or effect absent from its contract.
- Evidence maturity is monotone and each stage remains distinct.
