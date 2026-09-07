# Oak standard library: foundations and first slice

Status: discussion draft, not normative specification or implemented API.
Reviewed 2026-09-07 against `SCKelemen/oak` branch `specification`, commit
`6453db54ea02dfbc5903a721967f79739b41c4fc`.
Repository location: `docs/notes/standard-library-design.md`.
The implementation evidence below is a snapshot of that reviewed commit, not a
claim about later branch revisions. Target requirements were clarified afterward.

## 1. Direction

Oak's standard library should combine ML's compositional value APIs with explicit
systems contracts: storage, mutation, failure, effects, and cost. Its foundation
must be useful in freestanding code; hosted facilities should build on that
foundation through explicit capabilities. Fixed-capacity containers are the first
delivery target. Allocator-backed collections remain a later, explicit policy.

This follows Oak's existing [constitution](https://github.com/SCKelemen/oak/blob/6453db54ea02dfbc5903a721967f79739b41c4fc/docs/spec/00-constitution.md)
and [ergonomics/cost specification](https://github.com/SCKelemen/oak/blob/6453db54ea02dfbc5903a721967f79739b41c4fc/docs/spec/05-ergonomics-and-cost.md).
The proposal does not change the language's five semantic axes or add container syntax.

## 2. What to take from the references

These are proposed adaptations, not compatibility promises. External sources were
read through GitHub; most links follow development branches and may change.

| Reference | Useful precedent | Proposed Oak adaptation |
| --- | --- | --- |
| [OCaml Option](https://github.com/ocaml/ocaml/blob/trunk/stdlib/option.mli) | Small algebra of optional values, mapping and binding | Canonical `Option[T]` and `Result[T,E]`; exhaustive matching; combinators with explicit callback costs |
| [Standard ML Basis Option](https://github.com/MLton/mlton/blob/master/basis-library/general/option.sig) | Compact signatures and composable operations | Small, explicit public contracts; ordinary ADTs for absence and failure |
| [Go io](https://github.com/golang/go/blob/master/src/io/io.go) | Reader/writer composition and precise partial-progress rules | Static constraints over concrete implementations; preserve progress together with EOF/error |
| [Deno architecture](https://github.com/denoland/std/blob/main/.github/ARCHITECTURE.md) | Narrow exports, small dependency surfaces, adjacent tests | Importable leaf modules with examples and contract tests; no broad implicit prelude |
| [TypeScript iterator declarations, v5.9.3](https://github.com/microsoft/TypeScript/blob/v5.9.3/src/lib/es2015.iterable.d.ts) | Typed yield/completion results and discoverable signatures | Typed iteration protocols and precise completion states; use Oak ADTs and static constraints |
| [Zig array list](https://github.com/ziglang/zig/blob/master/lib/std/array_list.zig) | Explicit capacity, allocator operations and invalidation documentation | Separate bounded insertion from growth; document storage and borrow invalidation for every operation |
| [SerenityOS CircularQueue](https://github.com/SerenityOS/serenity/blob/master/AK/CircularQueue.h) | Compact fixed-capacity queue implementation | `Ring[T,N]`, but ordinary full insertion returns `Full`; overwriting is a separate operation |
| [Linux list](https://github.com/torvalds/linux/blob/master/include/linux/list.h) | Embedded membership and constant-link-count insertion/removal | Pool/index links, with explicit membership and liveness checks |
| [Boost.Intrusive catalog](https://github.com/boostorg/intrusive/blob/develop/include/boost/intrusive/intrusive_fwd.hpp) | Separate hooks, tags and node/value traits | Typed hook roles and reusable statically resolved link access |
| [TigerBeetle TigerStyle](https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/TIGER_STYLE.md) | Bounded work, startup allocation, assertions and simulation | Bounded container contracts, deterministic operation traces and explicit resource limits |

Do not copy external implementations into Oak as part of this design exercise.

## 3. Existing Oak evidence and gaps

The normative authority is `docs/spec/`. Book chapters and old examples are design
input; executable tests are evidence for the specific paths they exercise.

| Area | Evidence at the reviewed commit | Consequence |
| --- | --- | --- |
| Generic ADTs | `compiler/e2e_generics_test.go` contains Option, Result and checked-conversion execution tests | Establish canonical library type identities; stop requiring examples to redeclare these types |
| Fixed-capacity storage | `compiler/e2e_ring_test.go` uses a generic record and concrete global push/pop functions | This is a representation/operation example, not a reusable generic ring API |
| Intrusive lists | `compiler/e2e_scheduler_test.go` implements concrete enqueue/unlink/dequeue | Extend into a contract with empty/full/membership/reuse cases |
| Generic functions | `book/hierarchies/intrusive.md` and `docs/notes/os-structures-survey.md` record reusable generic functions as a gap | Verify generic function specialization with an executable multi-instantiation probe before publishing generic containers |
| Borrow returns | `docs/spec/50-borrowing.md` documents conservative rejection of view/span return signatures | Returned views, text validation wrappers and borrowed iterators need provenance-preserving return support |
| Resource ownership | The borrowing spec documents aggregate value copies and deferred move/consume semantics | Do not model files, pools or unique owners as freely copyable records and claim ownership enforcement |
| Closures | `docs/spec/60-effects-allocation.md` rejects capturing closures pending storage justification | Early algorithms may use direct loops or explicit state; do not promise closure-based pipelines yet |
| I/O and strings | `examples/io/io.oak` has a placeholder `copy_all`; `examples/strings/strings.oak` has placeholder validation/recode bodies | Reconcile their API ideas, but do not promote these files as working stdlib |

The status matrix still describes checked conversions as awaiting generic Result
lowering, while `e2e_generics_test.go` contains a test for that newer path. Resolve
this discrepancy by running the tests before updating maturity claims. Tests
were inspected, not executed in this review; a checkout was unavailable.

## 4. Proposed module boundary

Names below are design names, not frozen import syntax. Begin with one stdlib
version released with the compiler; keep module boundaries small without adding
independent package-version coordination yet.

| Layer | Initial modules | Dependency rule |
| --- | --- | --- |
| Values and algorithms | `option`, `result`, `cmp`, `num`, `bits`, `slice`, `bytes` | No OS, allocator, scheduler or global mutable state requirement |
| Storage and collections | `mem`, `collections`, `intrusive` | Explicit storage and authority; bounded forms first |
| Text and representation | `strings`, `encoding`, `fmt` | Build on bytes and caller buffers; text validity is preserved |
| Protocols | `iter`, `io` | Concrete state plus static constraints; carry effects of callbacks/implementations |
| Hosted services | `fs`, `net`, `process`, `time`, `random` | Explicit capabilities; target adapters are below the API |
| Verification tools | `testing` | Deterministic seeds, operation traces, failure injection; no production dependency on a test runner |

Compiler-known `c`, `simd` and `arm64` surfaces retain their current identity.
Portable APIs may select their implementations, but portable modules must not
require an architecture-specific import from users.

Bootstrap the prelude with only the agreed canonical value types and essential
language support. Defer hash tables, persistent collections, intrusive trees,
Unicode normalization/grapheme tables, networking protocols and async execution
until their dependencies and invariants have concrete implementations.

## 5. Public API contract

Every exported operation must state:

1. Semantic inputs/results, including absence and each recoverable failure.
2. Storage ownership, mutation authority, borrow provenance and invalidation.
3. Required effects and capabilities, including transitive callback work.
4. Time complexity and bounds, auxiliary storage, element-copy cost and allocation.
5. Success postconditions and exact state left by failure.
6. Safety preconditions, concurrency guarantees and maturity evidence.

Use `Option` for ordinary absence; use `Result` for failure with a cause. Domain
states should use named ADT variants. Programmer-invariant violations may trap;
external input and expected capacity exhaustion should produce recoverable results.
Never replace a diagnostic with a plausible default value.

Prefer names that expose material work: `copy_into`, `encode_into`,
`collect_into`, `sort_in_place`, and explicit allocation/growth operations.
Names supplement checked effects; they do not replace them. An allocation-free
operation may still perform substantial work or copy a large value.

Sequence algorithms come before a universal iterator abstraction. `map_into`
must specify output capacity, partial writes, callback failure and aliasing.
`fold` must include callback cost. A lazy `filter` can inspect many elements per
yield: allocation-free does not mean constant-time or bounded without an input bound.

## 6. First container contracts

Start with `Ring[T,N]`, `BitSet[N]`, and a fixed pool with checked handles. A
fixed vector can follow the same initialized-prefix discipline. This section
specifies semantics; generic signatures and mutable receiver syntax remain open.

### Ring

Require `N > 0`. Logical contents are a FIFO sequence of length `0..N`.

| Operation | Result | State guarantee | Work excluding element transfer |
| --- | --- | --- | --- |
| `try_push` | Success or `Full` | Append on success; unchanged when full; failed insertion retains caller's value | O(1) |
| `pop` | `Some(value)` or `None` | Remove oldest element; unchanged when empty | O(1) |
| `front` | Borrowed oldest element or absence, once supported | No mutation; borrow prevents conflicting modification | O(1) |
| `clear` | Unit | Empty; element cleanup follows the eventual resource contract | O(length) when cleanup is required |

Storage is O(N × size(T)) plus cursors/length and any initialization metadata.
Only occupied slots may be read. Zeroed bytes are not a valid generic initializer
for every T. The first implementation can use tagged optional slots, with their
measured representation cost, or restrict its pilot to supported element types;
an uninitialized-storage optimization needs a separate safety argument.

Compute wraparound without overflowing the cursor type before reduction.
Document capacity/index representability. Reject-full is the ordinary policy.
If later provided, `push_overwrite` must explicitly report any displaced value.
The initial ring requires exclusive access; it is not an SPSC or MPMC queue.

### BitSet

Expose test/set/clear and first-set search with explicit index bounds. Bits above
N in the final storage word are always zero. Set/clear/test touch O(1) words;
first-set visits at most the storage word count. Cover N=0, partial final words,
and word-aligned capacities. Until const arithmetic in types is implemented,
backing-word dimensions must be explicit and checked rather than assumed.

### Pool and handles

A handle identifies a pool instance, slot and generation. An element type alone
does not identify a pool. Resolution succeeds only for the issuing pool, a live
slot, and the current generation. Free invalidates the handle. Generation
exhaustion retires the slot or fails closed; it never wraps into validity.

Construction must create a distinct pool identity. A fresh static brand could
serve this role when the language can enforce generativity; until then use a
checked runtime identity or limit the pilot to explicitly unique static pools.
Do not claim that a user-written phantom tag alone prevents duplicate identities.

Outstanding borrows must prevent freeing/reusing their slot. Identity checking
does not itself enforce borrow lifetimes or forbid copying a pool owner.

## 7. Intrusive membership

Use the existing pool/index doctrine and add a distinct hook role per membership,
for example ready-queue versus timer-queue membership. A single live object may
carry both hooks. A hook may belong to at most one container instance at a time.
Role identity alone does not distinguish two ready queues.

Each hook needs explicit detached/linked state and sufficient container identity
to reject wrong-container removal. Singleton membership cannot be inferred from
`next` and `prev` both being absent. Insertion checks pool identity, liveness and
detached state before mutation. Removal checks membership and restores detached
state. Failed checked operations leave all structures unchanged.

O(1) unlink requires O(1) membership evidence; searching the list first is O(n).
Freeing an element while any hook remains linked must be rejected or performed by
an explicit operation that removes every membership. Bounds-checked indices alone
do not establish liveness, acyclicity, membership or correct generation reuse.

For the first list, use exclusive access and checked membership. Mutable
iteration and concurrent reclamation are later protocols with their own
invalidation and memory-order contracts. Do not label index links intrinsically
thread-safe, lock-free or ABA-safe.

## 8. I/O and text contracts to settle next

An I/O result must carry progress alongside status. Use a conceptual read outcome
`(count, status)` where status is `Continue`, `End`, `WouldBlock`, or `Failed(E)`.
The destination prefix of length count is initialized and meaningful on every
outcome. A read can deliver bytes and report EOF/error together. Writers likewise
report bytes accepted together with continuation, blocking, or failure status.

Specify zero-length behavior separately. A nonempty request with zero progress
must not cause an unbounded retry loop. `write_all` and copy helpers must handle
short writes, preserve cumulative progress on failure, and require explicit
waiting/cancellation policy. Their aggregate byte counters need overflow handling.
No generic reader/writer contract alone promises allocation-free or nonblocking
behavior; the concrete implementation's effects determine that.

Preserve `string = Str[Utf8]`. Validation is fallible and lifetime-preserving;
byte slicing produces bytes unless character-boundary/validity conditions are
established. Separate code-unit length, scalar iteration and grapheme iteration.
Re-encoding requires caller storage or an explicit allocator and reports consumed
input/produced output when streaming. Never implement recoding by changing an
encoding tag. Follow the existing [text specification](https://github.com/SCKelemen/oak/blob/6453db54ea02dfbc5903a721967f79739b41c4fc/docs/spec/70-strings.md).

## 9. Implementation sequence and acceptance gates

| Step | Deliverable | Acceptance evidence |
| --- | --- | --- |
| 1 | Canonical Option/Result/Overflow identity and module loading contract | Cross-module imports resolve one nominal type; checked conversions use it; conflicting local names are diagnosed or resolved correctly |
| 2 | Generic function and mutable-container probes | Two element types and two capacities specialize and execute correctly; receiver mutation updates original storage; no accidental whole-container copying |
| 3 | Ring, then BitSet | Execution tests for empty/full/wraparound, capacity one, partial words, unchanged-on-failure and overflow boundaries; randomized bounded traces against a simple reference model |
| 4 | Pool and first intrusive list | Wrong pool/container, duplicate insert, detached remove, singleton, head/tail/middle removal, stale handles, generation exhaustion and multi-hook traces |
| 5 | Borrow returns, byte algorithms and validated text | Positive caller-owned return cases and negative lifetime/aliasing cases; exact output counts and invalid-input tests |
| 6 | Reader/writer adapters and formatting into buffers | Short read/write, bytes-plus-error, EOF, zero progress, would-block, cancellation and undersized-buffer tests |

Inject clocks, randomness and I/O when they arrive so deterministic simulation can
control them. For the first pure containers, seeded operation traces suffice;
distributed simulation infrastructure is not a prerequisite.

Track specified, implemented, tested, modeled, proved and refined separately,
as Oak already requires. Proposed Lean targets are FIFO preservation, occupancy,
bitset tail invariants and handle/membership transition laws. Execution tests that
mirror a model do not establish a machine-checked implementation refinement.

The first review decision is whether to adopt this bounded foundation and module
boundary. The first coding task is the canonical types/module contract and generic
mutation probes; those determine how the reusable ring API can honestly be spelled.

## 10. Apple Silicon systems target

The initial target is Apple Silicon M-series hardware, serving the hypervisor
and kernel in [SCKelemen/os](https://github.com/SCKelemen/os) and the database
identified by the user as [SCKelemen/db](https://github.com/SCKelemen/db).
The OS documents also reference `SCKelemen/dbs`; that repository identity remains
to be confirmed before importing database-specific requirements. The database
guidance here is a proposed storage contract, not a claim about its implementation.

The [OS architecture](https://github.com/SCKelemen/os/blob/main/docs/rfcs/0001-hypervisor-os.md)
places capability authority and stage-2 custody at EL2, an application-host kernel
at EL1, and native services at EL0. Its [capability IDL draft](https://github.com/SCKelemen/os/blob/main/docs/rfcs/0002-capability-idl.md)
calls for bounded messages and typed resource transfer. These motivate a
freestanding foundation with explicit authority and no mandatory hosted runtime.
They do not establish that these protocols are already implemented in Oak.

### Generics without boxing

Generic types and functions should specialize into concrete layouts and direct
operations. `Ring[u8,64]` contains inline element storage; `Option[T]` and
`Result[T,E]` use inline discriminants and payloads unless another checked
representation is selected. Generic constraints do not introduce implicit
runtime interface objects. Phantom type/authority distinctions require no fields
when their facts are entirely static.

Storage placement is independent: stack, static, caller-owned, or explicitly
allocated. Neither generics nor pointer authentication require heap allocation.
Specialization can increase code size, and by-value aggregate operations can copy
large payloads. Mutable container APIs must preserve caller storage identity and
make those costs visible.

### Pointer tags and authentication

Pointer tagging is a representation optimization for values that already contain
pointers. Inline values need not acquire an indirection to carry a tag. Low bits
may hold discriminators when alignment guarantees their availability and the
backend removes them correctly before access. High bits must not be allocated
independently of the address-translation and authentication configuration.

Apple documents PAC support on Apple Silicon and its use through the `arm64e`
ABI. Our freestanding ABI must define its own supported profile, while honoring
external ABI contracts at interoperability boundaries. See
[Apple pointer authentication](https://developer.apple.com/documentation/security/preparing-your-app-to-work-with-pointer-authentication)
and [Clang's authentication model](https://clang.llvm.org/docs/PointerAuthentication.html).

A PAC authenticates a pointer using a key and context; its bits are not arbitrary
software tag storage. A type or authority-domain discriminator may contribute to
that context under a specified scheme. PAC does not itself provide bounds,
read/write permissions, revocation, or CHERI-style hardware capabilities.

Before assigning a bit layout, the target profile must specify:

1. Supported hardware features, address widths, translation configuration and
   separate instruction/data pointer representations; unsupported required
   authentication must fail closed rather than silently weaken the contract.
2. Tag encoding, signing and authentication order, and which semantic metadata
   is authenticated. Stripping a PAC is not authentication.
3. Key ownership, access to signing operations, key initialization and isolation,
   and save/restore rules across threads, cores, guests and exception levels.
4. Whether authentication is bound to a storage address; copying or relocating
   such a reference may require authenticated re-signing.
5. Legal authority narrowing, authenticated boundary conversions, failure
   behavior, and FFI handling. Raw integer conversion must not silently mint
   trusted references or erase their provenance.

No exact PAC width, spare-bit budget, MTE availability or universal M-series
layout is promised by this draft. These require a concrete, validated machine
profile and execution tests on the target hardware.

### Authority and persistence

| Use | Proposed representation and enforcement |
| --- | --- |
| Reference within one protection domain | Borrowed reference; optional PAC and checked tag packing under the target profile |
| Cross-domain capability | Typed handle resolved against protected identity, rights, ownership and revocation state |
| Persistent database reference | Stable object/page identity or offset, validated against its storage format and lifetime |

A privilege tag describes authority; it does not grant CPU privilege. The
checker, capability validation, translation permissions and protected entry
points enforce the corresponding obligations. Code with access to the relevant
signing operations is part of the PAC threat model.

An authentic pointer may still refer to revoked authority or reused storage.
Capability resolution therefore retains explicit revocation/liveness checks;
PAC cannot replace them. The OS's synchronous revocation contract must also
cover in-flight requests and completion of the relevant isolation transitions.

Persist identifiers and offsets rather than process addresses or PAC-bearing
pointers. Recovery validates the persistent representation and reconstructs
current in-memory references. Durable authorization and data integrity require
their own protocols; they do not inherit security from a previous execution's PAC.

### Systems acceptance work

After the exclusive-access ring and pool foundation, add the OS's bounded SPSC
transport profile as a distinct concurrent protocol. Specify release/acquire
publication, counter wraparound, slot ownership, hostile peer validation,
revocation, and notification behavior; an ordinary ring is not automatically a
safe cross-domain transport. Exercise negative cases as well as throughput.

Capability resource transfer needs move/consume semantics and runtime boundary
validation. Compiler-level move checks alone cannot police an untrusted peer.
For database-facing bytes and records, add explicit endian encoding, length and
offset overflow checks, malformed-input rejection, and deterministic recovery
tests. Neither transport nor storage should depend on native pointer bit layouts.
