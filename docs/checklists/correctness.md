# Correctness checklist

Everything that must be true. One flat list, grouped by where the question
bites. Each item is a question; "no" is a finding. See [README](README.md)
for the shape of an item and how to run a pass.

Sources, abbreviated in parentheses: TigerStyle/TigerBeetle (TB), NASA
Power of Ten (P10), MISRA C (MISRA), Rust, Zig, Odin, Go, Swift, Elm, the
ML family (ML), Scala, Futhark, Mojo, Idris, Coq, Lean, TLA+, Apalache, Z3,
simdjson, simdutf, Hyperscan, data-oriented design (DOD), langsec.

---

## 1. Principles the rest depends on

- [ ] **Correctness first.** When a design trades correctness for speed or
      simplicity, is the trade written down and rejected? A faster design
      whose invariants cannot be stated and checked is not acceptable.
      (constitution) — Oak: `00-constitution.md` Priorities.
- [ ] **One fact, many projections.** Does every semantic fact — field
      order, a refinement, a protocol transition, a layout — have exactly
      one authoritative statement from which type checking, layout, proof
      assumptions, runtime checks, tests, and debugger output are derived?
      Is the compiler ever reconstructing a lost fact by guesswork?
      (constitution, Idris/Lean: definition once, theorems many) —
      Oak: `00-constitution.md`, `125-verification.md` §1.
- [ ] **Five axes stay separate.** Does a feature overload one axis (type,
      representation, authority, proposition, protocol) to smuggle in
      another — a doc tag that changes ABI, a default that acts as a wire
      discriminant? (constitution) — Oak: `00-constitution.md`.
- [ ] **Safe by default, unsafe visible.** Can safe code reach undefined
      behavior by any ordinary operation? Does every unsafe operation cross
      a syntactically visible boundary that records exactly which
      assumption it introduces, leaving every unrelated invariant checked?
      (Rust, Zig, constitution) — Oak: `00-constitution.md`,
      `50-borrowing.md`, `OAK-B0110`/`OAK-B0122` recorded assumptions.
- [ ] **No hidden work.** Does any ordinary operation silently allocate,
      block, do I/O, take a contended lock, dispatch dynamically without
      bound, or copy unbounded data? Hidden work is a correctness problem
      before it is a performance one: it is an effect the checker cannot
      see. (constitution, Zig) — Oak: `00-constitution.md`,
      `60-effects-allocation.md` §3.
- [ ] **Machine semantics are semantics.** Are width, overflow behavior,
      alignment, endianness, pointer size, atomics, and volatile access
      specified as language semantics rather than left to a backend? Is a
      mathematical integer ever confused with a machine integer?
      (constitution, MISRA essential types) — Oak: `00-constitution.md`,
      `20-types.md` §11.
- [ ] **Sugar normalizes to a core.** Does every surface convenience lower
      to a smaller core with one semantics, or does it create a parallel
      semantics that must be kept in sync by hand? (constitution, Elm's
      small core, Scala's desugaring pitfalls) — Oak: `00-constitution.md`
      Syntax equivalence.
- [ ] **Fail closed on unknowns.** When the checker cannot know something
      — the effects of a call through an unknown value, the independence of
      loop iterations, the layout of a foreign type — does it reject rather
      than assume? (TB, P10 rule 10) — Oak: `60-effects-allocation.md` §2
      (`OAK-E0103`), `55-parallelism.md` §2.

## 2. Specify and model before you build

- [ ] **Design document first.** Is there a written statement of what the
      component must do, its invariants, and its failure modes, before
      code? TB: the time spent designing is the cheapest time in the
      project. (TB) — Oak: `docs/spec/` is normative; legacy docs retire
      only after reconciliation (`docs/spec/README.md`).
- [ ] **Five layers named.** For the feature, which of surface syntax,
      static semantics, dynamic/machine semantics, formal model, and
      implementation correspondence exist, and which are missing? Is the
      maturity stated with the exact vocabulary — specified, implemented,
      tested, modeled, proved, refined — and never rounded up? (Lean, Coq,
      constitution) — Oak: `docs/spec/README.md`, `STATUS.md`.
- [ ] **A proof of the model is not a proof of the compiler.** Where a
      Lean or TLA+ result is cited, is the gap to the implementation
      stated: extraction faithfulness, refinement, or differential testing
      against the model? (Coq/CompCert lesson, TB's "simulation is a
      witness, not a proof") — Oak: `00-constitution.md` Verification
      discipline, `95-extraction.md`, `125-verification.md` §3.
- [ ] **Invariants stated, not implied.** Does every stateful component
      write down its invariants as predicates over its state — the TLA+
      `TypeOK` plus safety properties — in a form a test, an assertion, and
      a model checker can all consume? (TLA+, TB) — Oak:
      `112-protocols.md` (invariant obligations, `oak prove`).
- [ ] **Inductive, not just true.** Is the stated invariant inductive
      (preserved by every step from any state satisfying it), or merely
      true of reachable states? A non-inductive invariant will not
      discharge in Apalache or Lean and hides which step is dangerous.
      (TLA+, Apalache) — Oak: `125-verification.md` §2a.
- [ ] **Temporal properties separated from safety.** Are liveness and
      fairness stated separately from safety, with the fairness assumption
      explicit? Most bugs are safety bugs; most unprovable claims are
      liveness claims with hidden fairness. (TLA+) — Oak: `112-protocols.md`
      §7 direction.
- [ ] **Small model, then big test.** Was the protocol model-checked with a
      small finite instance (two or three nodes, tiny data) before being
      property-tested at scale? Exhaustive on the small model, statistical
      on the large one. (TLA+/TLC, Apalache bounded symbolic) — Oak:
      `112-protocols.md`, TLA+ export.
- [ ] **Refinement mapping written.** Where an optimized implementation
      claims to implement a simpler specification, is the refinement
      mapping (abstraction function from concrete to abstract state)
      written down and checked, not argued? (TLA+, Lamport; Coq) — Oak:
      `112-protocols.md` §4a conformance, `STATUS.md` refinement policy.
- [ ] **Decidable fragment chosen deliberately.** For each obligation sent
      to an SMT solver, is it in a decidable fragment (linear integer
      arithmetic, bit-vectors, arrays) so the answer is yes/no rather than
      unknown/timeout? Quantifiers and non-linear arithmetic are where
      solvers become oracles. (Z3, Apalache) — Oak: `125-verification.md`
      §3 discharge ladder.
- [ ] **Counterexamples are first-class.** When a check fails — pattern
      exhaustiveness, a protocol invariant, a property test — does the tool
      hand back a concrete, minimal counterexample the author can run?
      (TLA+, Elm, property testing) — Oak: `35-pattern-analysis.md`,
      `110-testing.md` shrinking, `15-diagnostics.md`.
- [ ] **Assumptions have an audit trail.** Is every admitted assumption
      listed in one place, reviewable, and stated as a theorem the proof
      layer could later discharge? An assumption that is not listed is a
      hidden axiom. (Lean `sorry`, Coq `Admitted`, TB) — Oak:
      `85-discipline.md` §7 `admit`, `oak vet`, `:obligations`, `:lean`.

## 3. Make illegal states unrepresentable

- [ ] **Sum types for alternatives.** Are mutually exclusive states a
      closed ADT rather than a record with flags and nullable fields whose
      combinations are mostly invalid? (Elm, ML, Rust, Swift) — Oak:
      `30-adts-patterns.md`.
- [ ] **Exhaustive matching, no default arm.** Is every match over a sum
      exhaustive without a wildcard, so adding a constructor is a compile
      error at every consumer? Is redundancy also an error? (Elm, ML,
      Rust, Swift; MISRA's "every switch has a default" is the weaker C
      form) — Oak: `35-pattern-analysis.md`.
- [ ] **No null.** Is absence `Option[T]`, with no nullable reference,
      sentinel integer, or zero-length-means-missing convention? (Elm,
      Rust, Swift, Odin/Zig optionals) — Oak: `30-adts-patterns.md` §1a,
      hypervisor note ask 9.
- [ ] **Errors are values.** Does fallible code return `Result[T, E]` with
      a closed error type, rather than throwing, returning a status code
      the caller may ignore, or returning an in-band sentinel? Where a
      register-return ABI justifies a status word internally, is the
      sentinel confined to private helpers and the justification written?
      (Rust, Go, Zig error unions; simdutf `convert_*` returning 0 and
      `result.count` meaning position or written are the anti-pattern) —
      Oak: `20-types.md` §11.1a, `resource-contracts-and-results.md`;
      `stdlib/json.oak` `json_result_value` and `JsonIntegerScan.status`
      are internal sentinels justified in `71-codecs.md` §18.
- [ ] **Newtypes for identities and units.** Are ids, offsets, byte
      counts, element counts, durations, and monetary amounts distinct
      types so that an offset cannot be passed as a length? Are units in
      names when the type does not carry them (`timeout_ms`)? (TB, Rust,
      F# units of measure, Haskell newtypes) — Oak: `80-metadata.md`
      phantom semantic types, `20-types.md` nominal identity.
- [ ] **Validated state lives in the type.** Once input is validated
      (UTF-8 checked, JSON parsed, signature verified), is the fact carried
      as a phantom type parameter or a distinct type so it cannot be
      re-validated or skipped by accident — "parse, don't validate"? Is
      the validated type constructible *only* through the validator?
      (Alexis King, simdjson, Idris) — Oak: `71-codecs.md` §2, §6;
      `70-strings.md`.
- [ ] **Typestate for protocols.** Where a value must be used in a fixed
      order (open→read→close, Host→Device custody), is the state an index
      on the type so a misordered call fails to compile, with the index
      erased at run time? (Rust typestate, Idris, session types) — Oak:
      `112-protocols.md` §5a, `Oak.Typestate`, `92-ffi.md` §2.8.5.
- [ ] **Refinements over raw scalars.** Where an integer must be nonzero,
      in range, aligned, or a power of two, is that a proposition the
      checker knows (and elides checks from) rather than a comment?
      (Idris, Liquid Haskell, Z3-backed refinement) — Oak: proposition
      axis, extent facts in `50-borrowing.md`, `20-types.md`.
- [ ] **Sizes in types.** Are fixed capacities const parameters
      (`[N]T`, `Ring[T, N]`) rather than runtime fields checked at every
      access? Are size relations (`[M*K]T`) folded at instantiation?
      (Futhark size types, Idris vectors, Zig comptime, Rust const
      generics) — Oak: `20-types.md` §11.0.
- [ ] **Effects in types.** Does a function's type say what it may do
      (allocate, block, read host memory, touch a device) so a caller's
      `forbids` sees through the call, including through function values?
      (Koka, effect rows; TB's "no allocation after init") — Oak:
      `60-effects-allocation.md` §2, §2a.
- [ ] **Uniqueness or ownership for in-place update.** When a function
      mutates its argument in place, does the type system guarantee no
      other reader sees the mutation — uniqueness types, `&mut`, or a
      consuming parameter mode? (Futhark uniqueness, Rust `&mut`, Clean)
      — Oak: `50-borrowing.md`, receiver/parameter modes.
- [ ] **Closed by default.** Are types, modules, and enumerations closed
      unless explicitly opened, so exhaustiveness and layout facts hold?
      Is `pub` opt-in and `pub(opaque)` available so representation does
      not leak? (Elm, Rust, Go, Swift `final`) — Oak: `83-modules.md`.
- [ ] **No implicit conversions.** Is every change of width, signedness,
      or numeric kind spelled out, with truncating, saturating, checked,
      and bit-reinterpreting forms distinct? (Swift, Rust, MISRA essential
      types, Go) — Oak: `20-types.md` §11.1.
- [ ] **Literals are typed exactly.** Does an out-of-range literal fail to
      compile rather than wrap or promote? Do integer constructors over
      literals fold without changing meaning? (Rust, Swift, MISRA) — Oak:
      `25-type-inference.md` §3a.
- [ ] **Structural sharing is explicit.** Does the type distinguish a view
      (borrowed, read-only), a span (borrowed, writable), an owned value,
      and a handle (index into an owner), with no implicit conversion from
      owned to borrowed that outlives the owner? (Rust, Zig slices, Odin)
      — Oak: `50-borrowing.md`, `60-effects-allocation.md` §8.

- [ ] **Wire identities are declared, not derived from source names.** Does
      a discriminator value or field key ever default to a type or field
      name, so a rename changes the wire format? Is discriminator-name
      consistency across a hierarchy checked at compile time? (weePickle
      FQCN default tag, runtime `findTagName`) — Oak: `40-records.md`
      tags, `30-adts-patterns.md`; ADT wire tags are not derived yet — not
      stated.
- [ ] **Defaults consumed by a codec are pure constants.** If a
      construction default can be omitted on write or filled on read, is it
      required to be a compile-time constant so omission is deterministic?
      (weePickle re-evaluates defaults per write for `currentTimeMillis`)
      — Oak: `40-records.md` construction defaults; purity requirement not
      stated.
- [ ] **Callback-scoped borrows are regions, not comments.** When a parser
      hands a consumer a view into a reusable buffer, is "valid until the
      buffer refills" a borrow the checker enforces, with refill a mutable
      borrow that conflicts with any live view? (weePickle
      `TextBufferCharSequence` "VERY MUTABLE BUFFER"; simdjson
      `string_view` lifetimes) — Oak: `50-borrowing.md` §8c and
      `71-codecs.md` §13a for whole inputs; streaming refill is design
      work (`71-codecs.md` §16).
- [ ] **Root metadata has copies with intersecting quorums.** Is
      fixed-position root state stored as N copies, written to a write
      quorum and opened from a read quorum with write + read = N + 1, the
      copy index outside the checksum, sequence plus parent checksum
      ordering versions, and broken copies repaired on open? (TB
      `superblock_quorums.zig`) — Oak: not stated.
- [ ] **Staging is never externalized.** Is state that is not yet durable
      held apart from working state, so no reply, ack, or in-memory
      guarantee depends on it? (TB `superblock.zig` `working`/`staging`)
      — Oak: `120-io.md` §3 durability clause; the program-side rule: not
      stated.
- [ ] **Checksums point outward.** Is every block reached by pointer
      checksummed by its parent (address, checksum pairs), with
      self-checksum reserved for the root, so a misdirected write of
      well-formed data is detected? (TB `BlockReference`, `data_file.md`)
      — Oak: not stated.

## 4. Memory, ownership, and aliasing

- [ ] **Every access bounds-checked or proven.** Is every indexed access
      either checked at run time or discharged by a fact the checker holds
      (`i < len`)? Is the elided check recorded as a proof obligation, not
      a flag? (Rust, Zig, Swift, TB) — Oak: `50-borrowing.md` extents,
      `56-kernels.md` §3 (elision open).
- [ ] **No dangling, no use-after-free, no double free.** Is every borrow
      bounded by its owner's region, every consuming operation invalidating
      its binding, every owner freed exactly once? Is this checked, not
      convention? (Rust, Cyclone regions) — Oak: `50-borrowing.md` §8c
      regions, `Oak.Escape`.
- [ ] **Mutable aliasing forbidden.** Can two live paths write the same
      memory without an atomic or a proven disjointness fact? Are
      writable-disjointness assumptions on unsafe blocks recorded?
      (Rust, Futhark, MISRA restrict) — Oak: `50-borrowing.md`,
      `OAK-B0110`.
- [ ] **No uninitialized reads.** Is every variable, field, and buffer
      element initialized before any read, including padding that a
      serializer might copy? Is "zero is a valid value" true for every
      zero-initialized type, or is zero-init forbidden for that type?
      (Rust, Zig `undefined` is explicit, MISRA 9.1, TB) — Oak:
      `60-effects-allocation.md` §10a static initializers.
- [ ] **Alignment and layout are facts.** Is every record layout derived
      from one stated rule, exposed via `size_of`/`offset_of`, asserted in
      the emitted code, and ratified against the C compiler? Do `(align:
      N)` annotations produce an emitted assertion? Is a padding-free,
      unique-representation predicate asserted for every record compared
      by bytes or written to a device, with checksum fields at 16- or
      32-byte offsets asserted? (Zig, Rust `#[repr(C)]`, DOD, TB
      `stdx.no_padding`) — Oak: `40-records.md` §6a–§6b,
      `45-representations.md`, `92-ffi.md` §2.6; the predicate: not
      stated.
- [ ] **Endianness explicit at every byte boundary.** Is every multi-byte
      read or write from a byte buffer through a named-endianness function
      that returns a result, never a cast or a reinterpret? (TB, MISRA,
      Zig `readInt`) — Oak: `bytes_read_*_le/be` in `stdlib/std.oak`,
      hypervisor note ask 12.
- [ ] **Pointer arithmetic only in unsafe, and rarely.** Does safe code
      compute offsets over views and spans, with pointer arithmetic
      confined to the FFI and MMIO layers under a recorded contract?
      (P10 rule 9, MISRA 18.x, Rust) — Oak: `92-ffi.md`, `96-aarch64-mmio.md`.
- [ ] **Handles over pointers, with generations.** For pooled objects, is
      the reference a typed index plus a generation counter so a stale
      handle is detected rather than dereferencing freed storage?
      (DOD, TB, Andre Weissflog's handles) — Oak:
      `60-effects-allocation.md` §8, `standard-library-design.md` §6.
- [ ] **Capacity is declared, exhaustion is a value.** Does every
      fixed-capacity container declare its capacity and return a result on
      exhaustion rather than growing or trapping? Is the capacity a
      written sum of named per-consumer maxima, asserted sufficient for
      progress, rather than a round number? (TB static allocation,
      `message_pool.zig`, P10 rule 3) — Oak: `60-effects-allocation.md`
      §6–§9, `85-discipline.md` §4; the sum discipline: not stated.
- [ ] **Resource cleanup is guaranteed and ordered.** Is every acquired
      resource released on every path, including error paths, in reverse
      acquisition order, with the release visible at the acquisition site?
      (Zig/Go `defer`, Rust `Drop`, Odin) — Oak: `defer` in
      `10-syntax.md` (block-scoped, one statement); terminal-state
      obligations in `112-protocols.md`.
- [ ] **Foreign memory is a contract, not a type cast.** Does every buffer
      that crosses the FFI carry pointer, count, and ownership as a typed
      triple, with the foreign side's aliasing and lifetime assumptions
      recorded per borrow? (Rust FFI, Zig extern, Swift unsafe pointers) —
      Oak: `92-ffi.md` §2.6–§2.8, `c.borrow`.
- [ ] **Custody across devices is a state, not a comment.** When memory
      moves between host and device, or between processes, is the custody a
      typestate whose transition is the only place the side effect can
      occur? (mlx unified memory pitfalls, CUDA) — Oak: `92-ffi.md`
      §2.8.5 `Buffer[T, S]`.
- [ ] **MMIO and volatile are effects with barriers.** Is every device
      register access typed (width, access kind, side effect), volatile,
      ordered by an explicit barrier, and never merged, reordered, or
      elided by the optimizer? (MISRA volatile, Linux kernel memory
      barriers doc) — Oak: `65-machine-memory.md` §9, `95-aarch64-barriers.md`,
      `96-aarch64-mmio.md`.
- [ ] **Wire and disk records have no implicit padding, and reserved bytes
      are zero on both sides.** Is every on-disk or on-wire record declared
      with a layout clause and asserted padding-free, with reserved fields
      asserted zero before write and checked zero after read, and paddings
      zeroed before they reach a device ("buffer bleed")? (TB
      `stdx.no_padding`, `Header.invalid()`, `journal.zig`) — Oak:
      `40-records.md` §6a `struct(no_padding)` (checked, `OAK-R0301`,
      wire-safe field shapes), `struct(packed)`, §6b `static_assert`;
      reserved field zero checks: not stated.
- [ ] **Reserved slots name their own address.** Does an empty slot in a
      ring or table carry its own index (as the op, address, or copy
      number) so a misdirected read of a valid-looking empty slot is
      detected? (TB `journal.zig` reserved headers, `SuperBlockHeader.copy`)
      — Oak: not stated; the dbs frame scan needs it.

## 5. Control-flow and coding discipline

- [ ] **Every loop has a static bound.** Does each loop carry a bound the
      compiler can see (canonical counter, declared bound with runtime
      guard, or a ranking function proven decreasing), so a runaway loop
      is impossible by construction? (P10 rule 2, TB, MISRA 14.x) — Oak:
      `85-discipline.md` §3, `OAK-D0103`, `Oak.BoundedLoop`.
- [ ] **Recursion is bounded or absent.** Is stack depth statically
      bounded — tail calls lowered to loops or trampolines, stack-consuming
      cycles rejected, declared depth bounds with runtime checks otherwise?
      (P10 rule 1, MISRA 17.2, TB) — Oak: `85-discipline.md` §2,
      `Oak.Discipline`.
- [ ] **No allocation after initialization.** Does every steady-state
      entry point (event loop, request handler, interrupt path) forbid
      allocation, with the compiler rejecting any reachable allocation
      including through externs? (P10 rule 3, TB, MISRA 21.3) — Oak:
      `85-discipline.md` §4, `steady` manifest lines, `OAK-E0104`.
- [ ] **Functions are short and do one thing.** Is any function over
      seventy lines, or doing two things a name cannot cover? Is the
      limit mechanical, with a ratchet so a small function cannot grow
      past it while legacy exceptions shrink? Do long functions keep the
      branching in the parent and pure leaves below ("push ifs up, fors
      down")? (P10 rule 4, TB `tidy.zig` red zone 70–73) — Oak: not
      stated as a rule; a strict-profile lint is a candidate.
- [ ] **Assertion density.** Does every function assert its arguments,
      results, and the invariants it relies on — at least two per
      function on average (TB `replica.zig`: about seven) — one condition
      per assertion, the negative space as well as the positive, with
      relationships between compile-time constants asserted at compile
      time? Are assertions on in every build mode, and does the simulator
      refuse a mode that strips them? (P10 rule 5, TB) — Oak:
      `85-discipline.md` §5, `40-records.md` §6b `static_assert`
      (density lint planned).
- [ ] **Pair assertions.** Where a property is established in one place
      and relied on in another, is it asserted at both — the producer
      asserting what it guarantees, the consumer asserting what it needs —
      so a violation is caught at the boundary it crosses? The canonical
      pair: assert validity immediately before writing to disk or sending,
      and immediately after reading or receiving. (TB) — Oak: practice;
      not stated.
- [ ] **Assert the negative space, one condition per assert.** Does every
      function assert what must *not* be true as well as what must, with
      compound conditions split (`assert(a); assert(b)`) and implications
      written `if a { assert(b) }`, so a failure names one condition? (TB
      `TIGER_STYLE.md` §Safety, `journal.zig` recovery matchers) — Oak:
      `85-discipline.md` §5 has `assert`/`assert_eq`; the rule: not
      stated.
- [ ] **Two assertion tiers.** Are cheap invariant asserts always on, and
      O(N) verification of O(1) operations behind one named build
      constant that CI and the simulator turn on? (TB `constants.verify`)
      — Oak: only always-on `assert`; not stated.
- [ ] **Possibly-false conditions are marked.** Where a condition may
      legitimately be true or false, is that written as `maybe(cond)`
      beside the asserts, so a reader can tell "not asserted" from
      "forgot to assert"? (TB `stdx.maybe`) — Oak: not stated.
- [ ] **Division rounding is spelled.** Does every division that can round
      name its rounding (`div_exact`, `div_floor`, `div_ceil`) rather than
      use `/`? (TB §Off-By-One, `stdx.div_ceil`) — Oak: `20-types.md`
      §11.1 has `/` only; not stated.
- [ ] **Result dimensionality is minimized.** Is the simplest sufficient
      result type used (`()` over `Bool` over `u64` over `Option` over
      `Result`), so callers branch on the fewest cases? (TB §Cache
      Invalidation) — Oak: not stated.
- [ ] **The hot loop performs no I/O.** Is the apply or commit step
      declared to forbid syscalls, blocking, and allocation, with every
      read done in a preceding prefetch phase? (TB `ARCHITECTURE.md`
      §Synchronous Execution) — Oak: `60-effects-allocation.md` §2
      `forbids` can state it; the storage-engine use: not stated.
- [ ] **Assertions name both values.** Does a failed comparison report
      got and want, not just "assertion failed"? Does a trap say which
      source line? (TB, Go testing) — Oak: `85-discipline.md` §5
      `assert_eq`/`assert_ne`.
- [ ] **Assertions may not have side effects.** Is every assertion
      condition pure, so compiling it in or out cannot change behavior?
      (MISRA 13.x, P10) — Oak: assertions are always on, which makes this
      moot only if the language forbids effects in the condition; check.
- [ ] **Every result is used or discarded on purpose.** Is a non-unit
      result that is neither consumed nor explicitly discarded (`_ =`) a
      rejection? Is discarding a unit value itself an error, so `_ =`
      always marks a real choice? (P10 rule 7, MISRA 17.7, Rust
      `#[must_use]`, Go `errcheck`) — Oak: `85-discipline.md` §6
      (`OAK-D0104` planned).
- [ ] **Data scope is minimal.** Is every variable declared at the
      smallest scope, every block its own scope, and shadowing either
      forbidden or confined? Is mutable global state absent or a typed
      static with an explicit initializer? (P10 rule 6, MISRA 8.x) — Oak:
      block scoping (hypervisor note ask 6), `60-effects-allocation.md`
      §10a.
- [ ] **No side effects in conditions or operands.** Is the order of
      evaluation of operands irrelevant to the result because operands are
      pure, or is the order specified and the effects visible? (MISRA
      13.x, Go's spec on evaluation order) — Oak: `10-syntax.md` fixes
      left-to-right for operands and call arguments; effects in operands
      are otherwise unrestricted — a strict-profile lint is a candidate.
- [ ] **Simple control flow.** No `goto`, no `setjmp`/`longjmp`, no
      exceptions, no non-local exit other than a result value; `break`
      leaves exactly one loop. (P10 rule 1, MISRA 15.x) — Oak:
      `85-discipline.md` §3a.
- [ ] **No dead or unreachable code.** Is unreachable code (an
      unreachable match arm, code after a diverging call) a diagnostic,
      and is dead code deleted rather than commented out? (MISRA 2.x) —
      Oak: `35-pattern-analysis.md` unreachable arms.
- [ ] **Magic numbers named.** Is every literal that carries meaning a
      named constant with its unit, and does the compiler fold it? (MISRA,
      TB) — Oak: `sam/literals-and-constants` branch.
- [ ] **Zero warnings, all checkers.** Does the build reject every warning
      under the strict profile, with each accepted assumption an explicit
      `admit` line that keeps its audit trail? Are all available static
      analyzers run every day? (P10 rule 10, MISRA, TB) — Oak:
      `85-discipline.md` §7.
- [ ] **Naming carries meaning.** Do names avoid abbreviations, carry units
      or qualifiers where the type does not, and put the most significant
      word first so related names sort together — units and qualifiers
      last in descending significance (`latency_ms_max`), related names
      the same length (`source`/`target`), a helper prefixed with its
      caller's name, callbacks last, an options record when two adjacent
      parameters share a type? (TB §Naming, Go) — Oak: style; not stated.
- [ ] **Ambiguous operator mixes are rejected.** Is mixing bitwise and
      arithmetic operators in one expression without parentheses a
      diagnostic? (TB `tidy.zig`) — Oak: `10-syntax.md`; not stated.
- [ ] **Style rules are tests with a ratchet.** Are line length, banned
      spellings with a named replacement, leftover `FIXME`s and debug
      prints, dead private declarations and dead files, and function
      length enforced by a test, with limits ratcheted from the bottom so
      legacy exceptions cannot grow? (TB `src/tidy.zig` under `zig build
      test`) — Oak: `oak vet` lists obligations only; not stated.
- [ ] **Tooling in the language.** Are generators, CI scripts, and release
      checks written in Oak or in the compiler's language rather than
      shell or Python, so they are typed and portable? (TB
      `src/scripts/*.zig`) — Oak: `stdlib/generate_*.py`,
      `stdlib/extract_*.py` are Python — finding.
- [ ] **Comments say why, not what.** Is every non-obvious decision,
      especially every unsafe block and every admitted assumption, given a
      reason a future reader can test? Are specification references linked
      with section numbers? (TB, P10) — Oak: practice.

## 6. Integer and floating-point semantics

- [ ] **Overflow behavior is chosen per operation.** Is the default
      (wrap) stated, and are checked, saturating, and truncating forms
      distinct named operations with total semantics — no
      implementation-defined C? Does `MIN / -1` have a stated answer?
      (Rust, Zig, Swift traps, MISRA) — Oak: `20-types.md` §11.1, §11.1a;
      `90-backend.md` §7.
- [ ] **Division by zero traps, everywhere.** Does the interpreter, the C
      backend, the Metal lowering, and the Lean model agree? (Zig, Rust)
      — Oak: `20-types.md` §11.1, `56-kernels.md` §3 fault word.
- [ ] **Shifts are bounded.** Is a shift by more than the width a compile
      error for constants and a trap or defined result for variables, never
      C's undefined behavior? (MISRA 12.2, Rust) — Oak: `20-types.md`
      §11 requires shift semantics to be specified per operation; the
      rule itself is not written — gap.
- [ ] **No signed/unsigned mixing.** Are comparisons and arithmetic across
      signedness or width rejected rather than promoted? (MISRA essential
      types, Go, Rust) — Oak: `20-types.md`; `OAK-T0601` for assertions.
- [ ] **Float addition is not associative, and the language knows it.**
      Is the grouping of every reduction a stated fact (`reduce.tree`'s
      balanced counter tree, `reduce.left`), so two backends and the Lean
      model produce the same bits? Is regrouping permitted only by a
      declared law? (ml pilot F2/F3, Futhark, numerical analysis) — Oak:
      `55-parallelism.md` §4, `stdlib/reduce.oak`, `10-syntax.md` §14a
      `laws { associative }`.
- [ ] **No fast-math.** Are FMA contraction, reassociation, reciprocal
      approximation, flush-to-zero, and NaN assumptions all off unless
      explicitly requested per operation, and is the request visible in
      the type or the call? (LLVM fast-math hazards, Mojo, mlx) — Oak:
      `56-kernels.md` §4, `93-simd.md` §1.2a.
- [ ] **NaN, infinities, and signed zero have stated behavior.** Does
      every comparison, min/max, sort, and hash on floats say what it does
      with NaN and `-0.0`? Is the ordering total where a sort needs it?
      (IEEE 754, Rust `total_cmp`, Swift) — Oak: `20-types.md` §11.3.3
      semantics fixed in the specification; `stdlib/float`; the Lean
      float model.
- [ ] **Float text round-trips.** Does printing use enough digits
      (`%.9g`/`%.17g` or shortest-round-trip) and does parsing produce the
      correctly rounded value? (Ryu, Eisel-Lemire, simdjson) — Oak:
      `85-discipline.md` §5 assertion printing; parsing in codecs.
- [ ] **Denormals and rounding mode are not assumed.** Does any kernel
      depend on the default rounding mode or on denormals being preserved
      without saying so? Does the Metal target differ from C here, and is
      the difference stated? (mlx, Metal shading language spec) — Oak:
      `56-kernels.md` §4.
- [ ] **Differential float testing against the model.** Is every float
      operation tested bit-for-bit against the interpreter and against the
      Lean model's definition, not just against "close enough"? (simdutf,
      TB) — Oak: `20-types.md` §11.3.5 three-witness rule (interpreter,
      C, Lean), §11.3.6 fourth witness for transcendentals.

## 7. Concurrency and the memory model

- [ ] **A data race is undefined, so it is forbidden.** Are conflicting
      unsynchronized accesses rejected by ownership or typed as atomics,
      never permitted with a comment? (Rust, C11/C++11, Go race detector)
      — Oak: `66-memory-model.md` §7.
- [ ] **Happens-before is the vocabulary.** Are synchronization arguments
      written in terms of sequenced-before, synchronizes-with, and
      happens-before, with the executions model the Lean theorems use,
      rather than in terms of "the compiler won't reorder this"?
      (C11, Java memory model, herd/litmus) — Oak: `66-memory-model.md`
      §1–§5, `MemoryOrder.lean`.
- [ ] **Orders are explicit and minimal but never weaker than proven.**
      Does every atomic operation name its order? Is relaxed used only
      with an argument the model checks? Is sequential consistency the
      default when no argument is given? (Rust, C11, Preshing) — Oak:
      `65-machine-memory.md` §2, `67-memory-ordering.md`,
      `68-sequential-consistency.md`.
- [ ] **Litmus tests per target.** Does each target's refinement (C11
      atomics, AArch64 barriers, RISC-V RVWMO) come with the standard
      litmus shapes (message passing, store buffering, load buffering,
      IRIW) run against the model and against hardware or a simulator?
      (herd7, Sail, ARM ARM) — Oak: `69-aarch64-memory-refinement.md`,
      `spec/sail`.
- [ ] **Single writer where possible.** Does the design prefer
      single-producer single-consumer rings, per-core ownership, and
      message passing over shared mutable state and locks? (TB, LMAX
      Disruptor, DOD) — Oak: `standard-library-design.md` Ring, dbs asks
      8.
- [ ] **Ownership transfer across threads is a protocol.** When a value
      changes owner across a synchronization edge, is that a typed
      transition with the barrier at the transition, model-checked as a
      state machine? (Rust `Send`, TLA+) — Oak: `112-protocols.md`,
      `Buffer[T, S]` custody.
- [ ] **No blocking in bounded paths.** Is blocking (locks, I/O, sleeps)
      an effect that realtime and interrupt entry points forbid? (TB,
      realtime audio rules) — Oak: `60-effects-allocation.md` §12,
      `55-parallelism.md` §8.
- [ ] **Parallel iterations are proven independent.** Is a parallel loop
      admitted only when the checker proves iterations do not conflict
      (one element per thread, tiles disjoint), failing closed otherwise?
      Is the theorem named? (Futhark, ml pilot, OpenMP's unchecked
      `parallel for` as the anti-pattern) — Oak: `55-parallelism.md` §2,
      `Oak.Kernel.run_perm` (checker rule open).
- [ ] **Deterministic under simulation.** Can every concurrent component
      run under a simulated scheduler with a seed so that any interleaving
      bug is replayable? (TB VOPR, FoundationDB) — Oak: `110-testing.md`
      Deterministic event simulation, Crashes and scheduling.

## 8. Testing as an engineering discipline

- [ ] **Deterministic simulation testing.** Does the component run under
      simulated time, storage, network, and scheduling from a single seed,
      so a failure replays exactly and shrinks? Is production code and
      test code the same code with the I/O port swapped? Does one `u64`
      seed reproduce the run, is it printed on failure, does the tool
      refuse to run unseeded in a mode that strips assertions, and can the
      simulator speed time arbitrarily? (TB VOPR, FoundationDB, dbs) —
      Oak: `110-testing.md`, `120-io.md` `iosim` vs `ionative`,
      `stdlib/sim_storage.oak`.
- [ ] **Fault injection covers the real fault model.** Are the faults
      injected the ones hardware and operating systems actually produce —
      torn writes, misdirected writes, dropped writes, lost fsync, bit
      flips, latent sector errors, crashes between write and sync, clock
      jumps, partitions — not just "the call returned an error"? Is
      corruption sticky under retry (its position seeded from the
      pristine bytes), does a misdirect keep the target's old data, are
      faults off during first format, and are the double faults the
      design does not claim to survive listed? (TB `testing/storage.zig`,
      dbs, "Protocol-Aware Recovery") — Oak: `110-testing.md` Simulated
      storage (six kinds, flipped/latent persist), Simulated time.
- [ ] **Swarm the configuration.** Does the simulation draw every knob —
      counts, capacities, latencies, fault probabilities, which fault
      kinds are enabled — from the seed, with some kinds disabled entirely
      per run, so no fixed mask hides an interaction? (TB `vopr.zig`
      `options_swarm`, `fuzz.random_enum_weights`; Regehr's swarm
      testing) — Oak: `sim_storage.oak` takes a caller-fixed fault mask
      and rate; not stated.
- [ ] **Heavy-tailed simulated latency and bursty ids.** Are simulated
      delays minimum plus exponential(mean), and ids drawn bimodally
      (hot/cold) or Zipfian so caches overflow and collide? (TB
      `fuzz.random_int_exponential`, `random_id`, `stdx/zipfian.zig`) —
      Oak: `sim_schedule_delayed` and `test_range` are uniform; no
      exponential or Zipfian generator — gap.
- [ ] **Liveness is checked after the faults stop, against a named core.**
      After the safety phase, does the scenario pick a fault-free, fully
      connected quorum, make every other failure permanent, and require
      convergence within a stated budget, diagnosing *why* not (which op
      or block the core lacks)? (TB `vopr.zig` liveness mode) — Oak:
      `112-protocols.md` §1 `eventually`, `sim_sched_max_wait`; a
      simulation-level convergence phase: not stated.
- [ ] **Failures are classified.** Does a failing run say crash, liveness,
      or correctness (distinct exit codes or signatures), so triage and
      corpus routing differ? (TB `Failure{crash=127, liveness=128,
      correctness=129}`) — Oak: `110-testing.md` signatures
      `invariant:<id>` vs signal; classes: not stated.
- [ ] **The fault atlas matches the redundancy claim.** Is fault placement
      constrained so the design's redundancy can recover (at least one
      good copy across replicas; a single-disk log corrupted only by
      crash), with out-of-model double faults listed? (TB
      `ClusterFaultAtlas`) — Oak: `110-testing.md` "three a single-disk
      log can honestly keep"; per-zone atlas: not stated.
- [ ] **Exhaustive tapes for small choice spaces.** Where a scenario's
      choices are few, are all tapes enumerated rather than sampled? (TB
      `exhaustigen.zig`; matklad) — Oak: `oak prove` enumerates theorem
      domains (`125-verification.md` §3); tape enumeration for `Sim`
      tests: not stated.
- [ ] **A canary fuzzer.** Does the fuzz registry include a target that
      must fail, so a green board proves the harness can see failures?
      (TB `fuzz_tests.zig` `canary`) — Oak: not stated.
- [ ] **Durability and detection are separate obligations.** Does the
      storage test distinguish "this block must survive" from "corruption
      of this block must be detected", tracked by provenance, so neither
      hides the other? (dbs note) — Oak: `110-testing.md` provenance
      ledger.
- [ ] **Property tests with shrinking and replay.** Does every generated
      input come from a choice tape that shrinks toward a minimal failing
      case, and is the failing tape stored in a corpus and replayed on
      every run thereafter? (QuickCheck, Hypothesis, TB) — Oak:
      `110-testing.md` Choice tapes, Corpus and replay.
- [ ] **Stateful command testing.** Are stateful components tested by
      generated command sequences against a model with invariants checked
      after every command, with shrinking that removes commands? (Erlang
      QuickCheck, Hypothesis stateful) — Oak: `110-testing.md` Stateful
      command properties, typed commands.
- [ ] **Differential testing against references.** Is every codec, hash,
      sort, UTF-8 validator, and numeric routine tested bit-for-bit
      against at least one independent implementation (Go, Rust, Zig,
      simdjson, simdutf) on the same inputs? (simdutf, TB, csmith for
      compilers) — Oak: `stdlib/hash.oak` differential vs Go,
      `benchmarks/state-machines`, `sam/float-differential`.
- [ ] **Oracle is the slow path, kept in tree.** Does every optimized
      routine keep its pre-optimization form as an oracle and test the two
      agree on generated inputs, including adversarial ones? (simdjson, ml
      fusion oracle) — Oak: `71-codecs.md` §4a, codec-fusion note.
- [ ] **Counters prove the optimization fired.** Does a test assert that
      the fast path was actually taken (a counter, an absence check over
      the emitted C), so a silent fallback to the slow path is a test
      failure? Is each hot-path log line bound to one named test that
      must hit it, so traceability rather than coverage percent is the
      claim? (ml, TB `marks.zig`) — Oak: `71-codecs.md` §4
      wrapper-absence checks; `testing_classify` labels.
- [ ] **Known-answer vectors.** Are standard test vectors (RFC, NIST,
      Unicode conformance, JSON test suite) run, with the vector file in
      tree and its provenance noted? Is an on-disk hash frozen by a
      change detector (hundreds of structured cases hashed to one
      constant) and shown independent of buffer alignment? (NIST CAVP,
      simdjson's JSONTestSuite `minefield`, TB `checksum.zig`) — Oak:
      `stdlib/hash.oak` KATs; no in-tree JSONTestSuite vectors for
      `stdlib/json.oak` — gap; stability constant: not stated.
- [ ] **Interpreter and every backend agree.** Is each language feature
      differentially tested across the interpreter, the C backend, and any
      other backend at every boundary value? (csmith, TB) — Oak: e2e
      tests in `compiler/`, hypervisor note ask 2.
- [ ] **Boundary values every time.** Zero, one, capacity, capacity minus
      one, capacity plus one, empty, maximum width, minimum signed,
      unaligned offset, input exactly at a SIMD block edge, input one byte
      past padding. (classic, simdjson block edges) — Oak: `110-testing.md`
      generated inputs; check per module.
- [ ] **Negative tests.** Does every validator have tests that must
      reject, with the exact error and precedence asserted, not just tests
      that must accept? (langsec, simdjson) — Oak: `71-codecs.md` error
      precedence (`InvalidEncoding` over `InvalidSyntax`).
- [ ] **Roundtrip and algebraic laws.** Are encode∘decode = id,
      decode∘encode = canonicalize, sort idempotence and permutation
      preservation, hash determinism, and ordering laws stated as
      properties and, where possible, as Lean theorems over the same
      definition? (QuickCheck, Lean) — Oak: `sam/codec-laws`,
      `sam/pdqsort-laws`, `sam/sort-laws-universal`, `sam/stdlib-laws-*`.
- [ ] **Exhaustive on small domains.** Where the input space is small
      (all byte pairs, all u8 values, all three-node protocol states), is
      it enumerated rather than sampled? (Hyperscan's byte-class tests,
      TLC) — Oak: practice per module.
- [ ] **Every bug becomes a test first.** Is the reproducer committed
      before the fix, in the corpus if generated, as a table row if
      hand-written? (classic) — Oak: `110-testing.md` Corpus, Table
      targets.
- [ ] **Tests are hermetic and deterministic.** No wall clock, no real
      network, no shared temp state, no order dependence; a failing seed
      is printed and re-runnable. Flakiness is a bug filed against the
      test. Does CI seed each simulation run from the commit hash, and
      does the merge queue test the merge commit? (Go, TB
      `fuzz.parse_seed`) — Oak: `110-testing.md` Isolation; `-seed`
      flag; commit seeding: not stated.
- [ ] **Release artifacts rebuild bit-identically.** Is a published binary
      rebuilt from its tag and required to hash-match? (TB
      `scripts/ci.zig validate_release`) — Oak: `15-diagnostics.md` §11
      covers emitted C only.
- [ ] **Fuzz continuously, structure-aware.** Is every parser exported to
      a fuzzer (libFuzzer) with a structure-aware generator, run
      continuously, with the corpus checked in? (simdjson, Hyperscan,
      oss-fuzz) — Oak: `110-testing.md` Fuzzing.
- [ ] **Diagnostics are tested.** Does every stable diagnostic code have a
      test asserting the code, the primary label location, and the help
      text, and is output deterministic across runs and machines? (Rust's
      UI tests, Elm) — Oak: `15-diagnostics.md` §11–§12.
- [ ] **Race detector and sanitizers in CI.** Are the Go race detector,
      ASan/UBSan on the emitted C, and Miri-equivalent interpretation run
      on the standard library and compiler tests? (Go, LLVM; simdutf's compiler × flags × libc matrix with
      `-fsigned-char`/`-funsigned-char`) — Oak: `-race` in `ci.yml`;
      ASan/UBSan on emitted C only in `stdlib-benchmark.yml`,
      `json-benchmark.yml`, and one libFuzzer smoke job — extend to the
      compiler e2e suites and add a compiler × flags matrix.

- [ ] **Every body is an oracle for every other.** With more than one
      lowering or ISA body, are tests and fuzzers run once per available
      body on the same machine with outputs compared bit for bit, is the
      portable body always compiled in, and does one fuzz target feed the
      same input to every body and the interpreter? (simdjson
      `fuzz_implementations`, simdutf per-implementation `TEST`,
      `SIMDUTF_ALWAYS_INCLUDE_FALLBACK`) — Oak: `93-simd.md` §1.4 runs
      NEON, `-DOAK_PORTABLE_INTRINSICS`, and the interpreter; §5 states the
      obligation; no differential fuzz target — gap.
- [ ] **The test asserts which kernel ran.** When a flag or environment
      variable forces a lowering, does a test verify the forced path is the
      active one, and does a nonexistent selection fail loudly? (simdjson
      `checkimplementation`, `SIMDJSON_FORCE_IMPLEMENTATION=doesnotexist`
      as a must-fail test) — Oak: `OAK_PORTABLE_INTRINSICS` exists; the
      assertion of the active path: check.
- [ ] **Generators produce each error class at every position.** For a
      validator, does a generator emit one specifically ill-formed input
      per error class (header bits, too short, too long, overlong 2/3/4,
      too large, surrogate) at every offset across a block edge, asserting
      the exact class and offset? Is detection lag — an error in block N
      reported while scanning block N+1 — its own test class? (simdutf
      `validate_utf8_with_errors_tests`, `puzzler2`) — Oak:
      `compiler/e2e_stdlib_utf8_diff_test.go` injects nine damage kinds at
      one random offset over 16 sizes × 9 alignments — partial.
- [ ] **Mutation brute force against the reference.** From valid text of
      each width mix, replace one byte with a random value and, separately,
      set one random bit, a thousand times per input, requiring the fast
      and reference validators to agree on every mutant. (simdutf
      `brute_force_tests`; how issue #514 surfaced) — Oak: not stated.
- [ ] **Generate with a witness.** Does the valid-input generator return the
      ground truth the routine must compute (code-point count, expected
      transcoded bytes), so count and length functions are checked
      against the generator rather than a second implementation? (simdutf
      `generate_counted`, `transcode_test_base`) — Oak: `110-testing.md`
      generators; witnesses per module: check.
- [ ] **Emulated targets with hostile tail policies.** Are scalable-vector
      bodies run under emulation with inactive lanes forced to all ones and
      `vl` shorter than requested, at several vector lengths, so code that
      observes dead lanes fails? (simdutf qemu `rvv_ta_all_1s`,
      `rvv_ma_all_1s`, `rvv_vl_half_avl`, VLEN 128/256/1024) — Oak:
      `93-simd.md` §5 states the obligation; the mechanism is not stated.
- [ ] **Canaries around fuzzed outputs.** Does the fuzz harness allocate
      each output separately and check canary bytes past the declared
      length, so a within-page over-write is a failure rather than luck?
      Is the fuzz corpus stored and every crash committed as a test named
      by its hash? (simdutf `use_canary_in_output`; simdjson `fuzz/`) —
      Oak: `110-testing.md` Fuzzing; canaries and stored corpus not
      stated.
- [ ] **Oracle independence.** Is at least one reference witness written by
      someone else (simdutf's Fuchsia-derived validator), not a
      transliteration of the same model the fast path came from? — Oak:
      `is_valid_utf8` in the C backend is a transliteration of the Lean
      brackets; the Go `unicode/utf8` witness is independent; simdutf is
      built in `benchmarks/state-machines/cross` but only timed, not
      compared on invalid inputs.

## 9. Parsing, input validation, and boundaries

- [ ] **Validate once, at the boundary, and record it.** Is every external
      input (bytes from disk, network, FFI, user) validated exactly once
      on entry, with the result a distinct type, and is the interior of the
      program free of re-validation and of unvalidated data? Are bytes
      never reinterpreted as a record before the checksum over them is
      verified? (langsec, "parse, don't validate", simdjson, TB) — Oak:
      `71-codecs.md` §6, `70-strings.md`.
- [ ] **Never read past the input.** Is the padding contract (if any)
      explicit in the type or the call, and is reading beyond `len`
      impossible in safe code even when the SIMD block would? (simdjson's
      `SIMDJSON_PADDING`, simdutf) — Oak: `71-codecs.md` §11, §16 forbid
      over-read.
- [ ] **Output unchanged on failure.** When an encoder or writer fails
      partway, is the destination left exactly as it was (two-pass
      size-then-write, or a rollback), so the caller cannot see a partial
      record? (TB, codec note) — Oak: `71-codecs.md` §7 contracts.
- [ ] **Length before content.** Is every length prefix checked against
      the remaining input and against a declared maximum before any
      allocation or loop uses it? (langsec, every CVE) — Oak:
      `bytes_read_*` return results; check derived binary codec (dbs ask
      9, wanted).
- [ ] **Depth and size limits.** Does every recursive format (JSON
      nesting, ASN.1, protocol payload trees) have a declared depth limit
      and total size limit, enforced before recursion? (simdjson depth,
      P10 recursion rule) — Oak: derived codecs nest only as deep as
      the finite schema, so no runtime depth stack exists
      (`71-codecs.md`); a schemaless JSON reader would need the limit;
      `110-testing.md` `-max-bytes` bounds input size.
- [ ] **Canonical encodings only.** Are non-canonical forms (overlong
      UTF-8, non-minimal varints, leading zeros where forbidden, duplicate
      keys) rejected rather than normalized silently, so two encodings of
      one value cannot bypass a check? (WHATWG, RFC 3629, Protobuf
      pitfalls) — Oak: `sam/varint-canonical`, `70-strings.md`.
- [ ] **Error precedence is specified.** When an input is wrong in two
      ways, which error is reported? Is that order stated, tested, and
      preserved by every fast path? (simdjson, codec note) — Oak:
      `71-codecs.md` §4a.
- [ ] **Total functions on untrusted input.** Does any input, however
      adversarial, cause a trap rather than a result in a parser? A trap on
      external input is a denial-of-service bug; a trap on an internal
      invariant is correct. (langsec, TB's distinction) — Oak: check every
      `assert` in `stdlib/json.oak`, `stdlib/strings.oak` is on an
      internal invariant, not on input.
- [ ] **Bounded work per byte.** Is the worst-case work of every parser
      linear in input size with no backtracking, no quadratic string
      building, no hash-collision blowup on attacker-chosen keys?
      (Hyperscan's no-backtracking DFA/NFA, simdjson two-stage) — Oak:
      `71-codecs.md` §11, §19; hash seeding in `stdlib/hash.oak` — check.
- [ ] **UTF-8 validation is exact and tested against the table.** Does the
      validator reject every ill-formed sequence in Unicode Table 3-7
      (overlongs, surrogates, above U+10FFFF, truncated sequences) and is
      it differentially tested against simdutf? (simdutf, Keiser–Lemire)
      — Oak: `benchmarks/state-machines` UTF-8 against Go, Rust, Zig,
      simdutf, simdjson.
- [ ] **FFI boundary is a validator.** Does every value entering from C —
      spans, records, unions, function pointers — get its contract checked
      or recorded at the boundary, with an unknown layout a rejection?
      (Rust FFI, Swift C interop) — Oak: `92-ffi.md` §2.6, §2.10;
      `feat(verify): records and unions at the boundary`.

- [ ] **Padding content is unspecified.** Where a padding contract exists,
      does the parser depend only on padding being readable, never on its
      value — copying a scalar that may end at `len` into a filled scratch
      rather than trusting a NUL or a space? Are the padded and unpadded
      paths both first-class, selected once per document, with one oracle?
      (simdjson `visit_root_number`, `parse_unpadded`, `INSUFFICIENT_PADDING`)
      — Oak: `71-codecs.md` §16 requires a readable-capacity contract;
      content rule and twin paths not stated.
- [ ] **Errors carry the byte, the path, and the token.** Does every decode
      error carry the input offset where it was detected and the
      structural path (RFC 6901 pointer or field chain), attached once by
      the root driver rather than threaded through every helper, so the
      hot scanner's ABI is untouched? Is the position a typed payload,
      never a count field whose meaning flips on error? (weePickle
      `TransformException`, simdjson `current_location()`, simdutf
      `result.count`) — Oak: done for text — `strings.utf8_check` returns `TextFault { error,
      at }` and `utf8.locate`/`utf8_first_error` the offset (`70-strings.md`
      §4a) — and for JSON — `decode_located[T, Json]: Result[T, JsonFault]`
      (`71-codecs.md` §13 "Positions"), the offset attached where the
      error is built while the `JsonIntegerScan` hot path (§18) keeps one
      call; a structural path is not carried.
- [ ] **Error reporting costs no more than parsing.** Is building the
      error value linear in depth and bounded in size — no quadratic path
      rendering, no echoing an unbounded token into the message?
      (weePickle `toJsonPointer` after an O(depth²) OOM on `"["·100000`,
      `ToBigInt` digit cap) — Oak: not stated.
- [ ] **Recoverable and fatal errors are distinct classes.** Can a caller
      retry a value as another type after a type error while a structural
      error poisons the iterator so nothing further can be read, and is
      "which errors are fatal" a stated predicate? (simdjson `is_fatal`,
      `abandon()`, `INCORRECT_TYPE` never stored) — Oak: `71-codecs.md`
      §13 fails fast; the class split is not stated.
- [ ] **Batch boundaries never split a scalar or a UTF-8 sequence.** For a
      streamed sequence of documents, is the cut placed at a value/value
      boundary with balanced brackets, are trailing partial UTF-8 bytes
      trimmed before validation, and is the truncated tail reported to the
      caller? Is the trim a total primitive with its "otherwise valid"
      precondition typed? (simdjson `find_next_document_index`,
      `truncated_bytes()`; simdutf `trim_partial_utf8`) — Oak:
      `stdlib/strings.oak` `utf8_decode_previous` is the building block;
      `71-codecs.md` §16 requires streaming APIs to state incomplete-input
      behavior — open.
- [ ] **Late discriminators buffer visibly and keep their position.** When
      an ADT tag is not the first key, is the fallback a caller-sized
      scratch with an explicit overflow error, does the replayed decode
      still report the original offset and path, and can the type require
      tag-first so the streaming path is the only path? (weePickle
      `taggedObjectContext`, `BufferedValue`, `JsonPointerVisitor`) — Oak:
      `71-codecs.md` §7 states the buffering contract; ADT variants are
      not derived; position on replay not stated.
- [ ] **Container counts are schema facts or buffers, never guesses.** For
      a format whose container header needs the element or field count, is
      it taken from the schema (arity minus statically omitted fields) or a
      declared count pass, and is a schemaless producer that cannot supply
      it rejected at the type rather than at run time? (weePickle
      `CaseW.length`, `MsgPackRenderer.require(length != -1)`) — Oak:
      `71-codecs.md` §4a size pass, §7; `stream[F, S]` in §3 not stated.
- [ ] **Unknown-field policy is declared per schema.** Is skip-unknown
      versus reject-unknown an explicit per-type choice, is the skip
      bounded by a declared depth and size, and is the API-evolution
      consequence (adding a producer field breaks strict consumers)
      written next to the choice? (weePickle `NoOpVisitor` skip; OpenAPI
      additive evolution) — Oak: `71-codecs.md` §13 rejects
      (`UnknownField`); the policy axis is not stated.
- [ ] **Duplicate-key semantics are one rule.** First wins, last wins, or
      error — stated once and identical across every derivation path and
      backend? (weePickle's Scala 2 first-wins vs Scala 3 last-wins drift)
      — Oak: `71-codecs.md` §13 `DuplicateField` — yes for JSON.
- [ ] **Schemaless number transit is lexical.** When transcoding between
      formats without a target type, is a number carried as its digits with
      decimal and exponent positions, rather than parsed to a double and
      reprinted? (weePickle `visitFloat64StringParts`; its MsgPack renderer's
      lossy `toDouble`) — Oak: `71-codecs.md` §3 `stream[F, S]` not stated.
- [ ] **Cross-format lowering of non-native values is a declared table.**
      Binary, timestamps, extension types, 64-bit integers into a format
      lacking them — is each mapping and its loss written down, or does a
      default silently pick strings and arrays? (weePickle `JsVisitor`
      defaults; 2^53) — Oak: not stated.
- [ ] **Lossy conversion is a separate total API.** Is U+FFFD replacement
      offered as a distinct always-succeeding function with a matching
      length function, never as a flag on the strict path? (simdutf
      `_with_replacement`, `to_well_formed_utf16`; simdjson
      `allow_replacement`) — Oak: `stdlib/STRINGS.md` transcoders are
      strict only — not stated.
- [ ] **Base64 last-chunk policy is a named parameter.** Are `loose`,
      `strict`, `stop_before_partial`, `only_full_chunks` stated, with the
      decoder returning both consumed and produced counts so a stream can
      resume? (simdutf `last_chunk_handling_options`, TC39 ArrayBuffer
      base64) — Oak: `stdlib/encoding.oak` is strict only; `70-strings.md`
      §12 says so — one policy, not stated as a choice.
- [ ] **The validated level is consumed, not just produced.** Does the
      standard library have functions whose signature takes the validated
      type (`string`, `Bytes[ValidUtf8]`) and therefore skips
      re-validation, or does every text function take `[]u8` and re-run
      the validator? (simdutf `convert_valid_*`) — Oak: `70-strings.md`
      §13 defines `string`; every `text_*` in `stdlib/strings.oak` takes
      `[]u8` and re-runs `is_valid_utf8`; the restrictions on `string`
      values (no rebinding, no aggregates) are the blocker — gap.

## 10. Errors, failure, and diagnostics

- [ ] **Crash on invariant violation, return on expected failure.** Does
      the code trap (fail fast, loudly, with location) when an internal
      invariant is broken, and return a result when the environment does
      something legal but unwelcome? Is the line between the two written
      down per module? (TB, Erlang "let it crash", Go panics vs errors) —
      Oak: `85-discipline.md` §5; state the line per stdlib module.
- [ ] **Errors carry cause and location.** Does every error value and every
      diagnostic identify the primary cause, secondary causes, and exact
      source positions, and explain in the programmer's concepts rather
      than the solver's? (Elm, Rust) — Oak: `15-diagnostics.md` §1–§4,
      §10.
- [ ] **Stable codes.** Does every diagnostic have a stable code that
      tests, documentation, `admit` lines, and users can name, and is a
      code never reused for a different meaning? (Rust `E0xxx`, MISRA
      rule numbers) — Oak: `15-diagnostics.md` §2.
- [ ] **Help is mechanically credible.** Does a suggested fix compile and
      preserve meaning, or is it labeled as a hint? A wrong "help" is worse
      than none. (Elm, Rust `rustfix`) — Oak: `15-diagnostics.md` §8.
- [ ] **Cascades suppressed.** Does one root error produce one diagnostic,
      with dependent errors suppressed, so the first line printed is the
      thing to fix? (Elm, Rust) — Oak: `15-diagnostics.md` §9.
- [ ] **Internal compiler errors are bugs, not diagnostics.** Is an ICE
      reported with a reproducer request and never as a user error, and
      does the compiler never emit code after an ICE? (Rust) — Oak:
      `15-diagnostics.md` §13.
- [ ] **No silent truncation or coercion in error paths.** Does an error
      message print values exactly (full width, correct signedness, float
      round-trip digits)? (TB) — Oak: `85-discipline.md` §5.

- [ ] **Use-once materialization is a type rule, not a debug check.** Is
      "unescape this token once" or "iterate this container once" enforced
      by consume or typestate rather than by a development-mode assertion?
      (simdjson `OUT_OF_ORDER_ITERATION` only under
      `SIMDJSON_DEVELOPMENT_CHECKS`) — Oak: `50-borrowing.md` §9 consume,
      `112-protocols.md` §5a typestate; a JSON iterator using them: not
      stated.
- [ ] **Recovery is a total decision table.** Is crash recovery a table
      over the observable predicates (header valid, body valid, reserved,
      op relations, epoch) with every impossible combination asserted and
      one decision per row, rather than nested ifs? Does a single-copy
      store report "corrupt, cannot recover safely" instead of truncating
      on a checksum mismatch alone? (TB `journal.zig` cases `@A..@P`,
      "Protocol-Aware Recovery") — Oak: expressible as a `theorem` over
      `Bool` parameters decided exhaustively (`125-verification.md` §3);
      not stated as practice.

## 11. Compiler and toolchain correctness

- [ ] **Deterministic output.** Does the same input produce byte-identical
      emitted C, diagnostics, API snapshots, and Lean extraction, across
      runs, machines, and map iteration orders? (reproducible builds, Go)
      — Oak: `15-diagnostics.md` §11; check emitted C ordering.
- [ ] **Public API snapshots gate SemVer.** Is every public surface
      snapshotted, diffed on every change, and the version bump computed
      rather than chosen? (Elm's enforced SemVer, Rust `cargo semver-checks`)
      — Oak: `82-package-semver.md`, `feat/canonical-api-snapshots`.
- [ ] **Extraction is faithful and fails closed.** Does the Lean
      extraction reject any construct it cannot model rather than
      approximating, and are the modeling choices (traps as `none`, wrap
      semantics) stated? Is faithfulness itself tested? (CompCert, hs-to-coq)
      — Oak: `95-extraction.md` §3–§4, `feat(lean)` faithfulness.
- [ ] **Foundational laws refined first.** Are the smallest load-bearing
      components — type lattice, parser cursor contract, borrow-state
      transitions, effect subsumption, span conversions, diagnostic
      structure — the ones with machine-checked refinement, before larger
      features claim proofs? (constitution) — Oak: `docs/spec/README.md`
      Proof/code relationship, `STATUS.md`.
- [ ] **Transformations are licensed.** Is every optimization (fusion,
      inlining, vectorization, tiling, reassociation, check elision)
      permitted only by a stated legality rule — values, machine numerics,
      borrow flow, effect order, observable traps, synchronization, ABI —
      and ideally by a theorem? (ml license theorem, Futhark, CompCert) —
      Oak: `05-ergonomics-and-cost.md` Optimization is constrained by
      semantics, `55-parallelism.md` §6.
- [ ] **Generic code is checked once, instantiated many.** Are constraints
      checked at the definition (no C++-style post-monomorphization
      errors), and is every instantiation's specialized code differentially
      tested against the generic semantics? (Rust, ML modules, Swift) —
      Oak: `25-type-inference.md`, `feat(nativegen): generic
      instantiations`.
- [ ] **Type inference is predictable and local.** Does inference never
      generalize unsoundly (value restriction), never depend on declaration
      order across a module boundary, and always admit an explicit
      annotation that means exactly what inference would have chosen?
      (ML value restriction, Go's locality, Swift's inference blowups as
      the anti-pattern) — Oak: `25-type-inference.md` safe generalization.
- [ ] **The spec and the implementation are reconciled continuously.** Is
      every behavior in the compiler traceable to a spec section, and every
      spec sentence either implemented, marked planned, or marked
      direction? Are legacy documents retired only after reconciliation?
      (TB "the code is the design, the design is the code") — Oak:
      `docs/spec/README.md`, `LEGACY_RECONCILIATION.md`, `STATUS.md`.
- [ ] **Obligations are enumerable.** Can a user list every unproven
      assumption in a build — unsafe contracts, unbounded loops, tail
      obligations, admitted warnings — with one command? (Lean `#print
      axioms`, TB) — Oak: `oak vet`, `:obligations`.
- [ ] **Bootstrap trust is stated.** Which parts of the toolchain (the Go
      compiler, the C compiler, Lean, the Metal compiler) are trusted, and
      is the trusted computing base written down and minimized? (Thompson
      "Reflections on Trusting Trust", CompCert TCB) — Oak: not stated;
      candidate for `125-verification.md`.

- [ ] **Public signatures are written, not inferred.** Does every `pub`
      export carry an explicit type, so an inferred narrower type cannot
      become frozen API by accident? (weePickle `ToDuration:
      MapStringTo[Duration]` bin-compat comment) — Oak:
      `82-package-semver.md` snapshots canonical types; the explicitness
      requirement is not stated.
- [ ] **Major versions coexist.** Can two major versions of a module be
      linked into one program (version in the module path or namespace),
      so a v2 does not wait on every transitive dependency? (weePickle
      `v1` packages, Go `/v2`) — Oak: `82-package-semver.md`,
      `83-modules.md` — not stated.
- [ ] **Wire schema changes are classified too.** Does the SemVer
      classifier see a change to a derived codec's wire shape (renamed
      key, new required field, changed discriminator) as an API change,
      not only a change to the Oak signature? (weePickle: "any API change
      that requires your consumers to update is breaking") — Oak:
      `82-package-semver.md` classifies exports only — not stated.

## 12. Process

- [ ] **Small commits, always green.** Is every commit buildable and
      tested, small enough to review in one sitting, with the spec change
      and the code change together? (TB, Go) — Oak: practice.
- [ ] **Review walks the list.** Does a review of a security- or
      correctness-sensitive change walk this checklist's relevant sections
      and record the "no"s in the note? (MISRA compliance matrix, P10) —
      Oak: this document.
- [ ] **Feedback from consumers is dispositioned, not lost.** Is every
      ask from the os, dbs, and ml consumers recorded with a disposition
      and revisit criteria, so the same gap is not rediscovered?
      (practice) — Oak: `docs/notes/*-feedback-*.md`.
- [ ] **Every pass writes back.** When a pass over a source teaches a new
      question, is the question added here with provenance, so the next
      pass starts from the list and not from the source? (this README) —
      Oak: `docs/checklists/README.md`.
