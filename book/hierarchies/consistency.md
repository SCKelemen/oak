# The Consistency Hierarchies

"Consistency" names two different ladders, and conflating them causes real
design errors. The first is about **what orders of events observers may
see** (the distributed-systems ladder). The second is about **who
maintains the invariants** (the ACID-C ladder). Oak takes positions on
both.

## Ladder 1 — ordering models, weakest to strongest

1. **Eventual** — replicas/observers converge if writes stop; any interim
   order may be observed. The only guarantee is convergence.
2. **Consistent prefix** — observers see *some* prefix of the write
   history: never a reordering, possibly a stale one.
3. **Session guarantees** — read-your-writes, monotonic reads, monotonic
   writes: per-observer sanity without global agreement.
4. **Causal** — if write B was issued by someone who had seen write A,
   nobody observes B without A. The strongest model that survives
   partitions with availability.
5. **Snapshot** — every read within a scope observes one consistent
   point-in-time state.
6. **Sequential** — all observers agree on a single total order of
   operations (not necessarily real-time).
7. **Linearizable ("strong")** — sequential *and* consistent with
   real time: an operation appears to take effect at an instant between
   its start and end. Per-object; its transactional big sibling is strict
   serializability (see [Isolation](isolation.md)).

## The mapping that makes this a kernel chapter

Between two cores, **shared memory is a replicated system** and the
memory orders are consistency models per location:

| Ordering model | Memory-order rung |
| --- | --- |
| eventual | plain access to a flag another core polls (don't) |
| session/monotonic per cell | `relaxed` atomics — indivisible, same-cell ordered, unordered against everything else |
| causal | `acquire`/`release` — precisely "what the writer had seen travels with the write"; the payload-publish pattern is causal consistency by construction |
| sequential | `seq_cst` operations among themselves |
| linearizable per cell | any single `Atomic[T]` cell's RMW history |

This is why the [memory-order ladder](../concurrency/memory-order.md)
advice "stand on the lowest rung that makes the invariant hold" is the
same advice as "don't buy linearizability where causal suffices" — they
are one ladder wearing two vocabularies. A hypervisor's vCPU mailbox wants
causal (rung 4 / acquire-release); a global generation counter read for
diagnostics tolerates rung 3; nothing in a well-partitioned kernel should
need rung 6 often enough to notice its cost.

## Ladder 2 — invariant obligations, by when violations die

The ACID-C reading: a *consistent* state is one where the invariants hold.
Oak's hierarchy of who enforces them:

1. **Types** (compile time) — impossible states unrepresentable: ADTs over
   Boolean flags (`docs/spec/10-syntax.md` §3a's boolean-blindness
   guidance), `rune` excluding surrogates, views without write authority,
   nominal `c.*` types keeping foreign values quarantined.
2. **Checkers** (compile time) — borrow aliasing laws, bounded loops,
   recursion rank certificates, exhaustiveness: invariants about *code
   shape*, machine-decided.
3. **Assertions** (run time, fail-stop) — `assert` never elided
   (`docs/spec/85-discipline.md` §5); bounds traps; the unreachable-match
   trap. A violated invariant dies at the violation site, in every build
   mode.
4. **Proofs** (meta) — the Lean gate checks laws about the rules
   themselves (`Oak.Borrowing`, `Oak.RecordLayout`,
   `Oak.TypeLatticeRefinement`…), so rungs 1–3 stand on checked ground.

Design rule: push every invariant down the ladder as far as it goes —
each rung down converts a class of runtime failures into impossibilities.
The two ladders meet in practice: a rung-4 *ordering* choice
(acquire/release) is usually what makes a rung-1 *invariant* claim ("this
Ring's slots are initialized before visible") actually true across cores.
