# The Durability Hierarchy

Durability answers: **after what failures does this state still exist?**
It is the one ACID letter a language cannot provide — durability lives in
storage protocols — but a language determines whether those protocols can
be written *correctly*. The ladder first, Oak's contributions after.

## The ladder

1. **None (volatile)** — RAM-resident; gone at power loss. Most kernel
   state correctly lives here; naming the rung matters because rung-0
   state must be *reconstructible* from higher-rung state.
2. **Process-crash durable** — survives the process, not the machine:
   page-cache writes without fsync. The rung where "we wrote it" is most
   often a lie.
3. **Single-node durable** — write-ahead log + fsync barriers + checksums;
   survives power loss on one machine, modulo the firmware telling the
   truth.
4. **Torn-write safe** — rung 3 plus atomic-unit discipline: block-sized,
   checksummed, generation-stamped records so a partial write is
   *detected and excluded* at recovery (the TigerBeetle discipline).
5. **Replicated / quorum** — survives node loss: consensus-committed
   before acknowledged.
6. **Geo-replicated** — survives site loss; latency becomes the invariant
   you trade.

Each rung is a *protocol* over the one below, and every protocol has a
recovery procedure — a rung without a tested recovery path is theater.

## What Oak contributes to each rung

- **Defined behavior on every input** (all rungs): recovery code parses
  hostile bytes — torn records, bit rot. Never-UB bounds/overflow
  discipline, total conversions, and `is_valid_utf8`-style validators
  (`Oak.Utf8Validity`) mean the parser fails *closed* instead of
  undefined. Recovery is exactly where C storage engines historically
  corrupt themselves.
- **Proven layout** (rungs 3–4): on-disk records are Oak records — the
  natural layout is proven (`Oak.RecordLayout`) and *asserted in the
  emitted C* (`sizeof`/`offsetof` static assertions), so serialization is
  `store`-shaped, not `memcpy`-and-pray. Explicit-endianness accessors
  remain the program's job (recorded direction).
- **Deterministic replay** (rungs 3–6): no hidden allocation, bounded
  loops, explicit state machines — the properties that make deterministic
  simulation testing (fault-injected virtual disks, replayable histories)
  viable for Oak programs. Durability bugs are found by simulation or by
  outage; the language decides which is available to you.
- **Named intermediate states** (rungs 2+): crash points are ADT
  constructors, and exhaustive `?` matches force recovery code to handle
  every one — the compiler enumerates your crash matrix.

## The composition rule

Durability composes *upward through* the other three hierarchies: a
rung-4 store is built from rung-2 [atomicity](atomicity.md) protocols
(publish points = commit records), a rung-4-or-better
[consistency](consistency.md) choice for replication visibility, and
[isolation](isolation.md) between concurrent writers of the log tail.
State the four rungs together — "volatile ready-queue, torn-safe
single-node event log, causal cross-core visibility, serializable log
append" is a design; any subset is a hope.
