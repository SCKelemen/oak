# Note: what TigerBeetle teaches the storage-engine port

**Status: extracted into the checklists.** 2026-09-12, `specification`
branch. Source: a read of `github.com/tigerbeetle/tigerbeetle` at `main` —
`docs/TIGER_STYLE.md`, `docs/ARCHITECTURE.md`, `docs/concepts/`,
`docs/internals/{vsr,sync,data_file,testing,vopr,HACKING}.md`,
`src/vsr/{journal,superblock,superblock_quorums,checksum,message_header,replica,client,grid,free_set}.zig`,
`src/{vopr,tidy,constants,message_pool,state_machine,static_allocator,storage,aof,fuzz_tests,io}.zig`,
`src/stdx/{stdx,prng,bounded_array,iops,ring_buffer}.zig`,
`src/testing/{storage,cluster,packet_simulator,time,fuzz,exhaustigen,marks}.zig`,
`src/lsm/{tree,compaction,manifest_log}.zig`, `src/scripts/ci.zig` —
against `docs/spec/`, `docs/checklists/`, `stdlib/`, and the dbs
feedback note. Every Oak pointer below was checked by grep against the
text it names.

The checklists already credited TigerBeetle for the bounded loops, the
static allocation rule, assertion density, pair assertions, deterministic
simulation, the real fault model, and the storage rows of the performance
list. This pass is the second reading: the *mechanized* rules (`tidy.zig`,
`constants.verify`, `maybe`), the VOPR's swarm and liveness phases, and the
journal and superblock designs in enough detail that the dbs frame-scan
port can copy them rather than rediscover them. The checklist changes are
in `docs/checklists/correctness.md` (§3 root quorums, staging, outward
checksums; §4 padding-free wire records, self-naming reserved slots; §5
negative-space asserts, two tiers, `maybe`, spelled division, minimal
result types, no-I/O hot loop, operator-mix diagnostic, style tests with a
ratchet, tooling in the language; §8 swarm, heavy-tailed latency, liveness
against a core, failure classes, fault atlas, exhaustive tapes, canary
fuzzer, release rebuilds; §10 recovery as a total table) and
`docs/checklists/performance.md` (§2d wire records with `u128`, bounded
arrays and pools; §8 Direct I/O and cost shape sharpened). The sharpened
items name their additions in place.

## Expressiveness findings

Class letters are the performance checklist's §0: (a) the language cannot
say it, (b) it can say it but no fact makes the check elidable, (c) it is
expressible with a recorded contract that a fact could replace.

| # | TigerBeetle technique | Oak today | Class |
| --- | --- | --- | --- |
| 1 | `extern struct` wire formats: 256-byte header, `u128` checksum and ids at `u256` alignment, `no_padding` and `has_unique_representation` asserted at compile time, bytes cast to the record after the checksum is verified | `struct(packed)`, `struct(align: N)`, per-field `align` (`40-records.md` §6a); `static_assert(size_of/offset_of/align_of)` (§6b) and the same asserts in the emitted C header (`92-ffi.md` §2.6). `u128` landed the same day (`20-types.md` §11: `unsigned __int128`, 16 bytes at 16); no `u256`. No no-padding predicate — `static_assert(packed_size == size)` approximates it. A borrowed record view at an offset into `[]u8` exists only for JSON-derived `View[u8, R]` fields (`71-codecs.md` §13a); the fixed-layout binary codec is wanted (dbs round 3 ask 9), so headers are read field by field through `bytes_read_*_be`. | (a) wide scalars and the predicate; (c) the view |
| 2 | Sector-aligned Direct I/O buffers, alignment in the pointer type (`*align(4096) [N]u8`), file size asserted a sector multiple, `pread` capped by the OS constant, Direct I/O tri-state with a filesystem probe | Alignment is a fact on records and fields only; no alignment fact on a view, span, or `IoBuffer` window (`50-borrowing.md`, `120-io.md`, `93-simd.md` §1: unaligned element access is legal). `ionative` Direct I/O is `120-io.md` §5 increment two. The fact that would make it safe is a refinement on `IoBuffer.base` plus an alignment fact on the registered region. | (a) |
| 3 | VOPR network simulation: per-path priority queue, exponential delay with a minimum, loss, replay, capacity drop, clog, partition modes × symmetry with stability windows, recorded packets | No network model: `110-testing.md` has no partition/packet/reorder/replay vocabulary; `120-io.md` reserves `accept/recv/send`; `iosim` owns one `SimProcess`. The language pieces exist (`SimSched`, `SimQueue`, tapes); a `SimNet` over `SimQueue` with a core bitset is a stdlib item. | (a) at library level |
| 4 | Redundant WAL headers and checksum chains | Two rings over `iosim` files, `link: Bool` for body-then-fsync ordering, `crc32c_update` for chaining (`stdlib/hash.oak`), `iosim_lied` provenance as the ledger — expressible. A `u128` checksum field is now declarable (row 1); no AES/AEGIS (`hash.oak` is SHA-256, BLAKE3, CRC-32C). CRC-32C serves the frame check only with the slot address folded into the header (row 6 of the lessons below), since a 32-bit CRC does not distinguish identical well-formed data at the wrong offset. | (a) small |
| 5 | `maybe(cond)` beside asserts; `unreachable` for arithmetic trichotomies | `assert`, `assert_eq`, `assert_ne` only (`85-discipline.md` §5). Exhaustive matches make `unreachable` unnecessary for sums; arithmetic trichotomies have no spelling. `maybe` is trivial as a stdlib function; the proposition-axis version ("not statically decidable here") is the interesting one. | (a) small |
| 6 | `BoundedArrayType` (array + count, `count_as(Int)` checked at compile time), `IOPSType` (array + busy bitset, acquire → null, index recovered from pointer) | `[N]T` plus a hand-rolled count (`iosim.oak` globals); `stdlib/slab.oak` is the generational form; `Ring`/`BitSet` planned (`standard-library-design.md`). A `count: u32 where value <= N` refinement (`20-types.md` §12) can carry the bound; nothing states it. Pointer-to-index recovery is (b) by design — handles replace it. | (c) |
| 7 | Runtime state checker across replicas: canonical commit chain, parent links, client in-flight oracle, no regression, convergence re-check | `oak prove` decides invariants over the projection's reachable states (`125-verification.md` §2a); `Oak.ProtocolConformance` compares two TLA modules (`112-protocols.md` §4a); "Stateful command properties" compares an implementation with its model per command (`110-testing.md`). Missing: a derived runtime conformance monitor from the protocol declaration (`112-protocols.md` §6 direction) and a cross-replica convergence checker; both are scenario code today. | expressible, not derived |
| 8 | `random_int_exponential`, `random_id` hot/cold, Zipfian | `test_range` uniform with acknowledged modulo bias (`110-testing.md` "Choice tapes"); `random.oak` uniform xoshiro. No exponential, geometric, weighted-enum, or Zipfian sampler. TigerBeetle uses floats here and says so; an Oak version should be integer-only — a geometric sampler over the tape with a Lean law. | (a) library |
| 9 | Swarm testing: every knob drawn from the seed, a random subset of variants disabled per run | The tape can supply configuration (its first bytes), and shrinking then removes faults — which the VOPR cannot do. Missing is the convention and helper (`random_enum_weights` → `test_weights(choices, data, n)`). | (a) library |
| 10 | Static allocation sized from CLI arguments at startup, not `.bss` | `iosim` uses compile-time fixed globals; runtime-sized ownership goes through `Buffer[T]`/`c.own` (`92-ffi.md` §2.8). Both satisfy `steady` (`83-modules.md` §4.1). `StaticAllocator`'s `init → static → deinit` is a typestate Oak can declare (`112-protocols.md` §5a). | not a gap |
| 11 | `constants.verify` tier; `tidy.zig` style tests | `-profile strict` is the analogue of `config_verify`; there is no "expensive verification on" switch and no style test. | (a) tooling |

## Correctness lessons for the dbs frame-scan port

The port creates, writes, fsyncs, renames, and fsyncdirs over `iosim`,
checksums frames, and recovers by scan. From `journal.zig` and
`superblock.zig`:

1. **Frame header layout** (`message_header.zig`): checksum over the rest of
   the header; a separate body checksum so a header is trusted without
   reading the body; `size`; `op`; `parent` = the previous header's
   checksum (hash chain); a file identity to catch writes to the wrong
   file; a kind; reserved bytes zero. Declare it `struct(packed)` or with
   explicit padding fields, `static_assert` size and offsets
   (`40-records.md` §6b), and check reserved bytes zero on read.
2. **Constant relationships asserted at compile time** (`journal.zig`
   comptime block): `frame_size_max % sector == 0`, `sector % header_size
   == 0`, `slot_count % headers_per_sector == 0`, `slot_count >
   write_concurrency`, and the correlated-torn-write rule `header_sectors
   > writes_in_flight_max` (or serialize header-sector writes as
   `lock_sectors` does).
3. **Redundant header ring, written after the body**: body `pwrite` with
   `link`, then `fsync`, only then the header sector, assembled from the
   headers whose bodies are known durable; neighbors not yet durable go
   out as `reserved` with `op = slot`. Never write a header whose body is
   not on disk. Assert the body slot's padding is zero before the write.
4. **Reserved slots name their slot**: `op = slot index`, `kind =
   reserved`, a valid checksum. Recovery validates "header ok" as checksum
   ∧ file id ∧ `op % slot_count == slot` ∧ known kind ∧ size in `[header,
   max]`. This turns a misdirected read into a detected fault rather than
   a phantom record — the dbs "no phantom record unless untrusted"
   obligation.
5. **Recovery reads everything, then decides by table** (`journal.zig`
   cases `@A..@P`): read the header ring and every body in full (tearing
   is visible only in the body); compute per slot the eleven predicates;
   encode the sixteen cases as a table with assert-true/assert-false
   matchers so an impossible combination traps at recovery instead of
   being handled. Write the table as an Oak `theorem` over the `Bool`
   predicates and let `oak prove` decide totality and disjointness
   exhaustively (`125-verification.md` §3).
6. **Single-copy decisions**: `eql` (header equals body), `nil`
   (reserved), `fix` (valid body, broken or reserved header → rewrite the
   header from the body), `cut` (past the durable maximum → truncate to
   reserved), `cut_torn` (item 7), and `vsr` → for a single file this is
   "corrupt, cannot recover safely": report and stop; never truncate
   merely because a checksum failed (Protocol-Aware Recovery). Same op
   with different epochs on header and body is undecidable locally: do not
   `fix`.
7. **Torn-tail rule** (`torn_prepares`): `op_max` over both rings; a torn
   candidate is a slot whose body fails but whose redundant header is
   valid, non-reserved, and at least one wrap behind; candidates lie in
   `(op_max, op_max + writes_in_flight_max]`; if any other fault exists
   outside that window, refuse to truncate anything — torn and corrupt
   are then indistinguishable. Truncate at most `writes_in_flight_max`
   slots.
8. **Faulty is not dirty; never heal a fault by accident**: keep `dirty ⊇
   faulty` bitsets; a faulty slot's header is written with a zero
   checksum, not as `reserved`, until repaired; recovery never loads a
   header into the in-memory ring *and* marks that slot faulty, because
   the next batched header-sector write would persist it as good.
9. **Assert at recovery end**: for every clean slot the redundant and
   in-memory header checksums agree; `prepare_checksum[i] == 0 iff
   !inhabited[i]` ("zero allows it to be asserted"); the maximum op has a
   header; `commit_min <= op`; the recovered prefix is a hash chain.
10. **Root or manifest** (`superblock.zig`, `superblock_quorums.zig`): a
    fixed-position root uses four copies, `copy` outside the checksum,
    `sequence` plus `parent` chain, write-verify three of four, open two
    of four, the older full quorum preferred over a newer partial one,
    copies repaired on open, and `staging` kept apart from `working` until
    the verify quorum returns. A root published by
    `create`+`fsync`+`rename`+`fsyncdir` (the path `120-io.md` §3 proves
    durable) carries the same sequence and parent in its name or header so
    two coexisting versions order strongly.
11. **Checksums**: external for anything reached by pointer (manifest →
    segment → frames), self-checksum only at the root; pin `crc32c` with a
    stability hash and an alignment-independence test (`checksum.zig`
    tests); fold the slot address into the header (item 4).
12. **Simulation contract**: state the fault atlas — which double faults
    the recovery table does not claim to survive (header misdirect plus
    body fault on one slot) — and either exclude them from the scenario or
    assert the `vsr` outcome; classify each failing tape as crash,
    liveness, or correctness; after the fault phase run a fault-free
    recovery-and-replay phase and require the recovered prefix to equal
    the prefix acknowledged on trusted blocks (`iosim_trusted` versus
    `iosim_lied`). An AOF-style `magic` per frame belongs only where
    frames are found by scanning bytes rather than by slot.

## Disposition

| Finding | Disposition | Revisit criteria |
| --- | --- | --- |
| No `u128`/`u256` scalars (row 1, row 4) | **`u128` done** (2026-09-12, `20-types.md` §11, `compiler/e2e_u128_test.go`): an unsigned 128-bit fixed-width integer lowering to `unsigned __int128`, 16 bytes at 16, with the constructor, narrowing, and `std` half-packing vocabulary; the interpreter computes it exactly. **Open**: `u256` (TigerBeetle uses it only as an alignment, which `struct(align: 32)` already states), a Lean `BitVec 128` rendering, the checked arithmetic family at 128. | A frame header that needs a 256-bit field, or a proof over a `u128` function. |
| No-padding predicate (row 1) | **Open**; `static_assert(packed_size == size)` is the workaround. A `layout` fact "no implicit padding" on a record declaration is the proposition-axis form. | First wire record declared for the port. |
| Alignment fact on a view or `IoBuffer` window (row 2) | **Open**, tied to `120-io.md` §5 increment two (Direct I/O). | `ionative` opens a file with `O_DIRECT`. |
| `SimNet` (row 3) | **Open**, stdlib; the dbs note's round-1 caveat. | The replication protocol leaves the projection and runs as two processes. |
| Exponential, geometric, weighted-enum, Zipfian samplers over the tape (rows 8, 9) | **Open**, stdlib; integer-only with a Lean law each. | The first `Sim` test whose failure depends on burstiness. |
| `maybe`, spelled division, minimal result types, negative-space asserts (row 5, §5 items) | **Practice**, recorded in the checklist; `maybe` as a stdlib function when the first caller appears. | — |
| Style tests with a ratchet, tooling in the language (row 11) | **Open**; `oak vet` is the seat. Two Python generators in `stdlib/` are the first candidates to rewrite. | A second contributor. |
| Runtime conformance monitor derived from a protocol (row 7) | **Open**, `112-protocols.md` §6 direction. | The port's replication scenario needs a cross-replica check. |
| Recovery as a total decision table (lessons 5–7) | **Recommended to dbs** as the shape of the frame-scan recovery, with `oak prove` deciding the table's totality. | The port's recovery lands. |
