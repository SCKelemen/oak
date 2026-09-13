# Note: feedback from the dbs storage-engine evaluation, and its disposition

**Status: record of decisions.** 2026-09-10, `specification` branch.
Source: the storage engine's evaluation of Oak against its three triggers
(typestate, borrowed returns, fault-injected storage in simulation), its
list of what is still absent, and its recommendation: Oak has a credible
place in the engine's *method* today — a third witness for the storage
fault model with minimized, replayable counterexamples — but not yet in its
implementation, because the VSR core and the zero-copy frame path cannot be
written in safe Oak without typestate and borrowed returns.

| # | Ask | Disposition |
| --- | --- | --- |
| 1 | Fault-injected storage in simulation | **Done.** `110-testing.md` "Simulated storage", `stdlib/sim_storage.oak`: a deterministic two-copy block device with the six fault kinds the evaluation mapped onto its own model (torn, misdirected, dropped, lost fsync, bit flip, latent sector), tape-driven so shrinking removes faults and replay is exact, and a provenance ledger that splits durability obligations (trusted blocks) from detection obligations (the rest). STATUS row added. Caveats stand: the bundled scenario is a four-block write-ahead log; there is no object-store, network, or partition model. |
| 2 | Checked add, subtract, multiply | **Done.** `20-types.md` §11.1a: `{type}_checked_{add\|sub\|mul}` returns `Result[type, Overflow]`, `{type}_saturating_{add\|sub\|mul}` clamps; one width per call, exact-result semantics, interpreter and C backend agree at every boundary. The operators keep wrapping; there is no `wrapping` spelling because `+` is it. |
| 3 | Borrowed returns | **Done, all three increments.** `50-borrowing.md` §8c: elided single-candidate view and span returns; explicit region parameters (`frame[R]: (buf: View[u8, R]): View[u8, R]`) erased before checking; records carrying a region (`Cursor[R]`) that cross calls. The callee is checked by provenance (`OAK-B0113`), the caller's binding is a reborrow of the argument; `Oak.Escape.return_param_borrow_wf` and `reborrow_wf` are the theorems. A decoder hands back a zero-copy frame view, and a cursor record travels through calls. Remaining: more than one region per record, cross-package region calls by qualified name. |
| 4 | Typestate axis | **Unchanged.** Still "direction, will receive its own normative spec before implementation." Sequenced after borrowed returns: a typestate over views depends on the region story. |
| 5 | IO surface | **Absent, and not on the experiment's critical path.** The proposed port of the frame scan and recovery rule runs against `SimDisk` with conformance vectors entering through the FFI boundary (`92-ffi.md` §2.6 header, `c.span_of`) or as embedded arrays. A real IO surface is a separate design. |
| 6 | Runtime SIMD dispatch, non-C backend | **Absent.** Recorded; neither gates the storage experiment. |

## Second round (2026-09-11)

| # | Ask | Disposition |
| --- | --- | --- |
| 1 | SHA-256 and CRC-32C in pure Oak (and BLAKE3) | **Done.** `stdlib/hash.oak`, `import("hash")`: incremental and one-shot SHA-256 and BLAKE3 into caller storage, CRC-32C with a continuation form for chaining; known-answer vectors and a differential test against Go in both realizations. Since measured against Rust and Go on 1 MiB (`benchmarks/kernels`): CRC-32C table-driven under the masked-index fact, SHA-256 compressing blocks in place under the scaled-index and lower-bound facts, BLAKE3's quarter round by value — within ten percent of hand-written Rust, ahead on SHA-256. |
| 2 | Big-endian reads and writes from a byte view | **Already present.** The core prelude has `bytes_read_u16_be/u32_be/u64_be(view, offset): Result[T, EndianError]` and the `bytes_write_*_be(span, offset, value)` forms alongside the little-endian family (`stdlib/std.oak`). A binary codec derive is not needed for the header; it remains a direction if a whole frame format is to be derived. |
| 3 | Array-valued protocol data | **In another session's hands.** The spec (`112-protocols.md` §1) admits fixed-array `data` fields; the manifest-wide invariant over N segments is the open part. No `sam/protocol-arrays` branch exists on the remote; `origin/sam/protocol-data-v2` carries protocol data work in progress and is the place to look. |
| 4 | Conformance of a hand-written TLA+ module against a projected protocol | **Direction, not started** (`112-protocols.md` §7). Needs a design: which normal form the two modules are compared in, and whether TLC refinement or a syntactic check decides. |
| 5 | Borrowed decoded views in codecs | **Done.** `71-codecs.md` §13a: a record with `View[u8, R]` fields decodes as views of the input's string tokens (quotes included, unescaped on demand), the derived reader and decoder carry the region, and the borrow checker's increment 4 (`50-borrowing.md` §8c) lets `Result[Frame[R], E]` and match bindings carry the borrow. The frame scan can hand a frame back as a view. |

## The experiment this enables

Port the phase-1 frame scan and the recovery rule to Oak, drive them from
`oak test` over `SimDisk` with the six fault kinds enabled, and check every
recovered state against the conformance vectors the Zig and Go
implementations already agree on. A failing tape shrinks to a run with
fewer faults and replays exactly, which neither the swarm's fault
filesystem nor the VOPR gives today. Checked arithmetic covers the offsets
and sequence numbers the recovery rule computes; borrowed returns (increment 1)
let the scan hand frames back as views instead of indices.

## Sent back to dbs

Two fault kinds the engine does not inject today — lost fsync and latent
sector error — and the provenance-ledger split, which lets the durability
and detection obligations be checked as separate properties instead of one
blurred invariant.

## Revisit criteria

- Borrowed returns increment 1 lands: the frame scan returns views and the
  codecs' borrowed decoded views (`71-codecs.md` §5 item 3) follow.
- A second scenario beyond the four-block log (a checkpointed index, or a
  two-device mirror) exercises the misdirected and latent kinds against
  detection obligations, not only durability.
- An IO surface design exists: the same recovery rule runs against a real
  file, and the simulation and the file agree on the conformance vectors.

## Third round (2026-09-12) — gates for the engine-language decision

Standing constraints, stated by the owner for everything below: every
landed feature carries a formal model (a Lean module or refinement under
`spec/lean/Oak/`) or a stated reason it cannot, and runtime paths are
measured — zero-cost erasure where the feature is static, no allocation,
benchmarks under `benchmarks/` where code runs.

| # | Ask | Disposition |
| --- | --- | --- |
| 1 | Typestate-indexed handles: a handle type carrying its custody state, so `evict` on an `Offloaded` handle is a compile error, not a trap in `custody_next` | **Done** (`112-protocols.md` §5a, `Oak.Typestate`, `compiler/e2e_typestate_test.go`). Design as planned: The other half of terminal-state obligations and `via` modes. Design: a resource type with one phantom parameter is state-indexed (`Segment[S]`); the protocol projects one marker type per state, `via` callables must take `Resource[From]` and return `Resource[To]`, and constructing a state other than the initial one is admitted only inside the transition into it. Erased at run time (`Oak.PhantomRepresentation`); soundness model `Oak.Typestate`: the static index always equals the machine state, so the legality trap is unreachable in a well-typed program. |
| 2 | `io/sim` and `io/native` per `120-io.md`, with directory sync, agreeing on the dbs conformance rows | **Done** (`stdlib/iosim.oak`, `stdlib/ionative.oak`, `Oak.IoPort`, `compiler/e2e_io_port_test.go`, `testrunner/io_sim_test.go`; `fsyncdir` is op 7; selection is `replace io => iosim|ionative`). The dbs conformance rows run as a `Table` target over the same consumer once the log store is ported in the dbs repository. Design as planned: Completion rings over `SimDisk`/`SimSched`/`SimProcess`, then `pread`/`pwrite`/`fsync`/`fsyncdir`; the two realizations differ only in the fault model. Rings are caller-owned storage (no allocation); the contract of §3 is the Lean target. |
| 3 | Quorum predicates in protocol guards: counting or quantification over an array field, multi-field payloads, array-of-records data | **Done for quantifiers and record arrays** (`112-protocols.md` §1/§4, `Oak.ProtocolQuorum`, `compiler/e2e_protocol_quorum_test.go`): `count/all/any/none` over `[N]Bool` and over a Bool field of `[N]Record`, element-field reads and stores, record sets in `TypeOK`. **Open:** multi-field payloads per step — the typed-command derive admits one scalar payload; a record payload needs the derive to generate and encode records. Original plan: Guard forms `count(data.acked) >= N`, `all(data.acked)`, `any(...)` with a bounded fold in Oak and `Cardinality`/`\A`/`\E` in the TLA+ export; payload records; `[N]Record` data. Extends `112-protocols.md` §1 and §4 together so the two gates keep agreeing. |
| 4 | Interval time source: earliest/latest with an attested bound, layered over timesim's faults | **Done** (`time_source_attest`, `time_interval`, `time_interval_before`; timesim faults `TIME_FAULT_BOUND_BREAK` and `TIME_FAULT_UNATTEST` with `timesim_interval_honest`; `Oak.TimeInterval`; `compiler/e2e_time_interval_test.go`). The clock-ordered class refuses on `Err(Unattested)` and a scenario can make the bound fail. Original plan: `110-testing.md` "Simulated time" gains an interval clock and a bound-attestation fault; the clock-ordered class refuses on an unattestable bound. |
| 5 | Conformance of a hand-written TLA+ module (`Custody.tla`) against a projection | **Done** (`112-protocols.md` §4a, `oak protocol -conform Custody -against Custody.tla custody.oak`, `Oak.ProtocolConformance`, `compiler/protocol_conform_test.go`). Modules outside the normal form are reported unsupported; TLC refinement stays their check. Original plan: Design chosen: compare in the projection's normal form — one action per step, one disjunct per line — after parsing the hand-written module's actions; a checker verdict, not a reviewer's. TLC refinement stays the fallback for modules that use forms the normal form lacks. |
| 6 | rv64 as a first-class target (AArch64 and RISC-V are dbs's only targets) | **In progress; first increment done** — the assembler's RV64 lane (`94-assembler.md` §9): `name.rv64.oakasm` units under the LP64 psABI contract, RV64IM generated from riscv-opcodes, seam checker with the comparison-branch rule and the `ra`/`s*` frame obligation, verifier terms with the W-form and total-division semantics (`Oak.RiscV`), `EM_RISCV` objects linking with `riscv64-elf-gcc`, encoder agreement with GNU as, and a QEMU differential against the verifier. **Second increment done**: `oak build -target linux/riscv64` (and every other `os/arch`) from any host — `90-backend.md` §2a: the target picks the lane, the companion object declares lp64d, and `zig cc` links a static musl binary with the assembled rv64 unit inside (`compiler/e2e_cross_test.go`, `Oak.Target`). **Third increment done**: freestanding builds for kernels and microcontrollers — `freestanding/arm` (Cortex-M) and `freestanding/riscv32` as ILP32 members, `-cpu`/`OAKCPU`, libc-free objects (`<math.h>` hosted-only), executed under QEMU on a Cortex-M3 and an RV32 core (`compiler/e2e_mcu_test.go`). **Fourth increment done**: the freestanding host boundary — `oak_host_write` (weak) carries every diagnostic, `timehost` realizes the time port over two clock hooks, `ionative`'s `oak_io_host_*` are the io hooks; `Oak.Freestanding`. **Fifth increment done**: span element memory in the rv64 checker and verifier (normalized LP64 length, index guards, element regions, `ebreak` failure arms; `first(v) = v[0]` proven, `vsum` in the QEMU differential). **Sixth increment done**: element loops proven (widened loop couplings) and the Sail RISC-V golden model as a second execution oracle (`TestRV64SailDifferential`). **Seventh increment done**: `oak run -target linux/riscv64` executes through a user-mode emulator (`OAK_EMULATOR`, `qemu-<arch>`), refused fail-closed without one; CI runs the rv64/arm64/amd64 cross builds under `qemu-user-static`. **Eighth increment done**: the RISC-V memory refinement layer (`69-riscv-memory-refinement.md`, `Oak.RiscVMemory`): the model found the ISA's C11 acquire mapping RCpc, so Oak's acquire is strengthened to RCsc on RISC-V in the emitted C. **Ninth increment done**: the Sail bridge — `Oak.SailRiscVBridge` proves the Sail model's instruction expressions equal Oak's RV64 semantics for 13 instructions against verbatim, drift-checked Sail definitions; `spec/lean-sail/` holds the same theorems against the export (blocked on a Sail newer than opam's 0.20.2). **Tenth increment done**: the F and D extensions under LP64D — floating-point registers, 127-encoding table, the `fa`/`fs` contract and obligations, encoder agreement with GNU as, an `f64` unit in the QEMU and Sail differentials against IEEE-754, `Oak.RiscV.lp64dBinding`. Next: RVV; RVWMO in `MemoryOrder.lean`, the sail-riscv bridge (emulator built under `external/`), then F/D and RVV. |
| 7 | Vector dispatch across AArch64 feature levels and RVV behind one deterministic interface | **First increment done**: the fixed `simd` vectors have a RISC-V Vector realization beside NEON and the portable loop (`93-simd.md` §1.4), chosen at build time by target and `-cpu …+v` — no runtime dispatch; the same programs pass under QEMU at VLEN 128 and 256 against the interpreter (`compiler/e2e_rvv_test.go`). Reductions and float min/max stay portable so results are bit-identical on every realization. **Second increment done**: the scalable strip-mining API of §4 (`simd.Active`, `ScalableU8`/`U32`, active-extent ops), block-local, with portable and RVV realizations and Lean's extent-independence theorems; witnessed at four extents across the interpreter, portable C, and RVV at two VLENs. **Third increment done**: the AArch64 SVE realization of the scalable API, selected by an SVE processor under `-cpu` (`generic+sve`, `neoverse_v2`): sizeless `svuint8_t`/`svuint32_t` block-locals, every operation under the `whilelt` predicate rebuilt from the extent, the fixed 128-bit vectors kept on NEON; the same program passes under QEMU at 128, 256, and 512-bit vector lengths against the interpreter (`compiler/e2e_sve_test.go`). **Fourth increment done**: predicated operations (`93-simd.md` §4.1) — comparisons to two-valued masks (`eq/ne/lt/gt`), `select`, a zeroing `load_masked`, a preserving `store_masked`, `count_nonzero` — in the portable, RVV, and SVE realizations, with Lean's per-lane preservation and chunking-independence theorems; a database-shaped range filter (compare, count, masked store over a marker, masked reload, select) agrees at extents 1/3/5/16 and under QEMU on both scalable ISAs. Next: `vsetvli` as assembler checker state. |
| 8 | SPSC and MPSC rings as memory-model consumers | Wanted. Follows the C and ISA refinement `MemoryOrder.lean` lists as next; rings then reuse the `io` ring shape. |
| 9 | Derived binary codec for fixed-layout records with per-field endianness | Wanted. A non-JSON derive in `71-codecs.md`; the header stops being hand-written over `bytes_read_*_be`. |
| 10 | Document `-max-bytes` in the Table section | **Done** (this round): `110-testing.md` "Table targets" names the flag, the default, and the per-row refusal. |

## Fourth round (2026-09-12, evening) — the engine question reopened

The engine's own summary, verified by running each item at `a99146a`
rather than reading the commit: seven of ten landed, every one with a
Lean model. Typestate-indexed handles (evict before publish is a type
error; caveat: a `Bool` data fact cannot refine the index, so `published`
must be a state, not data), `io/sim` and `io/native` behind one surface
selected in `oak.mod` (the engine's WAL-over-`iosim` contract passes),
quorum predicates exported as `Cardinality` and quantifiers, the interval
time source (an exact fit to `ClockOrder.tla`), the conformance checker
(normal form cannot read `Custody.tla`'s sets and functions; TLC stays the
path for hand-written specs), rv64 as an assembler lane only, and hash
through the AArch64 crypto instructions at 0.97 and 1.26 times Go with the
portable body as oracle. Beyond the list: `oak prove` decides theorems
over state and data exhaustively (the custody `Durable` invariant over 168
step cases, the evict mutant refuted with a counterexample state), the
opt-in native AArch64 backend with bit-level verification, and the closed
extraction chain for one real program.

**Decision recorded by the engine.** The three gates are met in letter,
so the question is open, not closed: Oak is a candidate for the storage
core, Zig keeps VSR until protocols carry per-replica logs and record
payloads; ADR-0001 is not flipped. Design log 0057 names three criteria
for an ADR-0002 proposing the split: the port passes the conformance rows
and all six `SimDisk` faults over `iosim`; the native build links on its
default path; a frame scan over 64 MiB lands within 1.2× the Zig reference
on AArch64.

| # | Ask | Disposition |
| --- | --- | --- |
| 1 | IO ops the recovery rule needs: exclusive create producing `exists`, truncate, readdir, rename, stat; `iosim` over `SimSched` and `SimProcess` as the spec says | **Done** (`120-io.md` §2, §4, §8 increment 5). Ops 8–13: `create` (exclusive, `Exists`), `truncate`, `readdir`, `rename`, `stat`, `unlink`, in both realizations and one consumer; the engine's own `FS` port (`Create`, `Open`, `List`, `Remove`, `SyncDir`; `Truncate`, `Size`) maps onto them one to one. `iosim` now has a flat directory of 16 named files of 4 KiB whose entries are durable only after `fsyncdir` — which caught the WAL scenario opening its log without one — picks completion chains through `SimSched`, and owns a `SimProcess` that asserts no operation while down. `Oak.IoPort` states the directory laws. Open: `mkdir`/`MkdirAll` and more than one directory. |
| 2 | Record payloads per protocol step, and per-replica log data, so `Replication.tla`'s log-agreement invariant is declarable | **Done** (`112-protocols.md` §1). Record payloads: a step's payload may be a declared record of command scalars, read as `cmd.field`, quantified over the record set of its fields' domains (one configuration constant per field), generated field by field by the typed-command derive, enumerated with the step by `oak prove`. Per-replica logs: data fields may be declared records and arrays of records with array fields inside (`replicas: [2]Replica`, `Replica { log: [3]u8, len: u8 }`), guards and effects use paths of any depth, the model-checker module folds nested stores into one `EXCEPT` per field, and the log-agreement invariant is a theorem over the projection that `oak prove` decides on the reachable states (`compiler/e2e_protocol_record_payload_test.go`, `compiler/e2e_protocol_replica_logs_test.go`, `prove/replica_logs_test.go`; TLC-checked). The invariant also reaches TLC: a theorem in the invariant subset is stated in the module as `Invariant_<name>` and listed in the configuration, so `Replication.tla`'s log agreement is one declaration checked by both the prover and TLC (`compiler/e2e_protocol_invariants_test.go`). **Addendum (evening):** refinement types as payloads (`112-protocols.md` §1) — `Replica: type = u8 where value < u8(2)` is one declared domain read by the projection, the TLA+ module (a defined set, no constant), `oak prove` (exactly the admitted values) and the typed-command derive; the refined two-replica model with per-replica logs decides `Agreement` and `CommitLeqOp` over 49 reachable states in a second, where the bare-`u8` model has 66,304 step values and is now refused before enumeration instead of hanging. |
| 3 | A TLC-refinement fallback in `-conform` for set-and-function-style modules | **Done** (`112-protocols.md` §4a, `compiler/protocol_refine.go`). A module the normal form reports unsupported (or any module on `-tlc`) is checked by TLC: the projection is written as `<Name>Projection`, a generated `<Module>Refinement` instantiates it under the `-map` state mapping and states `RefinementSpec == Projection!Spec`, the module's constants come from `-against-cfg`, and TLC decides whether every behavior of the module is one of the projection — exit 0, 1 with the counterexample, or 2 with the four files written for a machine that has TLC. A set-and-function Slots module refines; one that halts a slot early is caught at `Halt`. |
| 4 | `oak prove` over larger domains: `u32` fields and small arrays via the bit-blaster, and a Lean path for array data | **Open**, listed as direction in `125-verification.md` §6. Today the exhaustive decider covers `Bool`, `u8`/`i8`, `u16`/`i16`, payload-free sums, and records of those; the bit-level decider covers fixed-width scalars of any width but no views, arrays, or data-dependent loops. |
| 5 | rv64 for Oak bodies: tested C cross-compile first, RVWMO instantiation, `ionative` on riscv64 Linux | **Open.** As the engine states: the assembler lane (`94-assembler.md` §9) is landed, the instruction-function library and a body target are not; `MemoryOrder.lean` has the RVWMO shape to instantiate. |
| 6 | Fix the `build -native` duplicate-symbol link on the default asm path; retire the stale "IO ports: design" STATUS row | **Done, both.** Reproduced on `examples/asm` with and without `-native`: `buildOne` emitted the inline-assembly C (the `-emit-c` form) and then linked it beside the native companion object, so every asm unit's symbol was defined twice; the executable is now compiled from the native emitter's C (`main.go`), and `TestBuildAsmUnitsLinkOnceInEveryMode` builds and runs the example under every asm mode. The `run` command was never affected (it already used `compileBinary`). The stale row is deleted; the landed row stands. |
| 7 | Still wanted: rings as memory-model consumers, a derived binary codec, runtime CPU-feature dispatch | **Runtime dispatch landed (2026-09-13)**: `dispatch { sve: f_sve, rvv: f_rvv }` on a function (`93-simd.md` §6; design note `cpu-dispatch-design-2026-09.md`) — one probe before `main`, a branch on the word per call, the SVE realization compiled beside the baseline in one translation unit, the interpreter's feature set as the differential check. Rings and the derived codec remain. Related this round: the `simd` catalog gained the mask vocabulary (`movemask_E`, `ctz`, `popcount`; `93-simd.md` §1.2), so a structural-index scan in the simdjson shape is now expressible; selection remains per target. |

### Revisit criteria (fourth round)

- ADR-0002's three criteria are the acceptance test for this repository:
  all six `SimDisk` faults over `iosim` against the conformance rows (needs
  ask 1), the default-path native build (done), and the 64 MiB frame scan
  within 1.2× Zig (needs the borrowed frame views and the block loop
  check-free — `docs/notes/codec-text-extraction-2026-09.md` finding 9).
- A `Bool` data fact refining a typestate index (the engine's caveat on
  ask 1 of the third round) is a proposition-axis question: whether a
  refinement on protocol data can select the state marker.
- The frame-scan port's WAL and recovery should copy TigerBeetle's journal
  and superblock designs rather than rediscover them; the twelve lessons
  (redundant header ring written after the body, reserved slots naming
  their slot, recovery as a total table decided by `oak prove`, the
  torn-tail rule, faulty ≠ dirty, outward checksums) and the
  expressiveness gaps they expose (`u128`, a no-padding predicate, an
  alignment fact on `IoBuffer` windows) are in
  `docs/notes/tigerbeetle-2026-09.md`.
