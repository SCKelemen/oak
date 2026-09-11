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
