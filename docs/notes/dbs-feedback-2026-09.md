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
| 3 | Borrowed returns | **Designed, not implemented.** `50-borrowing.md` §8c: region-indexed returns — the region elided when one parameter can be its source, a `[R]` type parameter otherwise, `View[T, R]`/`Span[T, R]`, region-carrying records so §8b aggregates can cross calls, `OAK-B0112` for a return that escapes its declared region, and `Oak.Escape.escape_outer_owner_preserves_wf` as the theorem the rule instantiates. Three increments listed; the first alone unblocks the frame cursor. Awaiting review before code. |
| 4 | Typestate axis | **Unchanged.** Still "direction, will receive its own normative spec before implementation." Sequenced after borrowed returns: a typestate over views depends on the region story. |
| 5 | IO surface | **Absent, and not on the experiment's critical path.** The proposed port of the frame scan and recovery rule runs against `SimDisk` with conformance vectors entering through the FFI boundary (`92-ffi.md` §2.6 header, `c.span_of`) or as embedded arrays. A real IO surface is a separate design. |
| 6 | Runtime SIMD dispatch, non-C backend | **Absent.** Recorded; neither gates the storage experiment. |

## The experiment this enables

Port the phase-1 frame scan and the recovery rule to Oak, drive them from
`oak test` over `SimDisk` with the six fault kinds enabled, and check every
recovered state against the conformance vectors the Zig and Go
implementations already agree on. A failing tape shrinks to a run with
fewer faults and replays exactly, which neither the swarm's fault
filesystem nor the VOPR gives today. Checked arithmetic covers the offsets
and sequence numbers the recovery rule computes; borrowed returns are not
needed until the scan hands frames back instead of indices.

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
