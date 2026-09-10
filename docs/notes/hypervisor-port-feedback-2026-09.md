# Note: feedback from the vgic/hypervisor ports, and its disposition

**Status: record of decisions.** 2026-09-10, `specification` branch.
Source: the twelve asks raised while porting the Zig hypervisor modules
(`vgic`, `ipc`, `virtio_mmio`, `virtio_queue`, `ring`, `sched`, `stage2`)
to Oak, ordered by the ports as "blocking or forcing ugly workarounds"
first, then "larger, for the backlog's hardest modules".

| # | Ask | Disposition |
| --- | --- | --- |
| 1 | Narrowing conversions | **Done.** `20-types.md` §11.1: `{target}_{op}_{source}` with `trunc`, `saturating`, `checked`, and `bits`; every operation total, no implementation-defined C. |
| 2 | Signed integer semantics | **Done.** `20-types.md` §11.1, `90-backend.md` §7: two's-complement wrap for `+ - * / %` on `i8`..`i64` through the union-pun helpers, `MIN / -1` wraps, division by zero traps; negation and comparisons follow the same widths. Differential-tested against the interpreter. |
| 3 | Conditional mutation without `if` | **Covered.** A one-armed conditional `cond ? { x = v }` is a statement (`10-syntax.md` §3a); the extents checker sees through `&&` and Bool bindings so guarded stores stay proven (`50-borrowing.md`, extent facts). |
| 4 | Bitwise complement `~` | **Done.** Prefix `^` is the complement (`10-syntax.md` §3b); a `~` in source is an illegal token whose diagnostic names `^`. |
| 5 | Full-width unsigned literals | **Done.** Decimal and radix literals up to `2^64-1` parse; above the signed range a literal is wide and types only as `u64` (`25-type-inference.md` §3a). |
| 6 | Block-scoped shadowing | **Done.** A loop body and every block are their own scope; a name declared inside does not collide with a sibling block's, and the C emitter scopes its container classification per block. |
| 7 | Tagged unions with payloads at the ABI | **Done.** `92-ffi.md` §2.6: every emitted union is `struct { u32 tag; union { ... } payload; }` with a cc-ratified layout; `pub` functions returning effects are consumed directly from C through a mirror typedef, `size_of`/`offset_of` answer for unions, and boundary spans carry views of unions. |
| 8 | Multiple return values / out-parameters | **Covered, no tuple syntax.** Return a record or a tagged union by value (`Step { tick, effect }`, `Effect`); records, unions, and now owned arrays (`90-backend.md` §10) are all values at a function boundary, so the `last_*` globals workaround is unnecessary. A tuple spelling would be sugar over an anonymous record and is recorded as a direction, not a gap. |
| 9 | Optionals | **Covered.** `Option[T]` is declared in the standard library (`import(std)`) and monomorphized per instantiation (`30-adts-patterns.md` §1a); a nullable record field embeds the concrete `Option` with a proven layout. Sentinel integers are not needed. |
| 10 | Const-generic functions over element type and size | **Done.** `20-types.md` §11.0: `sum[N: u32]: (v: [N]u32)`, `size[T, N: u32]: (r: Ring[T, N])`, inferred from an argument's static length or a const record's instantiation, or explicit; lengths may be arithmetic over const parameters (`[M*K]T`), folded at instantiation. `Sched(N, Q)` and `Vgic(irq_count)` are a const-generic record plus const-generic functions over it. A whole-`Geometry` generic (`stage2`) is a record of consts passed as one const-generic record. |
| 11 | Atomics with acquire/release in portable code | **Covered.** `65-machine-memory.md`: `Atomic[T]` cells embed in records and owned arrays; `atomic_load_acquire`, `atomic_store_release`, `atomic_load_relaxed`, the read-modify-write and compare-exchange forms with explicit orders are ordinary Oak builtins over a storage path; cacheline placement is a per-field `(align: 64)` annotation (`40-records.md`) with the emitted offset assertions. The SPSC ring is expressible as written. |
| 12 | Bounds-checked guest-memory accessor | **Covered by the standard library.** `bytes_read_u16_le` / `_be`, and the `u32`/`u64` forms, read at a computed offset from a `[]u8` and return `Result[T, EndianError]`, so a descriptor-ring walk is copy-then-validate over checked reads with no pointer arithmetic. A dedicated accessor type over a guest region (a view with a base offset) is a direction once views may live in records (`50-borrowing.md`, roadmap). |

## Revisit criteria

- A tuple return spelling (8) waits on a use that a named record does not
  serve; the cost is a second anonymous-record surface.
- A guest-region accessor type (12) waits on views in records
  (`roadmap-authority-resources.md`).
- Generic modules over a whole geometry (10, `stage2`) are const-generic
  records plus functions today; a module-level parameter is a direction.
