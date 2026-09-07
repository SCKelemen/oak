# Can Oak express real OS kernel data structures?

Status: survey note · 2026-09-07 · evaluated at `d5891ac` against the
structure inventories of SerenityOS (`AK/`, `Kernel/`), Linux
(`include/linux/`), and Fuchsia's Zircon (`fbl/`, `ktl/`). Where a pattern
is claimed expressible, an **executable test in this repo compiles and runs
it** — expressibility here means "runs today through the C backend", not
"should work".

## Method

Each system's load-bearing structures were grouped by *pattern*, since the
three codebases converge on a small set: fixed-capacity value containers,
intrusive linked containers, bitmaps/packed words, static/per-CPU state,
ownership/refcount wrappers, and hardware-shaped tables. For each pattern:
what the C/C++ original does, what the Oak form is, whether it runs today,
and what it costs at runtime relative to the original.

## 1. Fixed-capacity containers — runs today, zero-cost

**Originals**: Serenity `CircularQueue<T, Capacity>` / `FixedArray<T>`,
Linux `kfifo`, Zircon `ktl::array`.

**Oak**: `Ring[T, N: u32]` with an owned-array field — const parameters
landed for exactly this shape:

```oak
Ring[T, N: u32]: type = struct {
  buffer: [N]T
  head: u32
  count: u32
}

events: Ring[u8, 8]
```

Executable: `compiler/e2e_ring_test.go` (push/pop with wraparound as a
static global). Cost: the emitted C is the struct a kernel author writes,
plus bounds traps on element access — the never-UB tax Oak's constitution
mandates. The `sizeof`/`offsetof` static assertions bind the layout to the
`Oak.RecordLayout` proof at cc time, which none of the originals have.

## 2. Intrusive linked containers — runs today, as pools + index links

**Originals**: Linux `struct list_head` (+ `container_of`), `hlist` hash
chains; Serenity `IntrusiveList<T, &T::m_node>` (scheduler ready queues);
Zircon `fbl::DoublyLinkedList`/`fbl::WAVLTree` (threads, handles, waiters).

This is the pattern that defines kernel C. The pointer-graph form is
**deliberately not** Oak's form: safe Oak has no raw object pointers, and
that is a feature. The Oak doctrine is the one TigerBeetle-style systems
already converged on:

> **Nodes live in static pools; links are typed indices.**

```oak
Thread: type = struct {
  priority: u8
  next: u32
  prev: u32
}

pool: [8]Thread
readyHead: u32 = 255
```

Executable: `compiler/e2e_scheduler_test.go` — enqueue, middle unlink,
dequeue over the pool, doubly linked. What the transformation buys:

- `container_of` vanishes: the index *is* the identity (Linux needs the
  macro precisely because a `list_head*` forgot its container);
- links are u16/u32, half or quarter the size of pointers — denser nodes,
  better cache behavior than the originals;
- every traversal step is bounds-checked (or provably in range), where the
  pointer form is unverifiable by construction;
- pools are static, matching Power-of-Ten rule 3 (no dynamic allocation
  after init) — which the kernels above enforce socially, not structurally.

Cost relative to `list_head`: one array-base add per hop (usually free on
AArch64 addressing), plus the bounds trap. Trees (rbtree/WAVL) are the
same doctrine with three links; expressible now, but *reusable* tree code
wants generic functions (gap #1 below).

## 3. Bitmaps, packed words, tagged fields — runs today

**Originals**: Linux `bitmap.h`/`bitops` (`unsigned long[]`), rbtree's
parent-pointer-plus-color packing, PTE bit layouts; Serenity `Bitmap`;
Zircon page-state bitmaps.

**Oak**: `[N]u64` globals plus explicit mask arithmetic, with the
`arm64.clz64`/`rbit64` instruction functions for find-first-set style scans
and `%`/shifts for word indexing. No bitfield syntax — MISRA prefers the
explicit masks Oak forces anyway. Typed wrappers (phantom-tagged words for
PTEs) are expressible with the existing phantom machinery when wanted.

## 4. Static and per-CPU state — runs today (single-core form)

**Originals**: Linux `DEFINE_PER_CPU`, static driver state; Zircon
`percpu` array; Serenity `Processor` instances.

**Oak**: static globals landed with constant-initializer discipline
(`OAK-T0501`): zero-initialized pools, counters, record globals — the
kernel-state shape (`compiler/e2e_globals_test.go`). Per-CPU indexing as
`[MAX_CPUS]PerCpu` with an explicit cpu-id index is expressible now; the
*register-backed* form (TPIDR_EL1/EL2 base) needs the assembler milestone
(`94-assembler.md`) and is the honest boundary.

## 5. Ownership and refcount wrappers — partially, by design

**Originals**: Serenity `NonnullOwnPtr`/`RefPtr`, Zircon `fbl::RefPtr` +
`fbl::RefCounted`, Linux `kref`.

Oak's position: single ownership plus borrows, no shared-ownership pointer
type. Explicit refcount fields in pooled objects (a `refs: u32` managed at
acquire/release sites, generational handles for use-after-free detection —
`semir.HandleTable` exists) express `kref` honestly. What does **not**
exist: destructors/RAII, so nothing runs on scope exit — release is
explicit. That is TigerStyle-compatible (explicit resource discipline) but
it is a real ergonomic difference from Serenity/Fuchsia C++, and
use-after-release is only caught dynamically (handles) until resource
types land (`OAK-B0111` reserved). Verdict: expressible with discipline;
*enforced* release needs the resource-types milestone.

## 6. Hardware-shaped tables and MMIO — largely landed

**Originals**: page tables, GDT/IDT-analogues, GICv2 register blocks.

**Oak**: `[N]u64` globals with proven layout for tables; the typed MMIO
and barrier surface (chapters 69/93 work, `arm64.mmio_*`, `dmb/dsb/isb`)
landed on this branch with fail-closed non-AArch64 emission; atomics with
C11 lowering landed earlier. The remaining hardware boundary is vector
tables and sysreg writes — assembler milestone.

## Gap list, ordered by what blocks kernel code

1. **Generic functions** — pools/rings/trees exist per-type; reusable
   `push[T, N](r: Ring[T, N], v: T)` does not monomorphize yet. Biggest
   ergonomic gap; everything above works but is written per instantiation.
2. **Resource types / enforced release** (`OAK-B0111`) — turns the
   refcount/handle discipline from convention into checked law.
3. **Assembler milestone** (`94-assembler.md`) — vector tables, sysregs,
   register-backed per-CPU; already normative design.
4. **Const-parameter arithmetic** (`[N+1]T`, `N % 2 == 0` constraints) —
   wanted for power-of-two ring masks instead of `%`.
5. **Atomic record fields / atomic arrays** — v1 confines `Atomic[T]` to
   standalone globals; faithful cross-core intrusive links (Vyukov MPSC
   next pointers, per-slot MPMC sequence counters) want atomic fields.
6. **Bounds-check elision for proven-in-range indices** — the canonical
   bounded loop already proves `i < N`; the backend still emits the trap.
   Zero-cost claim is "zero *abstraction* cost"; the safety cost is
   deliberate but should shrink where proofs already discharge it.

## Verdict

The three kernels' structures fall into six patterns; **four run in Oak
today with C output a kernel author would sign** (fixed containers,
index-linked intrusive structures, bitmaps, static state), one is landed
at the hardware-independent level (tables/MMIO), and one is expressible
with discipline but not yet enforced (ownership/refcounts). The pointer
soup that makes the originals unverifiable is replaced by pools and typed
indices — smaller, cache-friendlier, and checkable — rather than imitated.
The abstraction cost is zero (monomorphized generics, matches lowering to
the same tag-guarded C, layout proven and cc-asserted); the safety cost is
explicit traps, with elision-by-proof as the recorded optimization path.
