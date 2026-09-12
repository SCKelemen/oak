# RISC-V (RV64) Memory Refinement

Status: implemented as an evidence layer (`codegen/riscv64_memory_refinement_test.go`,
`spec/lean/Oak/RiscVMemory.lean`). The RISC-V counterpart of
`69-aarch64-memory-refinement.md`, for dbs's second target (ask 6,
`docs/notes/dbs-feedback-2026-09.md`).

The same stack, and the same care about what each layer claims:

```text
Oak source atomics
        |
        v
C11 explicit atomics             executable backend mapping (one C for every target)
        |
        v
Clang RV64 assembly              implementation witness
        |
        +----> instruction-family admission checks
        |
Oak language execution model
        +----> SB / MP / LB / IRIW small-state litmus checks (shared)
        |
Lean RVWMO local-order model
        +----> kernel-checked instruction-class capability proofs
```

## 1. What the C11 mapping gives, and what it does not

The ISA's recommended C11 mapping (RISC-V Unprivileged ISA, Appendix A
"Mappings from C/C++ primitives to RISC-V primitives"), as clang emits it
for `-march=rv64gc`:

| C11 operation | RV64 instructions |
| --- | --- |
| load relaxed | `ld` |
| load acquire | `ld; fence r,rw` |
| load seq_cst | `fence rw,rw; ld; fence r,rw` |
| store relaxed | `sd` |
| store release | `fence rw,w; sd` |
| store seq_cst | `fence rw,w; sd; fence rw,rw` |
| RMW relaxed / acquire / release / acq_rel, seq_cst | `amo*` / `amo*.aq` / `amo*.rl` / `amo*.aqrl` |
| CAS relaxed / acq_rel / seq_cst | `lr; sc` / `lr.aq; sc.rl` / `lr.aqrl; sc.rl` |
| fence acquire / release / acq_rel / seq_cst | `fence r,rw` / `fence rw,w` / `fence.tso` / `fence rw,rw` |

Under RVWMO an `.aq` annotation alone, and the `ld; fence r,rw` sequence,
are **RCpc**: a release store and a later acquire load to another address
may reorder — nothing orders the store before the load. This is the RISC-V
analogue of AArch64's `LDAPR`.

## 2. Oak's RISC-V OS-profile acquire

Oak's OS profile requires RCsc acquire for acquire loads and for every
acquiring read-modify-write (`69-aarch64-memory-refinement.md` §2). On
RISC-V that is:

| Oak operation | Admitted RV64 mapping |
| --- | --- |
| acquire load | the seq_cst load sequence `fence rw,rw; ld; fence r,rw` |
| acquire RMW (`fetch_add`, `exchange`) | `amo*.aqrl` |
| acquire and acq_rel compare-exchange | `lr.aqrl; sc.rl` (the seq_cst pair) |

Everything else keeps the C11 mapping. The strengthening is the smallest
one: the Lean model proves the C11 mapping already meets Oak's requirement
for every other order (`c11_amo_valid_except_acquire`,
`c11_lrsc_valid_except_acquires`, `c11_load_valid_except_acquire`).

The backend emits one C translation unit for every target, so the
selection is a preprocessor fact: the atomics prelude defines
`OAK_ORDER_LOAD_ACQUIRE`, `OAK_ORDER_RMW_ACQUIRE`, `OAK_ORDER_CAS_ACQUIRE`,
and `OAK_ORDER_CAS_ACQ_REL` as `memory_order_seq_cst`,
`memory_order_acq_rel`, `memory_order_seq_cst`, `memory_order_seq_cst`
under `__riscv`, and as the plain C11 orders elsewhere. Acquire loads and
RMWs are spelled through these macros; release, relaxed, and seq_cst
orders are spelled literally.

## 3. Lock-free admission

The RISC-V compile carries the same `_Static_assert(__atomic_always_lock_free(...))`
admission for `u8`, `u16`, `u32`, `u64` as the AArch64 layer, so a `rv64gc`
build of a program with a `u32` fetch-add fails in the C compiler rather
than pulling a locked routine from libatomic.

## 4. Formal instruction-class model

`spec/lean/Oak/RiscVMemory.lean` models the local capabilities over the
same `LocalOrdering` (acquire, release, RCsc acquire) as the AArch64 model,
with instruction classes for `fence r,rw`, `fence rw,w`, `fence.tso`,
`fence rw,rw`; loads and stores as an access with fences around it; AMO
annotations `.aq`, `.rl`, `.aqrl`; and LR/SC pairs. Lean proves:

- the C11 acquire load, `amo.aq`, and the `lr.aq; sc.rl` pair do **not**
  satisfy Oak's RCsc acquire (`c11_acquire_load_is_rcpc`,
  `c11_acquire_amo_is_rcpc`, `c11_acqrel_lrsc_is_rcpc`) — the finding that
  set §2;
- Oak's mapping satisfies every required load, store, fence, AMO, and
  LR/SC order (`oak_load_profile_valid`, `oak_store_profile_valid`,
  `oak_fence_profile_valid`, `oak_amo_satisfies_local_order`,
  `oak_lrsc_satisfies_local_order`);
- seq_cst selects the intended classes (`oak_seqCst_amo_is_aqrl`,
  `oak_seqCst_fence_is_full`), and the strengthened spellings are the
  ones the macros select.

These proofs are local, as the AArch64 ones are. `Oak.SequentialConsistency`
remains the separate global-order layer.

## 5. CI gate

The `RISC-V Memory Refinement` job requires a clang with the riscv64
target (`OAK_REQUIRE_RISCV64_CLANG=1` turns absence into a failure),
compiles the Oak-generated atomics for `riscv64-unknown-none-elf
-march=rv64gc`, and checks the instruction families per function: the full
fence before acquire and seq_cst loads, the release fence before release
stores, `.aqrl` on every acquiring AMO and never `.aq` alone, `lr.aqrl`
with `sc.rl` on acquiring compare-exchanges. Locally the test finds clang
on PATH, Homebrew LLVM's, or `zig cc`, and skips without one.

## 6. What this does not yet prove

- That clang's RVWMO lowering of C11 is itself correct; the Sail RISC-V
  golden model is an oracle for the assembler lane (`94-assembler.md` §9),
  not yet for concurrent executions.
- Cycle costs of the strengthened acquire on real cores; the choice is the
  OS profile's simple reviewable rule, as on AArch64, and a weaker RCpc
  source operation stays a separate future contract.
- Anything about the Zacas/Zabha extensions or `amocas`; the model covers
  the `A` extension's AMOs and LR/SC.
