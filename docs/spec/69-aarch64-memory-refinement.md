# AArch64 memory refinement: compiler and machine evidence

This chapter begins the refinement from Oak's language-level memory model
(chapters 65–68) to the AArch64 machine profile intended for the operating
system.

The governing rule is:

> A correct source memory model is useful only if the compiler and target
> preserve it.

This layer deliberately uses **several independent forms of evidence** rather
than treating one assembly snapshot as a proof of the entire Arm memory model.

## 1. Evidence layers

The current refinement stack is:

```text
Oak source atomics
        |
        v
C11 explicit atomics             executable backend mapping
        |
        v
Clang AArch64 assembly           implementation witness
        |
        +----> instruction-family admission checks
        |
Oak language execution model
        +----> SB / MP / LB / IRIW small-state litmus checks
        |
Lean AArch64 local-order model
        +----> kernel-checked instruction-class capability proofs
```

These layers make different claims.

- C11 lowering verifies Oak emits the requested C memory order exactly.
- Assembly inspection verifies the current compiler emits an admitted AArch64
  instruction family for that C operation.
- Lean proves the **abstract admitted instruction class** provides the local
  acquire/release/RCsc capabilities Oak requires.
- Litmus tests verify the language model permits and forbids the intended
  outcomes.

No one of these alone is called a complete C/LLVM/Arm axiomatic refinement
proof.

## 2. AArch64 OS-profile acquire semantics

Oak's AArch64 OS profile requires RCsc acquire for ordinary acquire and seq-cst
loads.

The admitted scalar acquire load is:

```text
LDAR
```

`LDAPR` is **not** admitted as an interchangeable implementation of Oak acquire
in this profile. LDAPR has RCpc/AcquirePC semantics rather than the RCsc acquire
class tracked by Oak's machine contract.

This deliberately gives the privileged OS profile a simple, reviewable ordering
rule. A future weaker RCpc source operation can be added explicitly if there is
a demonstrated performance need and a separate semantic contract.

## 3. Baseline ARMv8-A scalar mapping

The assembly gate cross-compiles Oak-generated C with:

```text
clang --target=aarch64-none-elf -march=armv8-a -ffreestanding -O2
```

The admitted scalar families are:

| Oak operation | required baseline family |
| --- | --- |
| relaxed load | `LDR` |
| acquire load | `LDAR` |
| seq-cst load | `LDAR` |
| relaxed store | `STR` |
| release store | `STLR` |
| seq-cst store | `STLR` |
| acquire fence | `DMB ... ISHLD` |
| release fence | `DMB ... ISH` |
| acq-rel fence | `DMB ... ISH` |
| seq-cst fence | `DMB ... ISH` |

The gate rejects `LDAPR` for Oak acquire/seq-cst loads.

Sequential consistency is **not** reduced to one local instruction property.
The global SC relation and read-visibility constraints remain those of chapter
68; the table above records only the target's local operation component.

## 4. Baseline RMW and compare-exchange

Without LSE, the admitted baseline implementation is an exclusive loop.

Relaxed RMW/CAS must use the relaxed pair:

```text
LDXR
STXR
```

Acquire-release and seq-cst RMW/CAS must use:

```text
LDAXR
STLXR
```

The source CAS is strong. The generated loop therefore retries store-exclusive
failure as needed rather than exposing architecture-level exclusive failure as
an Oak CAS failure.

CAS retry count remains potentially unbounded under contention. Nothing in this
mapping changes the realtime rule that lock-free is not equivalent to bounded
WCET.

## 5. ARMv8.1-A + LSE performance profile

The same Oak source is separately cross-compiled for:

```text
-march=armv8.1-a+lse
```

The performance profile expects the compiler to use the single-instruction LSE
forms where available:

| Oak operation | admitted LSE family |
| --- | --- |
| relaxed fetch-add | `LDADD` |
| acq-rel / seq-cst fetch-add | `LDADDAL` |
| relaxed strong CAS | `CAS` |
| acq-rel / seq-cst strong CAS | `CASAL` |

This is both a correctness and performance regression gate: an unexpected
fallback to an out-of-line runtime or unnecessary generic dispatch is visible.

The language semantics do not require LSE. Baseline LL/SC and LSE are two
machine representations of the same Oak atomic operation.

## 6. Target lock-free admission

The cross-target compilation includes compile-time assertions that Oak's current
v1 atomic carriers are always lock-free for the AArch64 target profile:

```text
u8
u16
u32
u64
```

Signed carriers have the same widths/storage requirements.

This converts lock-freedom from an assumption into a target admission check for
the compiler/architecture tuple exercised by CI.

It does not imply arbitrary aggregate or pointer atomics are lock-free, and it
does not yet prove a cycle-level WCET bound.

## 7. Litmus outcomes

`semir/memory_litmus_test.go` exercises canonical small-state outcomes using the
same execution/HB/MO/SC validators that define Oak's language model.

### 7.1 Message passing (MP)

Release/acquire publication establishes:

```text
payload write HB payload read
```

when the acquire observes the release flag publication.

### 7.2 Store buffering (SB)

For seq-cst stores followed by seq-cst loads, the both-zero outcome is forbidden.
The test exhausts every candidate global SC order and verifies none satisfies
the witness constraints.

For all-relaxed atomics, the both-zero outcome remains allowed and data-race-free.
This guards against accidentally making relaxed atomics stronger than specified.

### 7.3 IRIW

Two seq-cst readers cannot observe two seq-cst writers in contradictory orders.
The test exhausts all candidate global SC orders for the six-event execution
and verifies the split observation has no valid witness.

### 7.4 Load buffering (LB)

The seq-cst both-zero load-buffering outcome is allowed when both loads occur
before both stores in one valid global order.

This negative/positive pair matters: the checker must implement Oak's actual
memory contract rather than merely rejecting every weak-looking outcome.

## 8. Formal instruction-class model

`spec/lean/Oak/AArch64Memory.lean` models local ordering capabilities:

```text
acquire
release
RCsc acquire
```

and instruction classes for:

- `LDR`, `LDAR`, `LDAPR`;
- `STR`, `STLR`;
- `DMB ISHLD`, `DMB ISH`;
- baseline exclusive load/store pairs;
- LSE relaxed/acquire/release/acq-rel RMW classes.

Lean proves:

- baseline load mappings satisfy their required local order;
- baseline store mappings satisfy their required local order;
- baseline fence mappings satisfy their required local order;
- every baseline RMW order maps to a sufficient exclusive pair;
- every LSE RMW order maps to a sufficient LSE class;
- `LDAR` satisfies Oak's RCsc acquire requirement;
- `LDAPR` does **not** satisfy that profile requirement;
- seq-cst load/store/fence select the intended local instruction classes.

These proofs are intentionally local. `Oak.SequentialConsistency` remains the
separate global-order proof layer.

## 9. CI gate

The main CI workflow has an independent:

```text
AArch64 Memory Refinement
```

job. It:

1. requires Clang AArch64 freestanding cross-target support;
2. runs the Oak source -> C -> AArch64 assembly checks;
3. runs the memory-model litmus outcomes.

The ordinary Go/race, Lean, and golden gates remain in place, so backend
refinement cannot replace source/compiler/formal regression coverage.

Local developers without Clang may skip the assembly tests. CI sets
`OAK_REQUIRE_AARCH64_CLANG=1`, turning absence of the cross compiler into a hard
failure rather than a skipped verification claim.

## 10. What this does not yet prove

This chapter does **not** claim:

- a complete formal refinement of C11 through LLVM IR to the official Arm
  axiomatic model;
- exhaustive compiler-version correctness;
- stochastic execution of weak-memory litmus tests on real AArch64 hardware;
- cache/coherency/DMA/device-memory correctness;
- cycle-level WCET for LL/SC retry loops;
- MMIO/barrier correctness for device registers.

The current result is stronger than source-only testing but deliberately weaker
than a full verified compiler/ISA stack.

## 11. Next steps

The next machine-memory work should add:

1. retained assembly artifacts/version metadata so failures are diagnosable;
2. real AArch64 hardware litmus execution when a CI runner is available;
3. MMIO address spaces and AArch64 `DMB`/`DSB`/`ISB` contracts;
4. DMA/coherency and interrupt-boundary ordering;
5. selective implementation-to-Lean refinement where the proof cost is
   justified.

Once this AArch64 refinement gate is stable, Oak has enough demonstrated
shared-memory machinery to begin `SpscRing[T, N]` as the first higher-level
lock-free proof consumer.
