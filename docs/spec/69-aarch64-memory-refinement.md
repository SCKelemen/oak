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
        |
Lean Arm ordered-before projection
        +----> inductive MP / SB / IRIW / full-DMB proofs
        |
Pinned CAT sources + cat2lisp AST
        +----> byte identity + structural projection certificate
        |
Oak barrier words -> Arm Sail decoder
        +----> kernel-checked operation / domain / access type
```

These layers make different claims.

- C11 lowering verifies Oak emits the requested C memory order exactly.
- Assembly inspection verifies the current compiler emits an admitted AArch64
  instruction family for that C operation.
- Lean proves the **abstract admitted instruction class** provides the local
  acquire/release/RCsc capabilities Oak requires.
- Litmus tests verify the language model permits and forbids the intended
  outcomes.
- Lean proves the corresponding machine outcomes from the `bob`, `obs`, and
  irreflexive/transitive `ob` consequences of Arm's official A-profile model.
- Herd's pinned parser structurally certifies that the exact CAT sources contain
  those restricted consequences and their route into `ob`.
- Lean generated from the Arm Sail fragment proves Oak's six barrier words
  decode to their intended DMB, DSB, or ISB operation and option.

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
`Oak.AArch64WeakMemory` proves the matching forbidden machine outcomes from the
ordered-before projection used by Arm's official `aarch64hwreqs.cat` and
`aarch64.cat` model.

The assembly litmus programs in `spec/litmus/aarch64` run with Herdtools7 and
that repository's official `aarch64.cat`, both fixed at commit
`76d5bd259d4c4b553a0f52158b9638559b79a5b5`.  The gate requires `Never` for
the MP stale-payload, STLR/LDAR SB both-zero, full-DMB SB both-zero, and LDAR
IRIW split observations.  It requires `Sometimes` for LDAR/STLR LB both-zero,
so an oracle that simply rejects weak-looking executions cannot pass.

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

## 8. Formal instruction-class and weak-memory models

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

`spec/lean/Oak/AArch64WeakMemory.lean` defines the least transitive relation over
the exact global consequences used from Arm's model: `bob` edges for STLR,
LDAR, STLR-followed-by-LDAR, and full DMB; and external reads-from and
coherence-after edges through `obs`. A valid projected execution supplies only
Arm's external irreflexivity condition. Lean proves:

- release/acquire message passing orders the payload and forbids a stale
  initial-value observation;
- STLR/LDAR seq-cst store buffering cannot return both initial values;
- two LDAR seq-cst readers cannot make the IRIW split observation;
- a full DMB in each thread also excludes the store-buffering outcome;
- Oak's selected instruction classes are exactly STLR, LDAR, and DMB ISH for
  the corresponding source operations.

`semir/aarch64_cat_projection_test.go` mechanically ties that restricted
relation to the pinned model. It byte-compares all 156 tracked
`herd/libdir/*.cat` blobs (and rejects untracked CAT inputs), invokes the pinned
`cat2lisp` beside `herd7`, and checks the include-expanded AST for DMB ISH in
`dmb.full`, the four required `bob` arms, the
`bob -> lob -> local-hw-reqs -> hw-reqs -> ob` and
`rf/ca -> Exp-obs -> obs -> ob` paths, `ob; ob`, and external
`irreflexive ob`. Exact AST hashes make any pin/model drift a reviewed change;
mutation checks show each required edge is fail-closed.

This is mechanical structural provenance for the restricted projection, not a
complete formal semantics of CAT. The local mapping, projection theorems, CAT
certificate, and `Oak.SequentialConsistency` remain separate proof layers so
none is silently substituted for another.

`spec/lean/Oak/AArch64Encoding.lean` and the regenerated Arm Sail bridge also
close the encoding/decoder seam for the barrier subset: the exact words for DMB
ISHLD/ISH/SY, DSB ISH/SY, and ISB are pinned to the generated encoder table and
proved to decode to the intended operation, shareability domain, and access
types. In particular, DMB ISHLD decodes as inner-shareable reads.

## 9. CI gate

The main CI workflow has an independent:

```text
AArch64 Memory Refinement
```

job. It:

1. requires Clang AArch64 freestanding cross-target support;
2. runs the Oak source -> C -> AArch64 assembly checks;
3. runs Oak's language-level memory-model litmus outcomes;
4. builds pinned Herdtools7 and runs the matching assembly cases against the
   official Arm CAT model from the same pinned checkout;
5. requires byte-identical CAT inputs and the parser-AST projection certificate.

The ordinary Go/race, Lean, and golden gates remain in place, so backend
refinement cannot replace source/compiler/formal regression coverage.

Local developers without Clang may skip the assembly tests. CI sets
`OAK_REQUIRE_AARCH64_CLANG=1`, turning absence of the cross compiler into a hard
failure rather than a skipped verification claim.
The Herd test similarly skips without `herd7` or `OAK_HERDTOOLS7_DIR` locally;
CI sets `OAK_REQUIRE_HERD7=1`, so absence, a checkout at the wrong commit, an
unparseable result, or an outcome drift is a hard failure.

## 10. What this does not yet prove

This chapter does **not** claim:

- a complete formal refinement of C11 through LLVM IR to the official Arm
  axiomatic model;
- a complete semantics-preserving translation of the CAT language or the full
  Arm model into Lean;
- a proof that STLR/LDAR/DMB executions generate the assumed Exp/W/R/L/A event
  tags, reads-from, and coherence-after relations;
- exhaustive compiler-version correctness;
- stochastic execution of weak-memory litmus tests on real AArch64 hardware;
- cache/coherency/DMA/device-memory correctness;
- cycle-level WCET for LL/SC retry loops;
- MMIO/barrier correctness for device registers.

The current result is stronger than source-only testing but deliberately weaker
than a full verified compiler/ISA stack.

## 11. Next steps

The next machine-memory work should add:

1. extend the mechanically pinned relation subset into a complete CAT semantics
   and prove the instruction-to-event-tag and `rf`/`ca` generation seams;
2. retained assembly artifacts/version metadata so failures are diagnosable;
3. real AArch64 hardware litmus execution when a CI runner is available;
4. MMIO address spaces and the state/effect contracts beyond the now-proved
   DMB/DSB/ISB decoder options;
5. DMA/coherency and interrupt-boundary ordering;
6. selective implementation-to-Lean refinement where the proof cost is
   justified.

Once this AArch64 refinement gate is stable, Oak has enough demonstrated
shared-memory machinery to begin `SpscRing[T, N]` as the first higher-level
lock-free proof consumer.

**Consumers (landed).** `stdlib/rings.oak` is that consumer: the SPSC,
MPSC, MPMC, and intrusive MPSC rings over caller-owned storage
(`65-machine-memory.md` §1). `compiler/e2e_rings_targets_test.go` compiles
their operations for `aarch64-none-elf -march=armv8-a` and requires the
families this chapter assigns — `stlr` (or `stlxr`) for every release
publication, `ldar` (or `ldaxr`) for every acquire observation, the
exclusive pairs or LSE forms for the claims, an exchange for the intrusive
push; the pthread harness of `compiler/e2e_rings_test.go` runs the same
rings on AArch64 hardware plain and under ThreadSanitizer, and the harness
cross-builds for `linux/arm64`. The happens-before facts they rely on are
`Oak.Rings`' instances of `Oak.HappensBefore`.

The RISC-V counterpart is `69-riscv-memory-refinement.md`.
