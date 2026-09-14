# Proof chain audit: from Oak source to the machine, 2026-09-13

The question: for a function written in Oak, how far does a proof carry
today — from the Lean statement about the Oak program, through the
backend that emits it, to the instruction semantics of the processor — and
where does it stop? The answer differs by backend, by lane, and by what
the function uses. Every link below is one of **proved** (a Lean theorem),
**evidence** (agreement on witnesses or on silicon), **audited**
(mechanically compared with the vendor's specification), or **trusted**
(no check beyond tests).

## The links

| Link | AArch64, scalar | AArch64, vectors | RISC-V 64, scalar | Both lanes, C backend |
| --- | --- | --- | --- | --- |
| Oak program ⟶ its specification (the source proofs: `Oak.Utf8Blocks.program_valid`, `Oak.Protocol`, `Oak.Teddy`, `Oak.Simd` lane laws) | proved, about the Oak text extracted to Lean (`codegen/lean`) | proved, the same way | proved, the same way | proved, the same way |
| Oak body ⟶ emitted instructions (`asm.Verify`) | **proved** for linear straight-line bodies (normal forms), **evidence** for bounded loops and span element loads over witnesses, **trusted** past the unrolling budget | **proved** for straight-line vector bodies (2026-09-13, the seventh increment: `asm/verify_vector.go`, `asm/verify_simd.go` — the SIMD corpus, the UTF-8 kernel's `special_cases` and `check_block` on both halves of their vector results), **evidence** for `check_blocks` (the node budget) and for the loop kernel `valid_with` (2026-09-14, the loop increment: 76 concrete inputs; every loop variable is coupled, the tail bytes to their frame slots, and the `error` obligation exceeds the node budget), **trusted** for `simd.store` | proved / evidence as AArch64, the RV64 lane of the same verifier | **trusted**: the C compiler's output is never compared with the Oak body; the differential tests (C, interpreter, portable, NEON, RVV) are the check |
| Instruction semantics ⟶ the vendor's specification | **proved**: `Oak.AssemblerSemantics` ≡ `Oak.ArmASL` ≡ Sail-generated Lean for `AddWithCarry`, `ConditionHolds`, the conditional selects and compares, `HighestSetBit`/`CountLeadingZeroBits` (`spec/sail/lean/Bridge.lean`); **evidence** on silicon for 181 register-level bodies × 60 inputs | **proved against `Oak.Simd`; the Arm text in place, bridged at the lane level**: the NEON lane functions the verifier applies (`asm/verify_vector.go`) are stated in Lean as `Oak.NeonSemantics` and proved to be the `Oak.Simd` operations; `spec/sail/arm_primitives.sail` carries Arm's own text for every instruction the backend emits (`Elem[]`, `UnsignedSatQ`, `BitCount`, `tbl`, `ext`, `dup`, the lane-wise arithmetic, compares, shifts, reductions, `cnt`, the bitwise forms), Sail generates its Lean, and `spec/sail/lean/Bridge.lean` proves the lane-level identities (`Elem[]` reads the lane, `Ones` is the all-ones lane, `UnsignedSatQ` of a difference is `uqsub`, the `cmeq` test is `cmeq`, the bitwise forms are the operators); the per-lane loops of the generated code are folds over the lane indices and each written lane reads its write, so `dup`, `add`, `sub`, `cmeq` (register and zero forms), `umin`, `umax`, `uqsub`, `tbl`, and `umaxv` are **proved** to compute the verifier's lane functions over the operands' lanes; `ext` is the byte-lane `ext`, `ushr` the lane shift, `sshr #7` on bytes the sign fill of `movemask` (decided over the 256 bytes), and Arm's recursive `Reduce` — stated by hand, since Sail's backend cannot discharge its termination — sums eight bytes as `addv`'s fold, and `cnt` is the population count of each lane (Arm's `BitCount` as `Oak.Intrinsics.popcount`) — every vector instruction the backend emits is bridged; **evidence** on silicon for 160 vector bodies × 60 inputs | **proved**: `Oak.RiscV` ≡ the Sail RISC-V model's Lean export (bridge, two halves); **evidence**: the Sail emulator and QEMU agree on the differential units | not applicable |
| Instruction text ⟶ machine word (the encoder) | **audited**: the table is generated from Arm's ISA XML and checked against Arm's Sail decode tree and templates | audited the same way (the NEON encodings are in the table and the audit) | audited against the Sail RISC-V decoder (`rv64_*` tests), RVC forms included | the system assembler, trusted |

## What this means for the golden cases

- The UTF-8 validator, the JSON decoder, and the literal scanner are
  **proved as Oak programs** (`Oak.Utf8Blocks`, `Oak.Teddy` and its masks,
  the protocol laws) and **run through the C backend**, where the last two
  links are trusted. Their speed results are C-backend results.
- Through the native backend the same functions lower to NEON, and
  since the seventh verifier increment (2026-09-13) the straight-line
  vector helpers are **proved** against their Oak bodies at the bit level
  — `special_cases` and `check_block` of the UTF-8 kernel on both halves
  of their vector results, the SIMD corpus entire — with `check_blocks`
  evidence and the loop kernel `valid_with` evidence too since the
  verifier's loop increment (2026-09-14: the vector file and the frame
  are loop-carried, so the kernel's three data-dependent loops are
  summarized and 76 concrete inputs agree; the coupling proof pairs lane
  groups with register halves and proves vector accumulator loops, but
  every loop variable of the kernel's three loops is coupled, the tail
  array's bytes included, since the frame array became loop-carried
  memory, and the one obligation left — `error`'s, the `check_blocks`
  composition — is beyond the node budget). What remains open one layer lower
  is the meaning of the instructions themselves: the verifier states that
  `tbl`, `ext`, `cmeq`, `uqsub`, `umaxv`, `sshr`, `addv` are `Oak.Simd`'s
  `tbl`, `prev`, `eqMask`, `subSat`, `anyLane`, `shr`, `movemask` as Go
  lane functions, and `Oak.NeonSemantics` proves the same statements in
  Lean over the same definitions, and the silicon differential checks the
  lane functions against the host core (160 vector bodies × 60 inputs).
  Arm's own text for the instructions is now in `spec/sail/` and generated
  to Lean; the bridge proves the register-level theorems for `dup`, `add`,
  `sub`, `cmeq`, `umin`, `umax`, `uqsub`, `tbl`, and `umaxv` against the
  generated loops, `ext`, `ushr`, and `sshr #7` on bytes, and the eight-byte
  `Reduce` against the hand-stated tree, and `cnt`: every vector
  instruction the backend emits is bridged to Arm's text.
- Scalar Oak functions without spans beyond the subset — the state
  machines' `next`/`legal` tables, arithmetic helpers, the protocol
  projections without data — are the only functions today whose proof
  reaches the processor's specification, on both lanes.

## What closes the vector link, in order

1. **Vector semantics in the verifier — done (2026-09-13).** A vector
   register as lanes of terms (`asm/verify_vector.go`); the NEON lane-wise
   instructions the native backend emits (`and`, `orr`, `eor`, `add`,
   `sub`, `umin`, `umax`, `cmeq`, `uqsub`, `ushr`, `sshr`, `dup`, `tbl`,
   `ext`, `umaxv`, `addv`, `umov`, `cnt`, `fmov`, the `q`/`d` frame
   accesses and the span `ldr q`) as lane functions; `simd.*` calls in the
   Oak body lowered through `Oak.Simd`'s definitions to the same terms
   (`asm/verify_simd.go`); a vector result decided half by half. Result:
   `special_cases` and `check_block` proven on both halves, `check_blocks`
   evidence, the loop kernel trusted (`docs/spec/94-assembler.md` §8, the
   seventh increment) — then evidence with the loop increment of
   2026-09-14 (vector registers, frame slots and Oak aggregates
   loop-carried; a frame store at a data-dependent index forgets the
   region; conjunctive loop guards recognized).
2. **The NEON meaning proved in Lean — done (2026-09-13).**
   `Oak.NeonSemantics` (`spec/lean/Oak/NeonSemantics.lean`) states each
   instruction's lane function as the verifier applies it and proves it is
   the `Oak.Simd` operation the lowering uses it for: `tbl` is `Simd.tbl`
   with the out-of-range rule, `ext #(16-n)` is `Simd.prev n`, `uqsub` is
   `Simd.subSat`, `cmeq` is `Simd.eqMask`, `add` is `addWrap`, `ushr` is
   `shr`, `umaxv` decides `anyLane` and (after `cmeq #0`) `allLanes`, and
   the `sshr #7`/`and`/`addv`/`orr` sequence is `Simd.movemask 8`.
3. **Grounding against Arm — the text in place, the lane level bridged
   (2026-09-13).** `spec/sail/arm_primitives.sail` carries Arm's Sail for
   `Elem[]`, `UnsignedSatQ`/`SatQ`, `BitCount`, and the execute bodies of
   every vector instruction the backend emits, with the register operands
   as parameters (the adaptations are listed in the file); Sail generates
   the Lean and `Bridge.lean` proves the register-level theorems against
   it: the generated per-lane loops are folds over the lane indices, a
   written lane reads its write, and `dup`, `add`, `sub`, `cmeq` (both
   forms), `umin`, `umax`, `uqsub`, `tbl`, and `umaxv` compute the
   verifier's lane functions over the operands' lanes; `ext` is
   `Oak.Neon.ext` over the byte lanes, `ushr` the lane shift, `sshr #7` on
   bytes the sign fill (decided over the 256 bytes), and the eight-byte
   `Reduce` — stated by hand, since Sail's Lean backend cannot discharge
   its termination — is `addv`'s fold, and `cnt` is the population count
   of each lane (Arm's `BitCount` as `Oak.Intrinsics.popcount`). Nothing
   the backend emits is left unbridged. Found on the way: the backend drops a tuple
   assignment to declared locals (it generated a unit-typed `let` and
   returned the initial values), so `SatQ` and the saturating subtract are
   written with `let` bindings. The silicon half is done: the differential
   runs 160 vector bodies against the host core, and caught the
   lane-narrowing bug on its first run.
4. **RISC-V vectors.** Not lowered natively; the C backend's RVV path is
   trusted. A native RVV lowering would enter at step 1 with the Sail
   RISC-V vector model as its ground.

## What closes the C-backend link

Nothing short of verifying the C compiler; the position stays: the C
backend is the portable realization, checked by the differential suites,
and the native backend is where proofs reach the machine. That makes the
native backend's performance (see `benchmarks/native/`) the condition for
the proved path to also be the fast path.
