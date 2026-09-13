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
| Oak body ⟶ emitted instructions (`asm.Verify`) | **proved** for linear straight-line bodies (normal forms), **evidence** for bounded loops and span element loads over witnesses, **trusted** past the unrolling budget | **trusted**: a vector parameter, local, load, or instruction ends verification ("vector or non-integer parameters", "a vector-register load", "a floating-point or vector instruction") | proved / evidence as AArch64, the RV64 lane of the same verifier | **trusted**: the C compiler's output is never compared with the Oak body; the differential tests (C, interpreter, portable, NEON, RVV) are the check |
| Instruction semantics ⟶ the vendor's specification | **proved**: `Oak.AssemblerSemantics` ≡ `Oak.ArmASL` ≡ Sail-generated Lean for `AddWithCarry`, `ConditionHolds`, the conditional selects and compares, `HighestSetBit`/`CountLeadingZeroBits` (`spec/sail/lean/Bridge.lean`); **evidence** on silicon for 181 register-level bodies × 60 inputs | **absent**: no NEON semantics in the verifier, none in `Oak.ArmASL`, none in `spec/sail/arm_primitives.sail`, no vector body in the silicon differential | **proved**: `Oak.RiscV` ≡ the Sail RISC-V model's Lean export (bridge, two halves); **evidence**: the Sail emulator and QEMU agree on the differential units | not applicable |
| Instruction text ⟶ machine word (the encoder) | **audited**: the table is generated from Arm's ISA XML and checked against Arm's Sail decode tree and templates | audited the same way (the NEON encodings are in the table and the audit) | audited against the Sail RISC-V decoder (`rv64_*` tests), RVC forms included | the system assembler, trusted |

## What this means for the golden cases

- The UTF-8 validator, the JSON decoder, and the literal scanner are
  **proved as Oak programs** (`Oak.Utf8Blocks`, `Oak.Teddy` and its masks,
  the protocol laws) and **run through the C backend**, where the last two
  links are trusted. Their speed results are C-backend results.
- Through the native backend (landed today for the vectors) the same
  functions lower to NEON, but the verifier marks every one of them
  trusted the moment it meets a vector, so the chain has the same open
  link as the C path, one layer lower: nothing yet states that the
  emitted `tbl`, `ext`, `cmeq`, `uqsub`, `umaxv`, `sshr`, `addv` mean what
  `Oak.Simd`'s `tbl`, `prev`, `eqMask`, `subSat`, `anyLane`, `shr`,
  `movemask` mean.
- Scalar Oak functions without spans beyond the subset — the state
  machines' `next`/`legal` tables, arithmetic helpers, the protocol
  projections without data — are the only functions today whose proof
  reaches the processor's specification, on both lanes.

## What closes the vector link, in order

1. **Vector semantics in the verifier.** A vector register as sixteen lane
   terms; the NEON lane-wise instructions the native backend emits (`and`,
   `orr`, `eor`, `add`, `sub`, `umin`, `umax`, `cmeq`, `uqsub`, `ushr`,
   `sshr`, `dup`, `tbl`, `ext`, `umaxv`, `addv`, `umov`, `cnt`) as lane
   functions; `simd.*` calls in the Oak body lowered through `Oak.Simd`'s
   definitions to the same terms. Result: proof or evidence verdicts for
   the straight-line vector helpers (`check_block`, `special_cases`,
   `classify`), evidence for the kernels with loops.
2. **The NEON meaning proved in Lean.** `Oak.NeonSemantics` stating each
   instruction's lane function and theorems that it is the `Oak.Simd`
   operation the lowering uses it for (`tbl` is `Simd.tbl` with the
   out-of-range rule, `ext #(16-n)` is `Simd.prev n`, `uqsub` is
   `Simd.subSat`, `cmeq` is `Simd.eqMask`, the `sshr`/`and`/`addv`
   sequence is `Simd.movemask`).
3. **Grounding against Arm.** The Sail text of the vector primitives
   (`Elem[]`, `UnsignedSatQ`, `BitCount`, the `ext` and `tbl` index
   functions) added to `spec/sail/arm_primitives.sail`, Lean generated,
   and `Oak.NeonSemantics` proved equal to it, as `Oak.ArmASL` is today;
   vector bodies added to the silicon differential.
4. **RISC-V vectors.** Not lowered natively; the C backend's RVV path is
   trusted. A native RVV lowering would enter at step 1 with the Sail
   RISC-V vector model as its ground.

## What closes the C-backend link

Nothing short of verifying the C compiler; the position stays: the C
backend is the portable realization, checked by the differential suites,
and the native backend is where proofs reach the machine. That makes the
native backend's performance (see `benchmarks/native/`) the condition for
the proved path to also be the fast path.
