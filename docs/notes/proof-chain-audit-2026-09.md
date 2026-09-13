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
| Oak body ⟶ emitted instructions (`asm.Verify`) | **proved** for linear straight-line bodies (normal forms), **evidence** for bounded loops and span element loads over witnesses, **trusted** past the unrolling budget | **proved** for straight-line vector bodies (2026-09-13, the seventh increment: `asm/verify_vector.go`, `asm/verify_simd.go` — the SIMD corpus, the UTF-8 kernel's `special_cases` and `check_block` on both halves of their vector results), **evidence** for `check_blocks` (the node budget), **trusted** for the loop kernels and `simd.store` | proved / evidence as AArch64, the RV64 lane of the same verifier | **trusted**: the C compiler's output is never compared with the Oak body; the differential tests (C, interpreter, portable, NEON, RVV) are the check |
| Instruction semantics ⟶ the vendor's specification | **proved**: `Oak.AssemblerSemantics` ≡ `Oak.ArmASL` ≡ Sail-generated Lean for `AddWithCarry`, `ConditionHolds`, the conditional selects and compares, `HighestSetBit`/`CountLeadingZeroBits` (`spec/sail/lean/Bridge.lean`); **evidence** on silicon for 181 register-level bodies × 60 inputs | **proved against `Oak.Simd`; the Arm text in place, bridged at the lane level**: the NEON lane functions the verifier applies (`asm/verify_vector.go`) are stated in Lean as `Oak.NeonSemantics` and proved to be the `Oak.Simd` operations; `spec/sail/arm_primitives.sail` carries Arm's own text for every instruction the backend emits (`Elem[]`, `UnsignedSatQ`, `BitCount`, `tbl`, `ext`, `dup`, the lane-wise arithmetic, compares, shifts, reductions, `cnt`, the bitwise forms), Sail generates its Lean, and `spec/sail/lean/Bridge.lean` proves the lane-level identities (`Elem[]` reads the lane, `Ones` is the all-ones lane, `UnsignedSatQ` of a difference is `uqsub`, the `cmeq` test is `cmeq`, the bitwise forms are the operators); the per-lane loops of the generated code are folds over the lane indices and each written lane reads its write, so `dup`, `add`, `sub`, `cmeq` (register and zero forms), `umin`, `umax`, `uqsub`, `tbl`, and `umaxv` are **proved** to compute the verifier's lane functions over the operands' lanes; **open**: `ext`, the shifts, `cnt`, and `Reduce` (recursive; Sail's backend cannot discharge its termination); **evidence** on silicon for 160 vector bodies × 60 inputs | **proved**: `Oak.RiscV` ≡ the Sail RISC-V model's Lean export (bridge, two halves); **evidence**: the Sail emulator and QEMU agree on the differential units | not applicable |
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
  evidence and the loop kernel trusted. What remains open one layer lower
  is the meaning of the instructions themselves: the verifier states that
  `tbl`, `ext`, `cmeq`, `uqsub`, `umaxv`, `sshr`, `addv` are `Oak.Simd`'s
  `tbl`, `prev`, `eqMask`, `subSat`, `anyLane`, `shr`, `movemask` as Go
  lane functions, and `Oak.NeonSemantics` proves the same statements in
  Lean over the same definitions, and the silicon differential checks the
  lane functions against the host core (160 vector bodies × 60 inputs).
  Arm's own text for the instructions is now in `spec/sail/` and generated
  to Lean; the bridge proves the register-level theorems for `dup`, `add`,
  `sub`, `cmeq`, `umin`, `umax`, `uqsub`, `tbl`, and `umaxv` against the
  generated loops, and still owes `ext`, the shifts, `cnt`, and the
  `Reduce` tree.
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
   seventh increment).
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
   verifier's lane functions over the operands' lanes. Still owed: `ext`
   as `Oak.Neon.ext`, the shifts, `cnt`, and Arm's recursive `Reduce`
   (Sail's Lean backend cannot discharge its termination; it stays a hand
   transliteration). Found on the way: the backend drops a tuple
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
