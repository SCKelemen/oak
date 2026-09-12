import Oak.AssemblerSemantics

/-!
# The RV64 lane (docs/spec/94-assembler.md §9)

The instruction semantics the Go verifier's RV64 lane transliterates
(`asm/rv64_verify.go`), over 64-bit registers:

* the W-forms compute at 32 bits and sign-extend (`addw`, `subw`, `sllw`,
  `srlw`, `sraw`, `mulw`, and `sext.w`);
* `slt`/`sltu` are the signed and unsigned comparisons as 0/1 values;
* the divisions are total: a zero divisor yields all ones for the quotient
  and the dividend for the remainder; the signed overflow yields the
  dividend and remainder 0 (`rv64Divide` in `asm/isa_semantics.go`);
* a conditional branch compares two registers — there are no flags. The
  bridge to the AArch64 lane is `Br.holds_eq_condHolds`: each branch holds
  exactly when the AArch64 condition code the verifier assigns to it
  (`rv64BranchCodes`) holds on the flags of the same subtraction. So the
  comparison term the two lanes share (`cmpTerm`) has one meaning.

The LP64 psABI's widening of narrow integer parameters is `widen`: a value
narrower than 64 bits is extended by its own sign to 32 bits, then
sign-extended to 64 (so a `u32` arrives sign-extended, its upper half
determined, unlike AAPCS64's unspecified bits).
-/

namespace Oak.RiscV

open Oak.AssemblerSemantics

abbrev X := BitVec 64

/-- Sign-extend a 32-bit result to the register. -/
def sextW (v : BitVec 32) : X := v.signExtend 64

def addw (a b : X) : X := sextW (a.truncate 32 + b.truncate 32)
def subw (a b : X) : X := sextW (a.truncate 32 - b.truncate 32)
def mulw (a b : X) : X := sextW (a.truncate 32 * b.truncate 32)
def sllw (a b : X) : X := sextW (a.truncate 32 <<< (b.truncate 5).toNat)
def srlw (a b : X) : X := sextW (a.truncate 32 >>> (b.truncate 5).toNat)
def sraw (a b : X) : X := sextW ((a.truncate 32).sshiftRight (b.truncate 5).toNat)
/-- `sext.w rd, rs` is `addiw rd, rs, 0`. -/
def sextw (a : X) : X := addw a 0

def sll (a b : X) : X := a <<< (b.truncate 6).toNat
def srl (a b : X) : X := a >>> (b.truncate 6).toNat
def sra (a b : X) : X := a.sshiftRight (b.truncate 6).toNat

def slt (a b : X) : X := if a.slt b then 1 else 0
def sltu (a b : X) : X := if a.ult b then 1 else 0

def divu (a b : X) : X := if b = 0 then BitVec.allOnes 64 else a / b
def remu (a b : X) : X := if b = 0 then a else a % b
def div (a b : X) : X :=
  if b = 0 then BitVec.allOnes 64
  else if a = BitVec.intMin 64 ∧ b = BitVec.allOnes 64 then a
  else a.sdiv b
def rem (a b : X) : X :=
  if b = 0 then a
  else if a = BitVec.intMin 64 ∧ b = BitVec.allOnes 64 then 0
  else a.srem b

/-- The W-forms are the 64-bit operation truncated and sign-extended: the
    verifier may compute either way. -/
theorem addw_eq (a b : X) : addw a b = sextW ((a + b).truncate 32) := by
  simp only [addw, sextW]; bv_decide
theorem subw_eq (a b : BitVec 64) : subw a b = sextW ((a - b).truncate 32) := by
  simp only [subw, sextW]; bv_decide
theorem mulw_eq (a b : X) : mulw a b = sextW ((a * b).truncate 32) := by
  simp only [mulw, sextW]; bv_decide

/-- A W-form result is a fixed point of `sext.w`. -/
theorem sextw_addw (a b : X) : sextw (addw a b) = addw a b := by
  simp only [sextw, addw, sextW]; bv_decide

/-- The low 32 bits of a W-form result are the 32-bit operation. -/
theorem addw_truncate (a b : X) : (addw a b).truncate 32 = a.truncate 32 + b.truncate 32 := by
  simp only [addw, sextW]; bv_decide

/-- The total divisions at the edges. -/
theorem divu_zero (a : X) : divu a 0 = BitVec.allOnes 64 := by simp [divu]
theorem remu_zero (a : X) : remu a 0 = a := by simp [remu]
theorem div_zero (a : X) : div a 0 = BitVec.allOnes 64 := by simp [div]
theorem rem_zero (a : X) : rem a 0 = a := by simp [rem]
theorem div_overflow : div (BitVec.intMin 64) (BitVec.allOnes 64) = BitVec.intMin 64 := by
  simp [div]
theorem rem_overflow : rem (BitVec.intMin 64) (BitVec.allOnes 64) = 0 := by
  simp [rem]

/-- The conditional branches: two registers compared, no flags. -/
inductive Br where
  | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, Repr

def Br.holds : Br → X → X → Bool
  | .beq, a, b => decide (a = b)
  | .bne, a, b => !decide (a = b)
  | .blt, a, b => a.slt b
  | .bge, a, b => !(a.slt b)
  | .bltu, a, b => a.ult b
  | .bgeu, a, b => !(a.ult b)

/-- The AArch64 condition code the verifier assigns to each branch
    (`rv64BranchCodes` in `asm/rv64_verify.go`). -/
def Br.cond : Br → Cond
  | .beq => .eq
  | .bne => .ne
  | .blt => .lt
  | .bge => .ge
  | .bltu => .lo
  | .bgeu => .hs

/-- `bltu` is the `lo` code on the flags of `a - b`. -/
theorem bltu_holds (a b : X) : a.ult b = condHolds .lo a b := by
  cases hc : condHolds .lo a b
  · apply Bool.eq_false_iff.mpr
    intro h
    have := (lo_holds_iff a b).mpr h
    rw [hc] at this
    exact Bool.false_ne_true this
  · exact (lo_holds_iff a b).mp hc

/-- `beq` is the `eq` code. -/
theorem beq_holds (a b : X) : decide (a = b) = condHolds .eq a b := by
  cases hc : condHolds .eq a b
  · apply Bool.eq_false_iff.mpr
    intro h
    have := (eq_holds_iff a b).mpr (of_decide_eq_true h)
    rw [hc] at this
    exact Bool.false_ne_true this
  · exact decide_eq_true ((eq_holds_iff a b).mp hc)

/-- The bridge: a branch holds exactly when its condition code holds on
    the flags of `a - b`. The comparison term is shared between the lanes
    with one meaning. -/
theorem Br.holds_eq_condHolds (br : Br) (a b : X) : br.holds a b = condHolds br.cond a b := by
  cases br
  · exact beq_holds a b
  · show (!decide (a = b)) = condHolds .ne a b
    have : condHolds .ne a b = !condHolds .eq a b := by simp [condHolds, Cond.holds]
    rw [this, beq_holds]
  · exact (lt_holds_eq_slt_w64 a b).symm
  · exact (ge_holds_eq_not_slt_w64 a b).symm
  · exact bltu_holds a b
  · show (!(a.ult b)) = condHolds .hs a b
    have : condHolds .hs a b = !condHolds .lo a b := by simp [condHolds, Cond.holds]
    rw [this, bltu_holds]

/-- `slt` is the `lt` comparison term as a 0/1 value; `sltu` the `lo` one. -/
theorem slt_eq_cond (a b : X) : slt a b = (if condHolds .lt a b then 1 else 0) := by
  simp only [slt, lt_holds_eq_slt_w64]
theorem sltu_eq_cond (a b : X) : sltu a b = (if condHolds .lo a b then 1 else 0) := by
  simp only [sltu]
  by_cases h : a.ult b
  · rw [if_pos h, if_pos ((lo_holds_iff a b).mpr h)]
  · have hc : condHolds .lo a b = false := by
      cases hc : condHolds .lo a b
      · rfl
      · exact absurd ((lo_holds_iff a b).mp hc) h
    rw [if_neg h, if_neg (by simp [hc])]

/-- The psABI widening of a `w`-bit integer parameter (`w ≤ 32`): by its
    own sign to 32 bits, then sign-extended to 64. -/
def widen (w : Nat) (signed : Bool) (v : BitVec w) : X :=
  sextW (if signed then v.signExtend 32 else v.zeroExtend 32)

/-- The low bits of a widened parameter are the parameter: the verifier's
    binding reads them back at the declared width. -/
theorem widen_truncate_u32 (v : BitVec 32) : (widen 32 false v).truncate 32 = v := by
  simp only [widen, sextW]; bv_decide
theorem widen_truncate_i32 (v : BitVec 32) : (widen 32 true v).truncate 32 = v := by
  simp only [widen, sextW]; bv_decide
theorem widen_truncate_u8 (v : BitVec 8) : (widen 8 false v).truncate 8 = v := by
  simp only [widen, sextW]; bv_decide
theorem widen_truncate_i8 (v : BitVec 8) : (widen 8 true v).truncate 8 = v := by
  simp only [widen, sextW]; bv_decide

/-- A widened `u32` parameter is already a W-form fixed point: `sext.w`
    on it is the identity, which is why `addw` on two widened `u32`s is
    their 32-bit sum widened. -/
theorem addw_widen (x y : BitVec 32) :
    addw (widen 32 false x) (widen 32 false y) = widen 32 false (x + y) := by
  simp only [addw, widen, sextW]; bv_decide

end Oak.RiscV
