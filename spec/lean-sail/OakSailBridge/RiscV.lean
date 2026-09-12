import LeanRV64D
import Std.Tactic.BVDecide

/-!
# Oak's RV64 semantics against the Sail RISC-V model

`Oak.RiscV` (spec/lean/Oak/RiscV.lean) is the verifier's transliteration
of the instructions it decides. The Sail model is the ISA's golden model.
Each theorem below states that, for the register values an instruction
reads, the value the Sail model computes for the destination register (or
the branch decision it takes) is Oak's function of those values. The
generated `execute_*` bodies are `wX_bits rd <value>` around exactly the
expression on the left of each theorem (LeanRV64D/InstsEnd.lean:
`execute_RTYPEW`, `execute_RTYPE`, `execute_BTYPE`), so the theorems are
the data semantics of the instructions with the monadic register plumbing
read off by inspection.

The Oak definitions are restated verbatim (the OAK-DEF blocks);
`asm/rv64_sail_bridge_test.go` checks them against the specification's
file, so the two cannot drift.
-/

namespace OakSailBridge

open LeanRV64D

-- OAK-DEF-BEGIN
abbrev X := BitVec 64

/-- Sign-extend a 32-bit result to the register. -/
def sextW (v : BitVec 32) : X := v.signExtend 64

def addw (a b : X) : X := sextW (a.truncate 32 + b.truncate 32)
def subw (a b : X) : X := sextW (a.truncate 32 - b.truncate 32)
def mulw (a b : X) : X := sextW (a.truncate 32 * b.truncate 32)
def sllw (a b : X) : X := sextW (a.truncate 32 <<< (b.truncate 5).toNat)
def srlw (a b : X) : X := sextW (a.truncate 32 >>> (b.truncate 5).toNat)
def sraw (a b : X) : X := sextW ((a.truncate 32).sshiftRight (b.truncate 5).toNat)

def sll (a b : X) : X := a <<< (b.truncate 6).toNat
def srl (a b : X) : X := a >>> (b.truncate 6).toNat
def sra (a b : X) : X := a.sshiftRight (b.truncate 6).toNat

def slt (a b : X) : X := if a.slt b then 1 else 0
def sltu (a b : X) : X := if a.ult b then 1 else 0

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
-- OAK-DEF-END

/-! ## RTYPEW: `execute_RTYPEW rs2 rs1 rd op` writes
    `sign_extend (m := 64) result` with `rs1_val = extractLsb x1 31 0`. -/

theorem addw_bridge (x1 x2 : X) :
    (sign_extend (m := 64) (Sail.BitVec.extractLsb x1 31 0 + Sail.BitVec.extractLsb x2 31 0)) = addw x1 x2 := by
  simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, addw, sextW]
  bv_decide

theorem subw_bridge (x1 x2 : X) :
    (sign_extend (m := 64) (Sail.BitVec.extractLsb x1 31 0 - Sail.BitVec.extractLsb x2 31 0)) = subw x1 x2 := by
  simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, subw, sextW]
  bv_decide

theorem sllw_bridge (x1 x2 : X) :
    (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb x1 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb x2 31 0) 4 0))) = sllw x1 x2 := by
  simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, shift_bits_left, sllw, sextW]
  bv_decide

theorem srlw_bridge (x1 x2 : X) :
    (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb x1 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb x2 31 0) 4 0))) = srlw x1 x2 := by
  simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, shift_bits_right, srlw, sextW]
  bv_decide

theorem sraw_bridge (x1 x2 : X) :
    (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb x1 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb x2 31 0) 4 0))) = sraw x1 x2 := by
  simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, shift_bits_right_arith, Sail.BitVec.toNatInt, Int.toNat, sraw, sextW]
  bv_decide

/-! ## RTYPE: the comparisons write `zero_extend (bool_to_bit (op x1 x2))`. -/

theorem slt_bridge (x1 x2 : X) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x1 x2))) = slt x1 x2 := by
  simp only [zero_extend, Sail.BitVec.zeroExtend, bool_to_bit, bool_bit_forwards, zopz0zI_s, slt, BitVec.slt]
  by_cases h : x1.toInt < x2.toInt <;> simp [h]

theorem sltu_bridge (x1 x2 : X) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u x1 x2))) = sltu x1 x2 := by
  simp only [zero_extend, Sail.BitVec.zeroExtend, bool_to_bit, bool_bit_forwards, zopz0zI_u, Sail.BitVec.toNatInt, sltu, BitVec.ult]
  by_cases h : x1.toNat < x2.toNat <;> simp [h]

/-! ## BTYPE: `taken` is the comparison; Oak's `Br.holds`. -/

theorem beq_bridge (x1 x2 : X) : (x1 == x2) = Br.holds .beq x1 x2 := rfl

theorem bne_bridge (x1 x2 : X) : (x1 != x2) = Br.holds .bne x1 x2 := rfl

theorem blt_bridge (x1 x2 : X) : zopz0zI_s x1 x2 = Br.holds .blt x1 x2 := by
  simp [zopz0zI_s, Br.holds, BitVec.slt]

theorem bge_bridge (x1 x2 : X) : zopz0zKzJ_s x1 x2 = Br.holds .bge x1 x2 := by
  simp only [zopz0zKzJ_s, Br.holds, BitVec.slt]
  cases h : decide (x1.toInt < x2.toInt) <;> simp_all <;> omega

theorem bltu_bridge (x1 x2 : X) : zopz0zI_u x1 x2 = Br.holds .bltu x1 x2 := by
  simp [zopz0zI_u, Sail.BitVec.toNatInt, Br.holds, BitVec.ult]

theorem bgeu_bridge (x1 x2 : X) : zopz0zKzJ_u x1 x2 = Br.holds .bgeu x1 x2 := by
  simp only [zopz0zKzJ_u, Sail.BitVec.toNatInt, Br.holds, BitVec.ult]
  cases h : decide (x1.toNat < x2.toNat) <;> simp_all <;> omega

end OakSailBridge
