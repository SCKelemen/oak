import Oak.RiscV

/-!
# Oak's RV64 semantics against the Sail RISC-V model's definitions

The Sail RISC-V model is the ratified golden model of the ISA. Its Lean
export (`sail --lean`, `external/sail-riscv`) spells each instruction's
`execute` as register plumbing around a pure expression over the Sail Lean
library's bit-vector primitives (`Sail.BitVec.extractLsb`, `signExtend`,
…) and the model's prelude helpers (`zopz0zI_s` is `<_s`, `bool_to_bit`,
`shift_bits_*`). This module restates those primitives and helpers
verbatim (`asm/rv64_sail_bridge_test.go` checks them against the fetched
library and export) and proves that the expression the model computes
for each instruction the verifier decides is `Oak.RiscV`'s function of the
same register values:

* `execute_RTYPEW rs2 rs1 rd op` writes `sign_extend (m := 64) result` with
  `rs1_val = extractLsb x1 31 0` — `addw`, `subw`, `sllw`, `srlw`, `sraw`;
* `execute_RTYPE` writes `zero_extend (bool_to_bit (op x1 x2))` for the
  comparisons — `slt`, `sltu`;
* `execute_BTYPE` takes the branch when the comparison holds — the six
  branch conditions of `Br.holds`.

The same theorems live in `spec/lean-sail/` against the export itself;
that project builds once the export is regenerated with a Sail newer than
the opam release (`docs/spec/94-assembler.md` §9).
-/

namespace Oak.SailRiscVBridge

open Oak.RiscV

/-! ## Verbatim: lean-sail `Sail/Sail.lean` (rev v4) -/
namespace Sail.BitVec
def toNatInt {w : Nat} (x : BitVec w) : Int := Int.ofNat x.toNat
def signExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' := x.signExtend w'
def zeroExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' := x.zeroExtend w'
def extractLsb {w : Nat} (x : BitVec w) (hi lo : Nat) : BitVec (hi - lo + 1) := x.extractLsb hi lo
end Sail.BitVec
def shift_bits_left (bv : BitVec n) (sh : BitVec m) : BitVec n := bv <<< sh
def shift_bits_right (bv : BitVec n) (sh : BitVec m) : BitVec n := bv >>> sh
notation:50 x "<b" y => decide (x < y)
notation:50 x "≥b" y => decide (x ≥ y)

/-! ## Verbatim: the export's `LeanRV64D/Prelude.lean` (Sail 0.20.2) -/
def sign_extend {m : _} (v : (BitVec k_n)) : (BitVec m) := (Sail.BitVec.signExtend v m)
def zero_extend {m : _} (v : (BitVec k_n)) : (BitVec m) := (Sail.BitVec.zeroExtend v m)
def bool_bit_forwards (arg_ : Bool) : (BitVec 1) :=
  match arg_ with
  | true => 1#1
  | false => 0#1
def bool_to_bit (x : Bool) : (BitVec 1) := (bool_bit_forwards x)
def zopz0zI_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool := ((BitVec.toInt x) <b (BitVec.toInt y))
def zopz0zKzJ_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool := ((BitVec.toInt x) ≥b (BitVec.toInt y))
def zopz0zI_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool := ((Sail.BitVec.toNatInt x) <b (Sail.BitVec.toNatInt y))
def zopz0zKzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool := ((Sail.BitVec.toNatInt x) ≥b (Sail.BitVec.toNatInt y))
/-- The export spells the amount as an `Int`; the shift takes it as the
    natural it is (a bit-vector's `toNat` is never negative). -/
def shift_bits_right_arith (value : (BitVec k_n)) (shift : (BitVec k_m)) : (BitVec k_n) := (BitVec.sshiftRight value (Sail.BitVec.toNatInt shift).toNat)

/-! ## RTYPEW -/

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

/-! ## RTYPE comparisons -/

theorem slt_bridge (x1 x2 : X) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x1 x2))) = slt x1 x2 := by
  simp only [zero_extend, Sail.BitVec.zeroExtend, bool_to_bit, bool_bit_forwards, zopz0zI_s, slt, BitVec.slt]
  by_cases h : x1.toInt < x2.toInt <;> simp [h]

theorem sltu_bridge (x1 x2 : X) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u x1 x2))) = sltu x1 x2 := by
  simp only [zero_extend, Sail.BitVec.zeroExtend, bool_to_bit, bool_bit_forwards, zopz0zI_u, Sail.BitVec.toNatInt, sltu, BitVec.ult]
  by_cases h : x1.toNat < x2.toNat <;> simp [h]

/-! ## BTYPE -/

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

end Oak.SailRiscVBridge
