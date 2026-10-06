import Std.Tactic

/-!
# Scalar signed-division lowering

The Core div_s instruction traps on zero and MIN / -1. Oak traps only on zero
and wraps the overflow. The production emitter guards every divisor -1 and
uses wrapping subtraction in that arm. Operands are already evaluated locals.
This proves the numeric lowering law, not the byte parser, local selection,
structured-control lowering, or end-to-end translation refinement.
-/
namespace Oak.WasmNumeric

def oakSignedDiv (width : Nat) (a b : Int) : Option (BitVec width) :=
  if b = 0 then none else some (BitVec.ofInt width (a.tdiv b))

def coreSignedDiv (width : Nat) (a b : Int) : Option (BitVec width) :=
  if b = 0 ∨ (a = -(2 ^ (width - 1) : Int) ∧ b = -1) then none
  else some (BitVec.ofInt width (a.tdiv b))

def loweredSignedDiv (width : Nat) (a b : Int) : Option (BitVec width) :=
  if b = -1 then some (BitVec.ofInt width 0 - BitVec.ofInt width a)
  else coreSignedDiv width a b

/-- In particular this covers every i32 and i64 input pair, including MIN / -1. -/
theorem signed_division_refines (width : Nat) (a b : Int) :
    loweredSignedDiv width a b = oakSignedDiv width a b := by
  by_cases hm : b = -1
  · subst b
    simp [loweredSignedDiv, oakSignedDiv, BitVec.ofInt_neg]
  · simp [loweredSignedDiv, coreSignedDiv, oakSignedDiv, hm]

theorem signed_division_traps_iff (width : Nat) (a b : Int) :
    loweredSignedDiv width a b = none ↔ b = 0 := by
  rw [signed_division_refines]
  simp [oakSignedDiv]

theorem signed_division_neg_one (width : Nat) (a : Int) :
    loweredSignedDiv width a (-1) = some (BitVec.ofInt width (-a)) := by
  rw [signed_division_refines]
  simp [oakSignedDiv]

theorem signed_division_overflow_32 :
    loweredSignedDiv 32 (-2147483648) (-1) = some (BitVec.ofInt 32 (-2147483648)) := by decide

theorem signed_division_overflow_64 :
    loweredSignedDiv 64 (-9223372036854775808) (-1) = some (BitVec.ofInt 64 (-9223372036854775808)) := by decide

end Oak.WasmNumeric
