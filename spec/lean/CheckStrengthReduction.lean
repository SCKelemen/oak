import Oak.StrengthReduction
import Lean

/-! Check the exact unsigned-division rewrite and its standard-only proof
authority. In particular, the shift count is not assumed to be below the width:
at or beyond 32, the divisor wraps to zero and both sides are zero. -/

open Lean Elab Command
open Oak.StrengthReduction

example (x k : BitVec 32) : x / (1#32 <<< k) = x >>> k := udiv_pow_two_32 x k

-- Zero shift, highest in-range shift, first wrapped divisor, and largest count.
example (x : BitVec 32) : x / (1#32 <<< 0#32) = x := by
  rw [udiv_pow_two_32]
  rfl

example (x : BitVec 32) : x / (1#32 <<< 31#32) = x >>> 31#32 :=
  udiv_pow_two_32 x 31#32

example (x : BitVec 32) : x / (1#32 <<< 32#32) = 0#32 := by
  rw [udiv_pow_two_32, BitVec.ushiftRight_eq', BitVec.ushiftRight_eq_zero (by decide)]

example (x : BitVec 32) : x / (1#32 <<< 4294967295#32) = 0#32 := by
  rw [udiv_pow_two_32, BitVec.ushiftRight_eq', BitVec.ushiftRight_eq_zero (by decide)]

-- Concrete values pin the unsigned top-bit and division-by-zero semantics.
example : 4294967295#32 / (1#32 <<< 31#32) = 1#32 := by decide
example : 4294967295#32 / (1#32 <<< 32#32) = 0#32 := by decide
example : 4294967295#32 / 0#32 = 0#32 := by decide

run_cmd do
  let name := ``Oak.StrengthReduction.udiv_pow_two_32
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "{name} depends on nonstandard axiom {axiomName}"
