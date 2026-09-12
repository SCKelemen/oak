import Std.Tactic.BVDecide

/-!
# The total floating-point operations, at the bit level

`asm/floats_lowering.go` models an `f32` as its IEEE 754 pattern for the
theorem decider; the total operations — negation, abs, copysign, the
classifiers, the comparisons, min, max, total_order — are bit operations
over that pattern, exactly the ones defined here over `BitVec 32`, and
`spec/oak/floats.oak` states their laws in Oak. This module proves the
same laws by `bv_decide`, so the two statements meet: the decider's
circuits are these definitions, and the laws hold of them.
-/

namespace Oak.FloatBits

abbrev signMask : BitVec 32 := 0x80000000#32
abbrev magMask : BitVec 32 := 0x7FFFFFFF#32
abbrev expMask : BitVec 32 := 0x7F800000#32
abbrev manMask : BitVec 32 := 0x007FFFFF#32

abbrev neg (x : BitVec 32) : BitVec 32 := x ^^^ signMask
abbrev abs (x : BitVec 32) : BitVec 32 := x &&& magMask
abbrev copysign (x y : BitVec 32) : BitVec 32 := (x &&& magMask) ||| (y &&& signMask)
abbrev isNaN (x : BitVec 32) : Bool := (x &&& expMask == expMask) && !(x &&& manMask == 0)
abbrev isFinite (x : BitVec 32) : Bool := !(x &&& expMask == expMask)
abbrev isInfinite (x : BitVec 32) : Bool := (x &&& expMask == expMask) && (x &&& manMask == 0)
abbrev isNormal (x : BitVec 32) : Bool := !(x &&& expMask == 0) && !(x &&& expMask == expMask)
abbrev sign (x : BitVec 32) : Bool := x.msb
abbrev bothZero (a b : BitVec 32) : Bool := (a ||| b) &&& magMask == 0

/-- IEEE equality over the patterns: NaN unequal to everything, the zeros equal. -/
abbrev feq (a b : BitVec 32) : Bool := !isNaN a && !isNaN b && (a == b || bothZero a b)

/-- IEEE less-than: the sign-magnitude order, NaN below nothing. -/
abbrev flt (a b : BitVec 32) : Bool :=
  !isNaN a && !isNaN b && !bothZero a b &&
    ((sign a && !sign b) ||
     (sign a && sign b && BitVec.ult (b &&& magMask) (a &&& magMask)) ||
     (!sign a && !sign b && BitVec.ult (a &&& magMask) (b &&& magMask)))

/-- The backend's minimum on non-NaN operands: equal operands pick by sign. -/
abbrev fmin (a b : BitVec 32) : BitVec 32 := if feq a b then (if sign a then a else b) else (if flt a b then a else b)
abbrev fmax (a b : BitVec 32) : BitVec 32 := if feq a b then (if sign a then b else a) else (if flt a b then b else a)

abbrev totalKey (x : BitVec 32) : BitVec 32 := if sign x then x ^^^ magMask else x
abbrev totalOrder (a b : BitVec 32) : Bool := BitVec.sle (totalKey a) (totalKey b)


/-- Unfold the bit definitions everywhere and decide over the bit vectors. -/
macro "bits_decide" : tactic =>
  `(tactic| (simp only [neg, abs, copysign, isNaN, isFinite, isInfinite, isNormal, sign, bothZero,
      feq, flt, fmin, fmax, totalKey, totalOrder, signMask, magMask, expMask, manMask] at *; bv_decide))

theorem neg_involutive (x : BitVec 32) : neg (neg x) = x := by bits_decide
theorem abs_idempotent (x : BitVec 32) : abs (abs x) = abs x := by bits_decide
theorem abs_of_neg (x : BitVec 32) : abs (neg x) = abs x := by bits_decide
theorem abs_clears_sign (x : BitVec 32) : abs x &&& signMask = 0 := by bits_decide
theorem copysign_composes (x y z : BitVec 32) : copysign (copysign x y) z = copysign x z := by bits_decide
theorem copysign_abs (x : BitVec 32) : copysign (abs x) x = x := by bits_decide

theorem nan_is_unequal (x : BitVec 32) : isNaN x = !feq x x := by bits_decide
theorem classes_cover (x : BitVec 32) : isNaN x || isInfinite x || isFinite x := by bits_decide
theorem classes_disjoint (x : BitVec 32) :
    !(isNaN x && isInfinite x) && !(isNaN x && isFinite x) && !(isInfinite x && isFinite x) := by bits_decide
theorem normal_is_finite (x : BitVec 32) (h : isNormal x) : isFinite x := by
  bits_decide
theorem neg_keeps_nan (x : BitVec 32) : isNaN (neg x) = isNaN x := by bits_decide

theorem less_irreflexive (x : BitVec 32) : flt x x = false := by bits_decide
theorem less_asymmetric (x y : BitVec 32) (h : flt x y) : flt y x = false := by bits_decide
theorem trichotomy_non_nan (x y : BitVec 32) (hx : isNaN x = false) (hy : isNaN y = false) :
    flt x y || feq x y || flt y x := by bits_decide
theorem neg_reverses_order (x y : BitVec 32) : flt x y = flt (neg y) (neg x) := by bits_decide

theorem total_order_reflexive (x : BitVec 32) : totalOrder x x := by bits_decide
theorem total_order_total (x y : BitVec 32) : totalOrder x y || totalOrder y x := by bits_decide
theorem total_order_antisymmetric (x y : BitVec 32) (hxy : totalOrder x y) (hyx : totalOrder y x) : x = y := by bits_decide
theorem total_order_refines_less (x y : BitVec 32) (h : flt x y) : totalOrder x y := by bits_decide

theorem min_commutative (x y : BitVec 32) (hx : isNaN x = false) (hy : isNaN y = false) : fmin x y = fmin y x := by bits_decide
theorem max_commutative (x y : BitVec 32) (hx : isNaN x = false) (hy : isNaN y = false) : fmax x y = fmax y x := by bits_decide
theorem min_is_operand (x y : BitVec 32) : fmin x y = x ∨ fmin x y = y := by bits_decide
theorem min_orders_zeros : fmin 0 signMask = signMask := by bits_decide

end Oak.FloatBits
