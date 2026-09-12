import Std.Tactic.BVDecide

/-! # Compiler correspondence for checked, saturating and trapping arithmetic

`docs/spec/20-types.md` §11.1a gives the arithmetic family one meaning over
the exact (mathematical) result of `a + b`, `a - b`, `a * b`:

* `{type}_checked_{op}(a, b)` is `Ok(exact)` when the exact result is in the
  type's range and `Err(Overflow)` otherwise;
* `{type}_saturating_{op}(a, b)` is the exact result clamped to the range,
  *on the side it left*;
* `{type}_trapping_{op}(a, b)` is the exact result when it fits, otherwise
  the program stops at a located trap.

The C backend (`codegen/arithmetic.go`, `arithmeticHelperSource`) realizes
them over the type-generic overflow builtins:

```c
static inline T oak_arith_T_checked_OP( T a, T b ) {
  T r;
  if (__builtin_OP_overflow(a, b, &r)) { return Result_Err(Overflow); }
  return Result_Ok(r);
}
static inline T oak_arith_T_saturating_OP( T a, T b ) {
  T r;
  if (__builtin_OP_overflow(a, b, &r)) {
    return (UPWARD) ? MAX : MIN;
  }
  return r;
}
static inline T oak_arith_T_trapping_OP( T a, T b, const char *file, u32 line ) {
  T r;
  if (__builtin_OP_overflow(a, b, &r)) { oak_overflow_trap(file, line); }
  return r;
}
```

where `UPWARD` is a cheap sign test chosen per operation and signedness:
unsigned `add` and `mul` say `1`, unsigned `sub` says `0`, signed `add`
says `b > 0`, signed `sub` says `b < 0`, and signed `mul` says
`(a < 0) == (b < 0)`.

The builtins' contract (GCC/Clang, "Built-in Functions to Perform
Arithmetic with Overflow Checking"): the operation is performed as if in
infinite precision, the result is stored wrapped, and the builtin returns
true exactly when the infinite-precision result does not fit the result
type. This module models that contract over `Int` with the type's bounds
as parameters, transliterates each helper body, and proves:

* `checked` is `Ok(exact)` exactly when the exact result is in range;
* `trapping` returns the exact result when it fits and traps otherwise;
* every `UPWARD` test equals "the exact result is above `hi`" whenever the
  builtin reported overflow and the operands are in range — so
  `saturating` clamps on the side the exact result left, which is the
  spec's clause and the theorem the cheap tests were chosen for.

The bounds are abstract: `lo ≤ 0 ≤ hi` for the unsigned case (`lo = 0`)
and `lo < 0 < hi` for the signed one, which every `u8..u64`, `i8..i64`
satisfies. The emitted helper text is pinned to this transliteration by
`codegen/checked_arithmetic_refinement_test.go`.

The correspondence is scoped: it covers the helpers' decisions given the
builtins' contract; the builtins themselves and `Result`'s constructors
are assumed. -/

namespace Oak.CheckedArithmeticRefinement

inductive Op where
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The exact (infinite-precision) result. -/
def exact : Op → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- The builtin's report: the exact result does not fit `[lo, hi]`. -/
def overflow (lo hi : Int) (e : Int) : Prop := e < lo ∨ hi < e

instance (lo hi e : Int) : Decidable (overflow lo hi e) := by
  unfold overflow; infer_instance

/-- The spec's clamp: the exact result, or the bound on the side it left. -/
def clamp (lo hi e : Int) : Int := if e < lo then lo else if hi < e then hi else e

/-! ## checked -/

inductive Checked where
  | ok (value : Int)
  | overflowed
  deriving DecidableEq, Repr

/-- `if (__builtin_OP_overflow(a, b, &r)) return Err; return Ok(r)`. -/
def checked (lo hi : Int) (op : Op) (a b : Int) : Checked :=
  if overflow lo hi (exact op a b) then .overflowed else .ok (exact op a b)

theorem checked_ok_iff (lo hi : Int) (op : Op) (a b : Int) :
    checked lo hi op a b = .ok (exact op a b) ↔ lo ≤ exact op a b ∧ exact op a b ≤ hi := by
  unfold checked overflow
  constructor
  · intro h
    by_cases hlt : exact op a b < lo
    · simp [hlt] at h
    · by_cases hgt : hi < exact op a b
      · simp [hlt, hgt] at h
      · omega
  · intro h
    have : ¬ (exact op a b < lo ∨ hi < exact op a b) := by omega
    simp [this]

theorem checked_err_iff (lo hi : Int) (op : Op) (a b : Int) :
    checked lo hi op a b = .overflowed ↔ (exact op a b < lo ∨ hi < exact op a b) := by
  unfold checked overflow
  by_cases h : exact op a b < lo ∨ hi < exact op a b <;> simp [h]

/-! ## trapping -/

/-- `if (__builtin_OP_overflow(a, b, &r)) oak_overflow_trap(); return r`:
    `none` is the trap. -/
def trapping (lo hi : Int) (op : Op) (a b : Int) : Option Int :=
  if overflow lo hi (exact op a b) then none else some (exact op a b)

theorem trapping_exact (lo hi : Int) (op : Op) (a b : Int)
    (h : lo ≤ exact op a b ∧ exact op a b ≤ hi) : trapping lo hi op a b = some (exact op a b) := by
  unfold trapping overflow
  have : ¬ (exact op a b < lo ∨ hi < exact op a b) := by omega
  simp [this]

theorem trapping_traps (lo hi : Int) (op : Op) (a b : Int)
    (h : exact op a b < lo ∨ hi < exact op a b) : trapping lo hi op a b = none := by
  unfold trapping overflow
  simp [h]

/-! ## saturating -/

/-- The C `UPWARD` test, per operation and signedness. -/
def upward (signed : Bool) : Op → Int → Int → Bool
  | .add, _, b => if signed then decide (b > 0) else true
  | .sub, _, b => if signed then decide (b < 0) else false
  | .mul, a, b => if signed then decide ((a < 0) = (b < 0)) else true

/-- `if (overflow) return UPWARD ? MAX : MIN; return r`. -/
def saturating (signed : Bool) (lo hi : Int) (op : Op) (a b : Int) : Int :=
  if overflow lo hi (exact op a b) then (if upward signed op a b then hi else lo) else exact op a b

/-- The load-bearing lemma: whenever the builtin reports overflow and the
    operands are in range, the cheap sign test says exactly whether the
    exact result is above `hi`. Unsigned bounds are `0 ≤ … ≤ hi`, signed
    bounds `lo < 0 < hi`. -/
theorem upward_iff_above (signed : Bool) (lo hi : Int) (op : Op) (a b : Int)
    (hsigned : signed = true → lo < 0 ∧ 0 < hi)
    (hunsigned : signed = false → lo = 0 ∧ 0 ≤ hi)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi)
    (hover : exact op a b < lo ∨ hi < exact op a b) :
    upward signed op a b = true ↔ hi < exact op a b := by
  cases signed with
  | false =>
    have hu := hunsigned rfl
    cases op with
    | add =>
      simp [upward, exact] at hover ⊢
      all_goals omega
    | sub =>
      simp [upward, exact] at hover ⊢
      all_goals omega
    | mul =>
      have hnn : 0 ≤ a * b := Int.mul_nonneg (by omega) (by omega)
      simp [upward, exact] at hover ⊢
      all_goals omega
  | true =>
    have hs := hsigned rfl
    cases op with
    | add =>
      simp only [upward, exact, if_true, decide_eq_true_eq] at hover ⊢
      constructor <;> intro h <;> omega
    | sub =>
      simp only [upward, exact, if_true, decide_eq_true_eq] at hover ⊢
      constructor <;> intro h <;> omega
    | mul =>
      simp only [upward, exact, if_true, decide_eq_true_eq] at hover ⊢
      constructor
      · intro hsame
        rcases hover with hlow | hhigh
        · exfalso
          -- same signs: the product is nonnegative, so it cannot fall below lo < 0
          by_cases hneg : a < 0
          · have hbneg : b < 0 := by rw [← hsame]; exact hneg
            have : 0 < a * b := Int.mul_pos_of_neg_of_neg hneg hbneg
            omega
          · have hbnn : ¬ b < 0 := by rw [← hsame]; exact hneg
            have : 0 ≤ a * b := Int.mul_nonneg (by omega) (by omega)
            omega
        · exact hhigh
      · intro hhigh
        -- above hi > 0: the product is positive, so the signs agree
        by_cases hneg : a < 0
        · by_cases hbneg : b < 0
          · simp [hneg, hbneg]
          · exfalso
            have h := Int.mul_nonneg (show (0 : Int) ≤ -a by omega) (show (0 : Int) ≤ b by omega)
            rw [Int.neg_mul] at h
            omega
        · by_cases hbneg : b < 0
          · exfalso
            have h := Int.mul_nonneg (show (0 : Int) ≤ a by omega) (show (0 : Int) ≤ -b by omega)
            rw [Int.mul_neg] at h
            omega
          · simp [hneg, hbneg]

/-- **Saturation clamps on the side the exact result left.** -/
theorem saturating_clamps (signed : Bool) (lo hi : Int) (op : Op) (a b : Int)
    (hsigned : signed = true → lo < 0 ∧ 0 < hi)
    (hunsigned : signed = false → lo = 0 ∧ 0 ≤ hi)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi) :
    saturating signed lo hi op a b = clamp lo hi (exact op a b) := by
  have hiff := fun hover => upward_iff_above signed lo hi op a b hsigned hunsigned ha hb hover
  unfold saturating clamp
  by_cases hlow : exact op a b < lo
  · have hover : exact op a b < lo ∨ hi < exact op a b := Or.inl hlow
    have hup : upward signed op a b = false := by
      cases h : upward signed op a b
      · rfl
      · have := (hiff hover).mp h
        omega
    simp [overflow, hlow, hup]
  · by_cases hhigh : hi < exact op a b
    · have hover : exact op a b < lo ∨ hi < exact op a b := Or.inr hhigh
      have hup : upward signed op a b = true := (hiff hover).mpr hhigh
      simp [overflow, hlow, hhigh, hup]
    · simp [overflow, hlow, hhigh]

/-! ## Shifts (10-syntax.md §3b)

```c
static inline T oak_shl_T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v << n); }
static inline T oak_shr_T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v >> n); }
```

A count reaching the operand width traps; below it, C promotes the
operand, shifts, and the `(T)` cast reduces mod `2^W`, which is the
fixed-width shift. The promotion is modeled as the widest carrier. -/

def shlGuard (width : Nat) (n : Nat) : Bool := !decide (n ≥ width)

theorem shl_guard_iff (width n : Nat) : shlGuard width n = true ↔ n < width := by
  unfold shlGuard; simp <;> omega

def shl8 (v n : UInt8) : UInt8 := (v.toUInt64 <<< n.toUInt64).toUInt8
def shr8 (v n : UInt8) : UInt8 := (v.toUInt64 >>> n.toUInt64).toUInt8
def shl16 (v n : UInt16) : UInt16 := (v.toUInt64 <<< n.toUInt64).toUInt16
def shr16 (v n : UInt16) : UInt16 := (v.toUInt64 >>> n.toUInt64).toUInt16
def shl32 (v n : UInt32) : UInt32 := (v.toUInt64 <<< n.toUInt64).toUInt32
def shr32 (v n : UInt32) : UInt32 := (v.toUInt64 >>> n.toUInt64).toUInt32

theorem shl8_eq (v n : UInt8) (h : n < 8) : shl8 v n = v <<< n := by
  unfold shl8; bv_decide
theorem shr8_eq (v n : UInt8) (h : n < 8) : shr8 v n = v >>> n := by
  unfold shr8; bv_decide
theorem shl16_eq (v n : UInt16) (h : n < 16) : shl16 v n = v <<< n := by
  unfold shl16; bv_decide
theorem shr16_eq (v n : UInt16) (h : n < 16) : shr16 v n = v >>> n := by
  unfold shr16; bv_decide
theorem shl32_eq (v n : UInt32) (h : n < 32) : shl32 v n = v <<< n := by
  unfold shl32; bv_decide
theorem shr32_eq (v n : UInt32) (h : n < 32) : shr32 v n = v >>> n := by
  unfold shr32; bv_decide

end Oak.CheckedArithmeticRefinement
