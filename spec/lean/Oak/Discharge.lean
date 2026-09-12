import Std.Tactic.BVDecide

/-!
# Static discharge of refinement constructions

`typechecker/discharge.go` emits a refinement's construction `Name(e)`
without its guard when the facts in scope prove the predicate of `e`
(docs/spec/20-types.md section 12). The divisibility shapes are stated
here over the fixed-width bit vectors the emitted code computes with,
and proved by `bv_decide`: every law is about a power-of-two divisor,
because wrapping arithmetic keeps a power-of-two divisor's low bits and no
other's — the rule's scope. `spec/oak/discharge.oak` states the same laws
in Oak and `oak prove` decides them at the bit level.
-/

namespace Oak.Discharge

/-- A shift by at least log2 K leaves a multiple of K. -/
theorem shift_multiple (e : BitVec 32) : (e <<< 12) % 4096 = 0 := by bv_decide

/-- A mask with a multiple of K leaves a multiple of K. -/
theorem mask_multiple (a : BitVec 32) : (a &&& 4294963200) % 4096 = 0 := by bv_decide

/-- A product with a multiple of K is a multiple of K, wrapping included. -/
theorem product_multiple (x : BitVec 32) : (x * 4096) % 4096 = 0 := by bv_decide

theorem product_multiple_by_two (x : BitVec 8) : (x * 2) % 2 = 0 := by bv_decide

/-- Sums, differences, and bitwise combinations of multiples are multiples. -/
theorem sum_of_multiples (a b : BitVec 32) (ha : a % 64 = 0) (hb : b % 64 = 0) :
    (a + b) % 64 = 0 := by bv_decide

theorem difference_of_multiples (a b : BitVec 32) (ha : a % 64 = 0) (hb : b % 64 = 0) :
    (a - b) % 64 = 0 := by bv_decide

theorem or_of_multiples (a b : BitVec 32) (ha : a % 64 = 0) (hb : b % 64 = 0) :
    (a ||| b) % 64 = 0 := by bv_decide

theorem xor_of_multiples (a b : BitVec 32) (ha : a % 64 = 0) (hb : b % 64 = 0) :
    (a ^^^ b) % 64 = 0 := by bv_decide

/-- A conversion keeps the low bits, narrowing or widening. -/
theorem narrowing_keeps_multiple (x : BitVec 32) (hx : x % 16 = 0) :
    (x.truncate 8) % 16 = 0 := by bv_decide

theorem widening_keeps_multiple (x : BitVec 8) (hx : x % 16 = 0) :
    (x.zeroExtend 32) % 16 = 0 := by bv_decide

/-- A literal bound composes with an offset. -/
theorem offset_below_bound (i : BitVec 32) (hi : i < 7) : i + 1 < 8 := by bv_decide

/-- **The scope of the rule**: for a divisor that is not a power of two the
    product law fails under wrapping — `x * 3` is not a multiple of 3 for
    every `x` once the product wraps — which is why the discharge admits
    power-of-two divisors only. -/
theorem product_multiple_needs_power_of_two :
    ∃ x : BitVec 8, (x * 3) % 3 ≠ 0 := ⟨86, by decide⟩

end Oak.Discharge
