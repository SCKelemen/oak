import Oak.LRATBoundsExtracted

/-!
The production LRAT word checker's subtraction guard, extracted from
`prove/solver/lrat.oak`. The drift test is `TestLRATKernelBoundsExtract`.
Acceptance means the mathematical endpoint lies within the supplied limit;
therefore the subsequent UInt32 addition cannot wrap. These are proofs of
the extracted guard, not a proof of the whole parser, RUP loop, extraction,
compiler, allocation driver, or ARM64/RV64 binary.
-/

namespace Oak.LRATBounds

theorem fits_iff (at_ count limit : UInt32) (fuel : Nat) :
    lrat_fits at_ count limit fuel = some true ↔
      at_.toNat + count.toNat ≤ limit.toNat := by
  simp only [lrat_fits, Option.pure_def, Option.some.injEq, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · intro ⟨ha, hc⟩
    rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ ha] at hc
    rw [UInt32.le_iff_toNat_le] at ha
    omega
  · intro h
    have ha : at_ ≤ limit := by rw [UInt32.le_iff_toNat_le]; omega
    refine ⟨ha, ?_⟩
    rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ ha]
    omega

theorem fits_no_wrap (at_ count limit : UInt32) (fuel : Nat)
    (accepted : lrat_fits at_ count limit fuel = some true) :
    (at_ + count).toNat = at_.toNat + count.toNat := by
  have bound := (fits_iff at_ count limit fuel).mp accepted
  have := limit.toNat_lt
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem fits_index (at_ count limit index : UInt32) (fuel : Nat)
    (accepted : lrat_fits at_ count limit fuel = some true)
    (inside : index < count) :
    (at_ + index).toNat = at_.toNat + index.toNat ∧ at_ + index < limit := by
  have bound := (fits_iff at_ count limit fuel).mp accepted
  rw [UInt32.lt_iff_toNat_lt] at inside
  have small : at_.toNat + index.toNat < limit.toNat := by omega
  have exactSum : (at_ + index).toNat = at_.toNat + index.toNat := by
    have := limit.toNat_lt
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact ⟨exactSum, by rw [UInt32.lt_iff_toNat_lt, exactSum]; exact small⟩

theorem zero_count (at_ limit : UInt32) (fuel : Nat) :
    lrat_fits at_ 0 limit fuel = some true ↔ at_ ≤ limit := by
  rw [fits_iff, UInt32.le_iff_toNat_le]
  simp

end Oak.LRATBounds
