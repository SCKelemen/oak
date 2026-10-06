import Oak.LRATBoundsExtracted

/-!
The production LRAT word checker's subtraction guard, extracted from
`prove/solver/lrat.oak`. The drift test is `TestLRATKernelBoundsExtract`.
Acceptance means the mathematical endpoint lies within the supplied limit;
therefore the subsequent UInt32 addition cannot wrap. These are proofs of
the extracted guards and the allocation arithmetic, not a proof of the whole
parser, RUP loop, extraction, compiler, allocator, or ARM64/RV64 binary.
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

/-- Reserving one element and four bytes per element fits a UInt32 exactly
when the production allocation guard succeeds. -/
theorem alloc_fits_iff (count : UInt32) (fuel : Nat) :
    lrat_alloc_fits count fuel = some true ↔
      (count.toNat + 1) * 4 < 4294967296 := by
  simp only [lrat_alloc_fits, Option.pure_def, Option.some.injEq,
    decide_eq_true_eq, UInt32.lt_iff_toNat_lt]
  change count.toNat < 1073741823 ↔ _
  omega

/-- The actual expressions used for scratch allocation neither wrap nor
request zero bytes, including when the declared count is zero. -/
theorem allocation_exact (count : UInt32) (fuel : Nat)
    (accepted : lrat_alloc_fits count fuel = some true) :
    (count + 1).toNat = count.toNat + 1 ∧
    ((count + 1) * 4).toNat = (count.toNat + 1) * 4 ∧
    0 < ((count + 1) * 4).toNat := by
  have h := (alloc_fits_iff count fuel).mp accepted
  have he : (count + 1).toNat = count.toNat + 1 := by
    rw [UInt32.toNat_add]
    exact Nat.mod_eq_of_lt (by change count.toNat + 1 < 4294967296; omega)
  have hb : ((count + 1) * 4).toNat = (count.toNat + 1) * 4 := by
    rw [UInt32.toNat_mul, he]
    exact Nat.mod_eq_of_lt h
  exact ⟨he, hb, by rw [hb]; omega⟩

/-- The raw stream header leaves eight words for the header. Both the body
sum and the full buffer's byte size are exact machine arithmetic. -/
theorem stream_allocation_exact (literalWords stepWords : UInt32) (fuel : Nat)
    (accepted : lrat_fits literalWords stepWords 1073741815 fuel = some true) :
    (literalWords + stepWords).toNat = literalWords.toNat + stepWords.toNat ∧
    ((8 + (literalWords + stepWords)) * 4).toNat =
      (8 + literalWords.toNat + stepWords.toNat) * 4 ∧
    0 < ((8 + (literalWords + stepWords)) * 4).toNat := by
  have h := (fits_iff literalWords stepWords 1073741815 fuel).mp accepted
  change literalWords.toNat + stepWords.toNat ≤ 1073741815 at h
  have hs := fits_no_wrap literalWords stepWords 1073741815 fuel accepted
  have ht : (8 + (literalWords + stepWords)).toNat =
      8 + literalWords.toNat + stepWords.toNat := by
    rw [UInt32.toNat_add, hs, Nat.mod_eq_of_lt (by
      change 8 + (literalWords.toNat + stepWords.toNat) < 4294967296; omega)]
    change 8 + (literalWords.toNat + stepWords.toNat) = 8 + literalWords.toNat + stepWords.toNat
    omega
  have hb : ((8 + (literalWords + stepWords)) * 4).toNat =
      (8 + literalWords.toNat + stepWords.toNat) * 4 := by
    rw [UInt32.toNat_mul, ht]
    exact Nat.mod_eq_of_lt (by change (8 + literalWords.toNat + stepWords.toNat) * 4 < 4294967296; omega)
  exact ⟨hs, hb, by rw [hb]; omega⟩

end Oak.LRATBounds
