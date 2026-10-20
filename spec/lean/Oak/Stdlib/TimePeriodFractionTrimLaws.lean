import Oak.Stdlib.TimeFixedWriterLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

/-- Removing decimal trailing zeroes preserves a positive fraction's scaled
value and cannot exhaust its field width. -/
theorem put_frac_trim_exact (fuel : Nat) :
    ∀ (value : UInt64) (places : UInt32),
      0 < value.toNat → value.toNat < 10^places.toNat → places.toNat < fuel →
      ∃ trimmed width, put_frac.loop1 value places fuel = some (trimmed, width) ∧
        0 < trimmed.toNat ∧ 0 < width.toNat ∧ width.toNat ≤ places.toNat ∧
        trimmed.toNat < 10^width.toNat ∧ trimmed%10 ≠ 0 ∧
        value.toNat = trimmed.toNat*10^(places.toNat-width.toNat) := by
  induction fuel with
  | zero => intro value places hp hv hf; omega
  | succ fuel ih =>
    intro value places hp hv hf
    by_cases hz : value%10 = 0
    · have hr : value.toNat%10 = 0 := by
        have := congrArg UInt64.toNat hz
        simpa only [UInt64.toNat_mod, UInt64.toNat_ofNat] using this
      have hplaces : 0 < places.toNat := by
        by_cases he : places.toNat = 0
        · rw [he] at hv; simp at hv; omega
        · omega
      have hsub : (places-1).toNat = places.toNat-1 := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by change 1 ≤ places.toNat; omega))]
        rfl
      have hwidth : places.toNat = (places-1).toNat+1 := by omega
      have hdiv : (value/10).toNat = value.toNat/10 := by rw [UInt64.toNat_div]; rfl
      have hpos : 0 < (value/10).toNat := by
        rw [hdiv]
        have := Nat.mod_add_div value.toNat 10
        omega
      have hbound : (value/10).toNat < 10^(places-1).toNat := by
        rw [hdiv]
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        rw [hwidth, Nat.pow_succ] at hv
        exact hv
      obtain ⟨trimmed, width, ho, ht, hw, hle, hb, hn, he⟩ :=
        ih (value/10) (places-1) hpos hbound (by omega)
      refine ⟨trimmed, width, ?_, ht, hw, by omega, hb, hn, ?_⟩
      · unfold put_frac.loop1
        rw [if_pos (by simp only [beq_iff_eq]; exact hz)]
        exact ho
      · have hexp : places.toNat-width.toNat = ((places-1).toNat-width.toNat)+1 := by omega
        rw [hexp, Nat.pow_succ, ← Nat.mul_assoc, ← he, hdiv]
        have := Nat.mod_add_div value.toNat 10
        omega
    · have hw : 0 < places.toNat := by
        by_cases he : places.toNat = 0
        · rw [he] at hv; simp at hv; omega
        · omega
      refine ⟨value, places, ?_, hp, hw, Nat.le_refl _, hv, hz, by simp⟩
      unfold put_frac.loop1
      rw [if_neg (by simpa only [beq_iff_eq] using hz)]
      rfl
end Oak.Stdlib.Time
