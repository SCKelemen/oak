import Oak.Stdlib.TimeFixedDecimalLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

private theorem fixed_writer_loop (fuel : Nat) :
    ∀ (dst : Array UInt8) (at_ value width : UInt32),
      at_.toNat+width.toNat ≤ dst.size → at_.toNat+width.toNat < 4294967296 →
      width.toNat < fuel → value.toNat < 10^width.toNat →
      ∃ out, put_digits.loop1 dst at_ value width fuel = some (out, 0, 0) ∧
        out.size = dst.size ∧ fixed_decimal_valid out at_.toNat width.toNat ∧
        fixed_decimal_value out at_.toNat width.toNat = value.toNat ∧
        (∀ k, k < at_.toNat ∨ at_.toNat+width.toNat ≤ k → out[k]? = dst[k]?) := by
  induction fuel with
  | zero => intro dst at_ value width hs hc hf hv; omega
  | succ fuel ih =>
    intro dst at_ value width hs hc hf hv
    by_cases hw : width = 0
    · subst width
      have hz : value = 0 := UInt32.toNat_inj.mp (by simpa using (show value.toNat = 0 by simpa using hv))
      subst value
      exact ⟨dst, by simp [put_digits.loop1], rfl, by simp [fixed_decimal_valid], rfl, by simp⟩
    · have hp : 0 < width.toNat := by have hn : width.toNat ≠ 0 := fun h => hw (UInt32.toNat_inj.mp h); omega
      have hsub : (width-1).toNat = width.toNat-1 := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by change 1 ≤ width.toNat; omega))]
        rfl
      have hpos : (at_+(width-1)).toNat = at_.toNat+(width.toNat-1) := by
        rw [UInt32.toNat_add, hsub]
        exact Nat.mod_eq_of_lt (by omega)
      have hwidth : width.toNat = (width-1).toNat+1 := by omega
      have hdiv : (value/10).toNat < 10^(width-1).toNat := by
        rw [UInt32.toNat_div]
        change value.toNat/10 < 10^(width-1).toNat
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        rw [hwidth, Nat.pow_succ] at hv
        exact hv
      let written := dst.setIfInBounds (at_+(width-1)).toNat (48+(value%10).toUInt8)
      obtain ⟨out, ho, hsize, hvalid, hvalue, hframe⟩ := ih written at_ (value/10) (width-1)
        (by simp only [written, Array.size_setIfInBounds]; omega) (by omega) (by omega) hdiv
      have hlast : out.getD (at_.toNat+(width-1).toNat) 0 = 48+(value%10).toUInt8 := by
        rw [Array.getD_eq_getD_getElem?, hframe _ (Or.inr (by omega))]
        dsimp [written]
        rw [hpos, hsub, Array.getElem?_setIfInBounds_self_of_lt (by omega)]
        rfl
      obtain ⟨hlo, hhi, hdigit⟩ := fixed_decimal_byte_exact value
      refine ⟨out, ?_, by simpa [written] using hsize, ?_, ?_, ?_⟩
      · unfold put_digits.loop1
        rw [if_pos (by simp only [decide_eq_true_eq]; exact UInt32.lt_iff_toNat_lt.mpr hp)]
        exact ho
      · intro j hj
        rw [hwidth] at hj
        by_cases hj' : j < (width-1).toNat
        · exact hvalid j hj'
        · have he : j = (width-1).toNat := by omega
          rw [he, hlast]
          exact ⟨hlo, hhi⟩
      · rw [hwidth, fixed_decimal_value, hvalue, hlast, hdigit, UInt32.toNat_div]
        change value.toNat/10*10+value.toNat%10 = value.toNat
        omega
      · intro k hk
        rw [hframe k (by omega)]
        exact Array.getElem?_setIfInBounds_ne (by rw [hpos]; omega)

/-- Fixed-width serialization emits valid ASCII digits with their exact numeric
value, including leading zeroes, and preserves every byte outside the field. -/
theorem put_digits_encoding (dst : Array UInt8) (at_ value width : UInt32) (fuel : Nat)
    (hs : at_.toNat+width.toNat ≤ dst.size) (hc : at_.toNat+width.toNat < 4294967296)
    (hf : width.toNat < fuel) (hv : value.toNat < 10^width.toNat) :
    ∃ out, put_digits dst at_ value width fuel = some ((), out) ∧
      out.size = dst.size ∧ fixed_decimal_valid out at_.toNat width.toNat ∧
      fixed_decimal_value out at_.toNat width.toNat = value.toNat ∧
      (∀ k, k < at_.toNat ∨ at_.toNat+width.toNat ≤ k → out[k]? = dst[k]?) := by
  obtain ⟨out, ho, hrest⟩ := fixed_writer_loop fuel dst at_ value width hs hc hf hv
  refine ⟨out, ?_, hrest⟩
  unfold put_digits
  simp only [bind, pure, ho, Option.bind_some]
end Oak.Stdlib.Time
