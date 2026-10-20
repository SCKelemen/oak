import Oak.Stdlib.TimePeriodFractionTrimLaws
import Oak.Stdlib.TimeUnsignedCopyLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

/-- A nonzero nanosecond fraction is serialized after the exact integer part.
The decimal field has one to nine digits, no trailing zero, and its value scaled
back to nanoseconds is unchanged. Every byte outside the result is preserved. -/
theorem put_frac_encoding (dst : Array UInt8) (at_ : UInt32) (whole fraction : UInt64)
    (extra : Nat) (hp : 0 < fraction.toNat) (hf : fraction.toNat < 1000000000)
    (hs : at_.toNat+30 ≤ dst.size) (hc : at_.toNat+30 < 4294967296) :
    ∃ (out digits : Array UInt8) (count width : UInt32),
      put_frac dst at_ whole fraction 9 (21+extra) = some (at_+count+1+width, out) ∧
      0 < count.toNat ∧ count.toNat ≤ 20 ∧ 0 < width.toNat ∧ width.toNat ≤ 9 ∧
      out.size = dst.size ∧
      reverse_decimal_value digits count.toNat 0 = whole.toNat ∧
      reverse_digits_valid digits count.toNat ∧
      (∀ j, j < count.toNat → out.getD (at_.toNat+j) 0 = digits.getD (count.toNat-1-j) 0) ∧
      out.getD (at_.toNat+count.toNat) 0 = 46 ∧
      fixed_decimal_valid out (at_.toNat+count.toNat+1) width.toNat ∧
      fixed_decimal_value out (at_.toNat+count.toNat+1) width.toNat * 10^(9-width.toNat) = fraction.toNat ∧
      out.getD (at_.toNat+count.toNat+width.toNat) 0 ≠ 48 ∧
      (at_+count+1+width).toNat = at_.toNat+count.toNat+1+width.toNat ∧
      (∀ k, k < at_.toNat ∨ at_.toNat+count.toNat+1+width.toNat ≤ k → out[k]? = dst[k]?) := by
  obtain ⟨integer, digits, count, hi, hcp, hcb, hcn, his, hdv, hde, hchars, hframe⟩ :=
    put_u64_encoding dst at_ whole extra (by omega) (by omega)
  obtain ⟨trimmed, width, ht, htp, hwp, hwb, htv, htn, hte⟩ :=
    put_frac_trim_exact (21+extra) fraction 9 hp hf (by change 9 < 21+extra; omega)
  change width.toNat ≤ 9 at hwb
  change fraction.toNat = trimmed.toNat*10^(9-width.toNat) at hte
  have htrim : trimmed.toNat < 1000000000 := by
    have hpow : 10^width.toNat ≤ 10^9 := Nat.pow_le_pow_right (by decide) hwb
    omega
  have hcast : trimmed.toUInt32.toNat = trimmed.toNat := by
    rw [UInt64.toNat_toUInt32]
    exact Nat.mod_eq_of_lt (by omega)
  have hstart : (at_+count+1).toNat = at_.toNat+count.toNat+1 := by
    rw [UInt32.toNat_add, hcn]
    change (at_.toNat+count.toNat+1)%4294967296 = _
    omega
  let dotted := integer.setIfInBounds (at_+count).toNat 46
  obtain ⟨out, ho, hos, hov, hoe, hof⟩ := put_digits_encoding dotted (at_+count+1)
    trimmed.toUInt32 width (21+extra)
    (by simp only [dotted, Array.size_setIfInBounds, his, hstart]; omega)
    (by rw [hstart]; omega) (by omega) (by rw [hcast]; exact htv)
  rw [hstart] at hov hoe hof
  rw [hcast] at hoe
  have hget (k : Nat) (hk : k < at_.toNat+count.toNat+1 ∨ at_.toNat+count.toNat+1+width.toNat ≤ k) :
      out[k]? = dotted[k]? := hof k hk
  refine ⟨out, digits, count, width, ?_, hcp, hcb, hwp, hwb,
    by simpa [dotted, his] using hos, hde, hdv, ?_, ?_, hov, by rw [hoe]; exact hte.symm, ?_, ?_, ?_⟩
  · unfold put_frac
    simp only [bind, pure]
    rw [hi, Option.bind_some]
    rw [if_neg (by simp only [beq_iff_eq]; intro hz; subst fraction; contradiction)]
    rw [ht, Option.bind_some, ho, Option.bind_some]
    rfl
  · intro j hj
    rw [Array.getD_eq_getD_getElem?, hget _ (Or.inl (by omega))]
    dsimp [dotted]
    rw [Array.getElem?_setIfInBounds_ne (by rw [hcn]; omega)]
    simpa only [Array.getD_eq_getD_getElem?] using hchars j hj
  · rw [Array.getD_eq_getD_getElem?, hget _ (Or.inl (by omega))]
    dsimp [dotted]
    rw [hcn, Array.getElem?_setIfInBounds_self_of_lt (by omega)]
    rfl
  · intro hz
    have hwidth : width.toNat = (width.toNat-1)+1 := by omega
    have hlast : at_.toNat+count.toNat+1+(width.toNat-1) = at_.toNat+count.toNat+width.toNat := by omega
    rw [hwidth, fixed_decimal_value, hlast, hz] at hoe
    have hmod : trimmed.toNat%10 = 0 := by simp only [UInt8.sub_self, UInt8.toNat_zero, Nat.add_zero] at hoe; omega
    apply htn
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod]
    exact hmod
  · rw [UInt32.toNat_add, hstart]
    exact Nat.mod_eq_of_lt (by change at_.toNat+count.toNat+1+width.toNat < 4294967296; omega)
  · intro k hk
    rw [hget k (by omega)]
    dsimp [dotted]
    rw [Array.getElem?_setIfInBounds_ne (by rw [hcn]; omega), hframe k (by omega)]
end Oak.Stdlib.Time
