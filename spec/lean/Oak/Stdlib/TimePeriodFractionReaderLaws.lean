import Oak.Stdlib.TimeFixedDecimalLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

/-- The fractional scanner reads an ASCII field as an exact scaled natural
number. The supplied end may be a buffer boundary or a following nondigit. -/
theorem read_fixed_fraction_complete (src : Array UInt8) (n : UInt32) (count : Nat) :
    ∀ (at_ digits : UInt32) (fraction scale : UInt64) (unit fuel : Nat),
      fixed_decimal_valid src at_.toNat count →
      at_.toNat+count ≤ n.toNat → digits.toNat+count ≤ 9 → count < fuel →
      (0 < count → scale.toNat = 10^(count-1)*unit) →
      fraction.toNat + fixed_decimal_value src at_.toNat count*unit < 18446744073709551616 →
      (at_.toNat+count = n.toNat ∨ is_digit (src.getD (at_.toNat+count) 0) 0 = some false) →
      ∃ finalScale, parse_iso_components.loop3 src n at_ fraction digits scale fuel =
        some (UInt32.ofNat (at_.toNat+count),
          UInt64.ofNat (fraction.toNat+fixed_decimal_value src at_.toNat count*unit),
          UInt32.ofNat (digits.toNat+count), finalScale) := by
  induction count with
  | zero =>
    intro at_ digits fraction scale unit fuel hv hn hd hf hs hb he
    cases fuel with
    | zero => omega
    | succ fuel =>
      refine ⟨scale, ?_⟩
      rcases he with he | he
      · have han : at_ = n := UInt32.toNat_inj.mp (by simpa using he)
        subst at_
        simp [parse_iso_components.loop3, is_digit, fixed_decimal_value]
      · have hstop : is_digit (src.getD at_.toNat 0) fuel = some false := by
          simpa only [Nat.add_zero, is_digit] using he
        unfold parse_iso_components.loop3
        simp only [bind, pure]
        rw [hstop]
        simp only [Option.bind_some, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
          fixed_decimal_value, Nat.zero_mul, Nat.add_zero, UInt32.ofNat_toNat, UInt64.ofNat_toNat]
  | succ count ih =>
    intro at_ digits fraction scale unit fuel hv hn hd hf hs hb he
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hlt : at_ < n := UInt32.lt_iff_toNat_lt.mpr (by omega)
      have hdlt : digits < 9 := UInt32.lt_iff_toNat_lt.mpr (by change digits.toNat < 9; omega)
      have hc := hv 0 (by omega)
      simp only [Nat.add_zero] at hc
      have hdigit : is_digit (src.getD at_.toNat 0) fuel = some true := by
        simp only [is_digit, hc.1, hc.2, decide_true, Bool.true_and, pure]
      let digit := (src.getD at_.toNat 0-48).toUInt64
      have hdn : digit.toNat = (src.getD at_.toNat 0-48).toNat := UInt8.toNat_toUInt64 _
      have hscale : scale.toNat = 10^count*unit := by simpa using hs (by omega)
      have hnext : (at_+1).toNat = at_.toNat+1 := by
        have := n.toNat_lt
        rw [UInt32.toNat_add]
        change (at_.toNat+1)%4294967296 = at_.toNat+1
        omega
      have hdnext : (digits+1).toNat = digits.toNat+1 := by
        rw [UInt32.toNat_add]
        change (digits.toNat+1)%4294967296 = digits.toNat+1
        omega
      have htotal : fraction.toNat+fixed_decimal_value src at_.toNat (count+1)*unit =
          fraction.toNat+digit.toNat*scale.toNat+fixed_decimal_value src (at_+1).toNat count*unit := by
        rw [fixed_decimal_cons, Nat.add_mul, hdn, hscale, hnext, Nat.mul_assoc, Nat.add_assoc]
      have hfit : fraction.toNat+digit.toNat*scale.toNat < 18446744073709551616 := by rw [htotal] at hb; omega
      have hex : (fraction+digit*scale).toNat = fraction.toNat+digit.toNat*scale.toNat := by
        have hm : digit.toNat*scale.toNat < 18446744073709551616 := by omega
        simp only [UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hfit]
      have hmodel : (fraction+digit*scale).toNat+fixed_decimal_value src (at_+1).toNat count*unit =
          fraction.toNat+fixed_decimal_value src at_.toNat (count+1)*unit := by rw [hex, htotal]
      have hend : (at_+1).toNat+count = at_.toNat+(count+1) := by rw [hnext]; omega
      obtain ⟨finalScale, hi⟩ := ih (at_+1) (digits+1) (fraction+digit*scale) (scale/10) unit fuel
        (by intro j hj; have h := hv (j+1) (by omega); simpa only [hnext, Nat.add_assoc, Nat.add_comm 1 j] using h)
        (by rw [hend]; exact hn) (by rw [hdnext]; omega) (by omega)
        (by
          intro hp
          rw [UInt64.toNat_div, hscale]
          change 10^count*unit/10 = 10^(count-1)*unit
          have hcount : count = (count-1)+1 := by omega
          rw [hcount, Nat.pow_succ]
          have hm : 10^(count-1)*10*unit = (10^(count-1)*unit)*10 := by simp only [Nat.mul_assoc, Nat.mul_comm 10 unit]
          rw [hm, Nat.mul_div_cancel _ (by decide)]
          simp)
        (by rw [hmodel]; exact hb) (by rw [hend]; exact he)
      refine ⟨finalScale, ?_⟩
      unfold parse_iso_components.loop3
      simp only [bind, pure]
      rw [hdigit, Option.bind_some]
      rw [if_pos (by simp only [hlt, hdlt, decide_true, Bool.true_and])]
      rw [hi, hmodel, hend, hdnext]
      simp only [Nat.add_assoc, Nat.add_comm 1 count]
end Oak.Stdlib.Time
