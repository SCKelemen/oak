import Oak.Stdlib.TimeUnsignedCopyLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- The actual scanner reads a bounded decimal sequence exactly and stops at
its supplied end or a nondigit. The model uses unbounded arithmetic. -/
theorem read_reverse_decimal_complete (src digits : Array UInt8) (n : UInt32) (count : Nat) :
    ∀ (at_ : UInt32) (value : UInt64) (fuel : Nat),
      reverse_digits_valid digits count →
      (∀ j, j < count → src.getD (at_.toNat+j) 0 = digits.getD (count-1-j) 0) →
      at_.toNat+count ≤ n.toNat → count < fuel →
      reverse_decimal_value digits count value.toNat ≤ 18446744073709551615 →
      (at_.toNat+count = n.toNat ∨ is_digit (src.getD (at_.toNat+count) 0) 0 = some false) →
      parse_iso_components.loop2 src n at_ false value fuel =
        some (UInt32.ofNat (at_.toNat+count), false,
          UInt64.ofNat (reverse_decimal_value digits count value.toNat)) := by
  induction count with
  | zero =>
    intro at_ value fuel hv hm hn hf hb hs
    cases fuel with
    | zero => omega
    | succ fuel =>
      rcases hs with hs | hs
      · have he : at_ = n := UInt32.toNat_inj.mp (by simpa using hs)
        subst at_
        simp [parse_iso_components.loop2, is_digit, reverse_decimal_value]
      · have hd : is_digit (src.getD at_.toNat 0) fuel = some false := by
          simpa only [Nat.add_zero, is_digit] using hs
        unfold parse_iso_components.loop2
        simp only [bind, pure]
        rw [hd]
        simp only [Option.bind_some, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
          Nat.add_zero, reverse_decimal_value, UInt32.ofNat_toNat, UInt64.ofNat_toNat]
  | succ count ih =>
    intro at_ value fuel hv hm hn hf hb hs
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hlt : at_ < n := UInt32.lt_iff_toNat_lt.mpr (by omega)
      have hchar : src.getD at_.toNat 0 = digits.getD count 0 := by simpa using hm 0 (by omega)
      have hc := hv count (by omega)
      have hd : is_digit (src.getD at_.toNat 0) fuel = some true := by
        rw [hchar]
        simp only [is_digit, hc.1, hc.2, decide_true, Bool.true_and, pure]
      let digit := (src.getD at_.toNat 0 - 48).toUInt64
      have hvdigit : digit.toNat = (digits.getD count 0-48).toNat := by
        simp only [digit, UInt8.toNat_toUInt64, hchar]
      have hstep := reverse_decimal_value_ge digits count (value.toNat*10+digit.toNat)
      have hfit : value.toNat*10+digit.toNat ≤ 18446744073709551615 := by
        simp only [reverse_decimal_value, ← hvdigit] at hb
        omega
      have hg : iso_decimal_overflows value digit fuel = some false := by
        rw [iso_decimal_overflows_exact]
        simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt]
        exact hfit
      have hex := iso_decimal_accept_exact value digit fuel hg
      have hnext : (at_+1).toNat = at_.toNat+1 := by
        have := n.toNat_lt
        rw [UInt32.toNat_add]
        change (at_.toNat+1)%4294967296 = at_.toNat+1
        omega
      have hend : (at_+1).toNat+count = at_.toNat+(count+1) := by rw [hnext]; omega
      have hmodel : reverse_decimal_value digits count (value*10+digit).toNat =
          reverse_decimal_value digits (count+1) value.toNat := by
        rw [hex, hvdigit, reverse_decimal_value]
      have hi := ih (at_+1) (value*10+digit) fuel
        (fun k hk => hv k (by omega))
        (by
          intro j hj
          have h := hm (j+1) (by omega)
          rw [hnext]
          have hp : at_.toNat+1+j = at_.toNat+(j+1) := by omega
          have hk : count+1-1-(j+1) = count-1-j := by omega
          simpa only [hp, hk] using h)
        (by rw [hend]; exact hn) (by omega)
        (by rw [hmodel]; exact hb) (by rw [hend]; exact hs)
      unfold parse_iso_components.loop2
      simp only [bind, pure]
      rw [hd]
      rw [Option.bind_some]
      rw [show (decide (at_ < n) && true && !false) = true by simp [hlt], if_pos rfl]
      rw [hg, Option.bind_some, if_pos (show (!false) = true from rfl), Option.bind_some]
      rw [hi, hend, hmodel]
end Oak.Stdlib.Time
