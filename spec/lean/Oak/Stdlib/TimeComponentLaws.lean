import Oak.Stdlib.TimeCalendarExtracted
import Lean.Elab.Tactic.Omega

/-! # Exact overflow guards for ISO period and duration components
The division guards are related to unbounded natural arithmetic, without
bit-vector certificates. These are local arithmetic contracts: the parser's
loop invariants and grammar remain separate obligations.
-/
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

private theorem component_fits (current value factor fraction limit : Nat)
    (hc : current ≤ limit) (hf : 0 < factor) :
    (fraction ≤ limit-current ∧ value ≤ (limit-current-fraction)/factor) ↔
      current + value*factor + fraction ≤ limit := by
  rw [Nat.le_div_iff_mul_le hf]
  omega

/-- The unsigned component expression cannot wrap when its mathematical sum fits. -/
theorem component_sum_exact (current value factor fraction limit : UInt64)
    (hfit : current.toNat + value.toNat*factor.toNat + fraction.toNat ≤ limit.toNat) :
    (current + value*factor + fraction).toNat =
      current.toNat + value.toNat*factor.toNat + fraction.toNat := by
  have hb := UInt64.toNat_lt limit
  have hm : value.toNat*factor.toNat < 18446744073709551616 := by omega
  have ha : current.toNat+value.toNat*factor.toNat < 18446744073709551616 := by omega
  have ht : current.toNat+value.toNat*factor.toNat+fraction.toNat < 18446744073709551616 := by omega
  simp only [UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ht]

/-- The parser's component guard rejects exactly the mathematical sums above
    the selected limit, assuming its accumulator invariant and a positive unit. -/
theorem iso_component_overflows_exact (current value factor fraction limit : UInt64) (fuel : Nat)
    (hc : current ≤ limit) (hf : 0 < factor) :
    iso_component_overflows current value factor fraction limit fuel =
      some (decide (limit.toNat < current.toNat + value.toNat*factor.toNat + fraction.toNat)) := by
  have hcn := UInt64.le_iff_toNat_le.mp hc
  have hfn : 0 < factor.toNat := by simpa using UInt64.lt_iff_toNat_lt.mp hf
  have hd := UInt64.toNat_sub_of_le limit current hc
  by_cases ho : fraction > limit-current
  · have hon := UInt64.lt_iff_toNat_lt.mp ho
    rw [hd] at hon
    have hsum : limit.toNat < current.toNat+value.toNat*factor.toNat+fraction.toNat := by omega
    simp [iso_component_overflows, ho, hsum]
  · have hr : fraction ≤ limit-current := UInt64.not_lt.mp ho
    have hrn := UInt64.le_iff_toNat_le.mp hr
    rw [hd] at hrn
    have hd2 := UInt64.toNat_sub_of_le (limit-current) fraction hr
    rw [hd] at hd2
    have hfit := component_fits current.toNat value.toNat factor.toNat fraction.toNat limit.toNat hcn hfn
    have hg : (value > (limit-current-fraction)/factor) ↔
        limit.toNat < current.toNat+value.toNat*factor.toNat+fraction.toNat := by
      change (limit-current-fraction)/factor < value ↔ _
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div, hd2]
      omega
    simp [iso_component_overflows, ho, hg]

/-- Accepted component arithmetic has the exact unbounded value and remains
    below its selected signed-magnitude limit. -/
theorem iso_component_accept_exact (current value factor fraction limit : UInt64) (fuel : Nat)
    (hc : current ≤ limit) (hf : 0 < factor)
    (ha : iso_component_overflows current value factor fraction limit fuel = some false) :
    (current+value*factor+fraction).toNat = current.toNat+value.toNat*factor.toNat+fraction.toNat ∧
      current+value*factor+fraction ≤ limit := by
  rw [iso_component_overflows_exact current value factor fraction limit fuel hc hf] at ha
  have hfit : current.toNat+value.toNat*factor.toNat+fraction.toNat ≤ limit.toNat := by simpa using ha
  have he := component_sum_exact current value factor fraction limit hfit
  exact ⟨he, UInt64.le_iff_toNat_le.mpr (by rw [he]; exact hfit)⟩

/-- Decimal accumulation rejects exactly the values beyond UInt64's maximum. -/
theorem iso_decimal_overflows_exact (value digit : UInt64) (fuel : Nat) :
    iso_decimal_overflows value digit fuel =
      some (decide (18446744073709551615 < value.toNat*10+digit.toNat)) := by
  have hd : digit ≤ 18446744073709551615 := by
    have hb := UInt64.toNat_lt digit
    rw [UInt64.le_iff_toNat_le]
    simpa using (show digit.toNat ≤ 18446744073709551615 by omega)
  have he := UInt64.toNat_sub_of_le 18446744073709551615 digit hd
  have hdiv := Nat.le_div_iff_mul_le (x := value.toNat) (y := 18446744073709551615-digit.toNat) (by decide : 0 < 10)
  have hg : (value > (18446744073709551615-digit)/10) ↔
      18446744073709551615 < value.toNat*10+digit.toNat := by
    change (18446744073709551615-digit)/10 < value ↔ _
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div, he]
    simp [UInt64.toNat_ofNat] at *
    have hbd := UInt64.toNat_lt digit
    omega
  simp [iso_decimal_overflows, hg]

/-- A non-overflowing decimal step is the exact base-ten extension. -/
theorem iso_decimal_accept_exact (value digit : UInt64) (fuel : Nat)
    (ha : iso_decimal_overflows value digit fuel = some false) :
    (value*10+digit).toNat = value.toNat*10+digit.toNat := by
  rw [iso_decimal_overflows_exact] at ha
  have hf : value.toNat*10+digit.toNat ≤ 18446744073709551615 := by simpa using ha
  have he := component_sum_exact 0 value 10 digit 18446744073709551615 (by simpa using hf)
  simpa using he

/-- Every mathematical sum within the limit is accepted. -/
theorem iso_component_accept_of_fit (current value factor fraction limit : UInt64) (fuel : Nat)
    (hf : 0 < factor)
    (hfit : current.toNat+value.toNat*factor.toNat+fraction.toNat ≤ limit.toNat) :
    iso_component_overflows current value factor fraction limit fuel = some false := by
  have hc : current ≤ limit := UInt64.le_iff_toNat_le.mpr (by omega)
  rw [iso_component_overflows_exact current value factor fraction limit fuel hc hf]
  simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt]
  exact hfit

end Oak.Stdlib.Time
