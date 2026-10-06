import Oak.Stdlib.TimeGregorianLaws

/-! # Checked day addition and month-end policies

The integer guard and structural policy arguments are kernel checked. The
bounded bit-vector certificates use Lean's native LRAT checker, which adds
native decision axioms in the pinned toolchain. Success and identity theorems
using Gregorian conversion inherit its native-evaluation trust as well.
-/
namespace Oak.Stdlib.Time

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

/-- The pre-addition guard is exactly the unbounded integer range check, even
    when `delta` is either i64 extremum. -/
theorem day_guard_exact (base delta : Int64)
    (lo : -719528 ≤ base) (hi : base ≤ 2932896) :
    (delta < -719528 - base ∨ delta > 2932896 - base) ↔
    (base.toInt + delta.toInt < -719528 ∨ base.toInt + delta.toInt > 2932896) := by
  simp only [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt, Int64.toInt_sub] at *
  simp at *
  have hl : (-719528 - base.toInt).bmod 18446744073709551616 = -719528 - base.toInt :=
    Int.bmod_eq_of_le (by omega) (by omega)
  have hh : (2932896 - base.toInt).bmod 18446744073709551616 = 2932896 - base.toInt :=
    Int.bmod_eq_of_le (by omega) (by omega)
  simp only [hl, hh]
  omega

/-- Accepted addition cannot wrap. -/
theorem checked_day_sum (base delta : Int64)
    (lo : -719528 ≤ base) (hi : base ≤ 2932896)
    (dl : -719528 - base ≤ delta) (dh : delta ≤ 2932896 - base) :
    (base + delta).toInt = base.toInt + delta.toInt := by
  simp only [Int64.le_iff_toInt_le, Int64.toInt_sub, Int64.toInt_add] at *
  simp at *
  have hl : (-719528 - base.toInt).bmod 18446744073709551616 = -719528 - base.toInt :=
    Int.bmod_eq_of_le (by omega) (by omega)
  have hh : (2932896 - base.toInt).bmod 18446744073709551616 = 2932896 - base.toInt :=
    Int.bmod_eq_of_le (by omega) (by omega)
  simp only [hl, hh] at *
  exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem checked_day_range (base delta : Int64)
    (lo : -719528 ≤ base) (hi : base ≤ 2932896)
    (dl : -719528 - base ≤ delta) (dh : delta ≤ 2932896 - base) :
    -719528 ≤ base + delta ∧ base + delta ≤ 2932896 := by
  bv_decide

private theorem epoch_civil_value (d : Date) (base : Int64) (fuel : Nat)
    (hv : date_valid d fuel = some true)
    (he : date_epoch_days d fuel = some (.Ok base)) :
    days_from_civil d.year d.month d.day fuel = some base := by
  cases hc : days_from_civil d.year d.month d.day fuel with
  | none => simp [date_epoch_days, hv, hc] at he
  | some value =>
    have h : value = base := by simpa [date_epoch_days, hv, hc] using he
    simp [h]

-- Rewrite the monadic plumbing before using the calendar-value equations.
-- Putting those equations directly in a broad simp set makes the simplifier
-- unfold the civil conversion while trying unrelated matches.
private theorem add_days_compute (d : Date) (base delta : Int64) (fuel : Nat)
    (hv : date_valid d fuel = some true)
    (hc : days_from_civil d.year d.month d.day fuel = some base) :
    date_add_days d delta fuel =
      (if (decide (delta < (0 - 719528) - base) || decide (delta > 2932896 - base)) then
        some (.Err .Overflowed) else date_from_epoch_days (base + delta) fuel) := by
  unfold date_add_days
  simp only [bind, pure]
  rw [hv, Option.bind_some]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hc, Option.bind_some]

/-- Day addition has the specified mathematical result and returns a valid date. -/
theorem add_days_success (d : Date) (delta base : Int64) (fuel : Nat)
    (hv : date_valid d fuel = some true)
    (he : date_epoch_days d fuel = some (.Ok base))
    (hl : -719528 - base ≤ delta) (hh : delta ≤ 2932896 - base) :
    ∃ result, date_add_days d delta fuel = some (.Ok result) ∧
      date_valid result fuel = some true ∧
      date_epoch_days result fuel = some (.Ok (base + delta)) ∧
      (base + delta).toInt = base.toInt + delta.toInt := by
  obtain ⟨b, hb, blo, bhi, _⟩ := date_epoch_roundtrip d fuel hv
  have hbase : b = base := by simpa [he, eq_comm] using hb
  subst b
  obtain ⟨slo, shi⟩ := checked_day_range base delta blo bhi hl hh
  obtain ⟨result, hr, hvresult, heresult⟩ := epoch_date_roundtrip (base + delta) fuel slo shi
  have hc := epoch_civil_value d base fuel hv he
  refine ⟨result, ?_, hvresult, heresult, checked_day_sum base delta blo bhi hl hh⟩
  rw [add_days_compute d base delta fuel hv hc]
  simp only [Int64.zero_sub, Int64.not_lt.mpr hl, Int64.not_lt.mpr hh,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false]
  exact hr

/-- The caller gets Overflowed exactly for an out-of-range mathematical sum. -/
theorem add_days_overflow (d : Date) (delta base : Int64) (fuel : Nat)
    (hv : date_valid d fuel = some true)
    (he : date_epoch_days d fuel = some (.Ok base))
    (hout : base.toInt + delta.toInt < -719528 ∨ base.toInt + delta.toInt > 2932896) :
    date_add_days d delta fuel = some (.Err .Overflowed) := by
  obtain ⟨b, hb, blo, bhi, _⟩ := date_epoch_roundtrip d fuel hv
  have hbase : b = base := by simpa [he, eq_comm] using hb
  subst b
  have hc := epoch_civil_value d base fuel hv he
  have hg := (day_guard_exact base delta blo bhi).mpr hout
  rw [add_days_compute d base delta fuel hv hc]
  rcases hg with hg | hg <;> simp [hg]

private theorem zero_day_guard (base : Int64)
    (hl : -719528 ≤ base) (hh : base ≤ 2932896) :
    ¬ (0 : Int64) < -719528 - base ∧ ¬ (0 : Int64) > 2932896 - base := by
  bv_decide

/-- Adding zero days preserves every valid date. -/
theorem add_days_zero (d : Date) (fuel : Nat) (hv : date_valid d fuel = some true) :
    date_add_days d 0 fuel = some (.Ok d) := by
  obtain ⟨base, he, hl, hh, hr⟩ := date_epoch_roundtrip d fuel hv
  have hc := epoch_civil_value d base fuel hv he
  obtain ⟨hlo, hhi⟩ := zero_day_guard base hl hh
  rw [add_days_compute d base 0 fuel hv hc]
  simpa only [Int64.zero_sub, hlo, hhi, decide_false, Bool.false_or,
    Bool.false_eq_true, ite_false, Int64.add_zero] using hr

/-- A checked linear month index decodes to the supported year/month range. -/
theorem month_index_fields (index : Int64) (lo : 0 ≤ index) (hi : index < 120000) :
    0 ≤ (index / 12).toInt32 ∧ (index / 12).toInt32 ≤ 9999 ∧
    1 ≤ ((index % 12 + 1).toUInt64).toUInt8 ∧
    ((index % 12 + 1).toUInt64).toUInt8 ≤ 12 := by
  bv_decide

private theorem month_length_bounds (y : Int32) (m : UInt8) (fuel : Nat)
    (hm : 1 ≤ m) (hm' : m ≤ 12) :
    ∃ last, days_in_month y m fuel = some last ∧ 28 ≤ last ∧ last ≤ 31 := by
  simp [days_in_month, is_leap_year]
  split <;> simp_all <;> split <;> simp_all

def month_index (d : Date) (months : Int32) : Int64 :=
  d.year.toInt64 * 12 + d.month.toUInt64.toInt64 - 1 + months.toInt64
def month_year (index : Int64) : Int32 := (index / 12).toInt32
def month_number (index : Int64) : UInt8 := (index % 12 + 1).toUInt64.toUInt8

/-- Reject preserves the day exactly; a successful result cannot be silently clamped. -/
theorem add_months_reject_preserves_day (d result : Date) (months : Int32) (fuel : Nat)
    (h : date_add_months d months .Reject fuel = some (.Ok result)) :
    result.day = d.day := by
  unfold date_add_months at h
  simp only [bind, pure] at h
  cases hv : date_valid d fuel with
  | none => simp only [hv, Option.bind_none, reduceCtorEq] at h
  | some valid =>
    cases valid <;> simp only [hv, Option.bind_some, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_true, ite_false] at h
    · simp at h
    · split at h
      · simp at h
      · cases hm : days_in_month (month_year (month_index d months)) (month_number (month_index d months)) fuel with
        | none =>
          unfold month_year month_number month_index at hm
          rw [hm, Option.bind_none] at h
          contradiction
        | some last =>
          unfold month_year month_number month_index at hm
          rw [hm, Option.bind_some] at h
          simp only [Bool.and_true, decide_eq_true_eq] at h
          split at h
          · simp at h
          · simp_all
            subst result
            rfl

private theorem clamped_day_bounds (day last : UInt8) (hd : 1 ≤ day) (hl : 28 ≤ last) :
    1 ≤ (if day > last then last else day) ∧ (if day > last then last else day) ≤ last := by
  split <;> simp_all [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] <;> omega

/-- Clamp succeeds for every valid input with an in-range target month. Its
    result uses the lesser of the original day and the target month's last day. -/
theorem add_months_clamp (d : Date) (months : Int32) (fuel : Nat)
    (hv : date_valid d fuel = some true)
    (lo : 0 ≤ month_index d months) (hi : month_index d months < 120000) :
    ∃ result last, date_add_months d months .Clamp fuel = some (.Ok result) ∧
      date_valid result fuel = some true ∧
      result.year = month_year (month_index d months) ∧
      result.month = month_number (month_index d months) ∧
      days_in_month result.year result.month fuel = some last ∧
      result.day = (if d.day > last then last else d.day) := by
  obtain ⟨hy0, hy, hm0, hm⟩ := month_index_fields (month_index d months) lo hi
  obtain ⟨last, hlast, hl, hh⟩ := month_length_bounds
    (month_year (month_index d months)) (month_number (month_index d months)) fuel hm0 hm
  obtain ⟨_, _, _, _, hd, _⟩ := valid_date_fields d fuel hv
  let result : Date := ⟨month_year (month_index d months), month_number (month_index d months),
    if d.day > last then last else d.day⟩
  refine ⟨result, last, ?_, ?_, rfl, rfl, hlast, rfl⟩
  · have hlow := Int64.not_lt.mpr lo
    have hhigh := Int64.not_le.mpr hi
    unfold month_index at hlow hhigh
    unfold month_year month_number month_index at hlast
    simp only [date_add_months, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hlow, hhigh, decide_false, Bool.false_or, hlast, Option.bind_some,
      Bool.not_true, Bool.and_false, bind, pure, decide_eq_true_eq]
    rfl
  · have hday : 1 ≤ result.day ∧ result.day ≤ last := by
      dsimp [result]
      exact clamped_day_bounds d.day last hd hl
    change 0 ≤ month_year (month_index d months) at hy0
    change month_year (month_index d months) ≤ 9999 at hy
    change 1 ≤ month_number (month_index d months) at hm0
    change month_number (month_index d months) ≤ 12 at hm
    simp [date_valid, result, hlast, hy0, hy, hm0, hm, hday.1, hday.2]

/-- Both policies reject an out-of-domain target month before constructing it. -/
theorem add_months_overflow (d : Date) (months : Int32) (policy : MonthEnd) (fuel : Nat)
    (hv : date_valid d fuel = some true)
    (hout : month_index d months < 0 ∨ month_index d months ≥ 120000) :
    date_add_months d months policy fuel = some (.Err .Overflowed) := by
  unfold month_index at hout
  rcases hout with hout | hout <;> simp [date_add_months, hv, hout]

/-- Within the domain, Reject returns InvalidCivil precisely when the original
    day exceeds the target month's last day. Otherwise it returns the same valid
    date as Clamp, with the original day preserved by add_months_reject_preserves_day. -/
theorem add_months_reject (d : Date) (months : Int32) (fuel : Nat)
    (hv : date_valid d fuel = some true)
    (lo : 0 ≤ month_index d months) (hi : month_index d months < 120000) :
    ∃ result last, date_valid result fuel = some true ∧
      result.year = month_year (month_index d months) ∧
      result.month = month_number (month_index d months) ∧
      days_in_month result.year result.month fuel = some last ∧
      date_add_months d months .Reject fuel =
        (if d.day > last then some (.Err .InvalidCivil) else some (.Ok result)) := by
  obtain ⟨result, last, _, hr, hy, hm, hlast, hd⟩ := add_months_clamp d months fuel hv lo hi
  refine ⟨result, last, hr, hy, hm, hlast, ?_⟩
  have hresult : result = ⟨month_year (month_index d months), month_number (month_index d months),
      if d.day > last then last else d.day⟩ := by
    cases result
    simp_all
  rw [hy, hm] at hlast
  have hlow := Int64.not_lt.mpr lo
  have hhigh := Int64.not_le.mpr hi
  unfold month_index at hlow hhigh
  unfold month_year month_number month_index at hlast
  unfold date_add_months
  simp only [bind, pure]
  rw [hv, Option.bind_some]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, hlow, hhigh,
    decide_false, Bool.false_or]
  rw [hlast, Option.bind_some]
  simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
  rw [hresult]
  by_cases hday : d.day > last <;> simp only [hday, ite_true, ite_false] <;> rfl

end Oak.Stdlib.Time
