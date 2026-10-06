import Oak.Stdlib.TimeCalendarExtracted
import Std.Tactic.BVDecide

/-!
# Gregorian conversion over the supported range

The two finite certificates evaluate the *extracted implementation* for every
supported epoch day and every year/month/day slot (including invalid dates).
They use `native_decide`: their trust boundary includes Lean's native evaluator
(native decision axioms), not just the kernel. The lifting arguments use the field bounds
below, whose bit-vector certificates also use Lean's native LRAT checker. No assertion here is a proof of compiler refinement.
-/
namespace Oak.Stdlib.Time

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private def indexedDay (n : Nat) : Int64 := Int64.ofInt ((n : Int) - 719528)
private def indexedDate (n : Nat) : Date :=
  ⟨Int32.ofNat (n / 372), UInt8.ofNat (n / 31 % 12 + 1), UInt8.ofNat (n % 31 + 1)⟩

private def dayCheck (n : Nat) : Bool :=
  let days := indexedDay n
  match date_from_epoch_days days 0 with
  | some (.Ok d) => decide (date_valid d 0 = some true ∧ date_epoch_days d 0 = some (.Ok days))
  | _ => false

private def dateCheck (n : Nat) : Bool :=
  let d := indexedDate n
  if date_valid d 0 = some true then
    match date_epoch_days d 0 with
    | some (.Ok days) => decide (-719528 ≤ days ∧ days ≤ 2932896 ∧
        date_from_epoch_days days 0 = some (.Ok d))
    | _ => false
  else true

-- All 3,652,425 supported days; this is not a sample.
private theorem all_days : (List.range 3652425).all dayCheck = true := by native_decide
-- All 3,720,000 year/month/day slots; invalid dates are excluded by date_valid.
private theorem all_dates : (List.range 3720000).all dateCheck = true := by native_decide

private theorem from_fuel (days : Int64) (fuel : Nat) :
    date_from_epoch_days days fuel = date_from_epoch_days days 0 := rfl
private theorem epoch_fuel (d : Date) (fuel : Nat) :
    date_epoch_days d fuel = date_epoch_days d 0 := rfl
private theorem valid_fuel (d : Date) (fuel : Nat) :
    date_valid d fuel = date_valid d 0 := rfl

/-- Every supported epoch day converts to a valid date and back to itself. -/
theorem epoch_date_roundtrip (days : Int64) (fuel : Nat)
    (lo : -719528 ≤ days) (hi : days ≤ 2932896) :
    ∃ d, date_from_epoch_days days fuel = some (.Ok d) ∧
      date_valid d fuel = some true ∧ date_epoch_days d fuel = some (.Ok days) := by
  have lo' : -719528 ≤ days.toInt := by simpa using (Int64.le_iff_toInt_le.mp lo)
  have hi' : days.toInt ≤ 2932896 := by simpa using (Int64.le_iff_toInt_le.mp hi)
  let n := (days.toInt + 719528).toNat
  have hn : n < 3652425 := by dsimp [n]; omega
  have he : indexedDay n = days := by
    unfold indexedDay
    have h : (n : Int) - 719528 = days.toInt := by dsimp [n]; omega
    rw [h, Int64.ofInt_toInt]
  have hc := List.all_eq_true.mp all_days n (List.mem_range.mpr hn)
  simp only [dayCheck, he] at hc
  simp only [from_fuel, valid_fuel, epoch_fuel]
  cases h : date_from_epoch_days days 0 with
  | none => simp [h] at hc
  | some r => cases r with
    | Err e => simp [h] at hc
    | Ok d => exact ⟨d, rfl, by simpa [h] using hc⟩

/-- The validity predicate bounds every field, including the day before narrowing. -/
theorem valid_date_fields (d : Date) (fuel : Nat)
    (h : date_valid d fuel = some true) :
    0 ≤ d.year ∧ d.year ≤ 9999 ∧ 1 ≤ d.month ∧ d.month ≤ 12 ∧
      1 ≤ d.day ∧ d.day ≤ 31 := by
  simp [date_valid, days_in_month, is_leap_year] at h
  split at h <;> simp_all <;> bv_decide

/-- Every valid date converts within the supported day range and back to itself. -/
theorem date_epoch_roundtrip (d : Date) (fuel : Nat)
    (h : date_valid d fuel = some true) :
    ∃ days, date_epoch_days d fuel = some (.Ok days) ∧
      -719528 ≤ days ∧ days ≤ 2932896 ∧
      date_from_epoch_days days fuel = some (.Ok d) := by
  obtain ⟨hy0, hy, hm0, hm, hd0, hd⟩ := valid_date_fields d fuel h
  have hy0' := Int32.le_iff_toInt_le.mp hy0
  have hy' := Int32.le_iff_toInt_le.mp hy
  have hm0' := UInt8.le_iff_toNat_le.mp hm0
  have hm' := UInt8.le_iff_toNat_le.mp hm
  have hd0' := UInt8.le_iff_toNat_le.mp hd0
  have hd' := UInt8.le_iff_toNat_le.mp hd
  change 0 ≤ d.year.toInt at hy0'
  change d.year.toInt ≤ 9999 at hy'
  change 1 ≤ d.month.toNat at hm0'
  change d.month.toNat ≤ 12 at hm'
  change 1 ≤ d.day.toNat at hd0'
  change d.day.toNat ≤ 31 at hd'
  let n := d.year.toInt.toNat * 372 + (d.month.toNat - 1) * 31 + (d.day.toNat - 1)
  have hn : n < 3720000 := by dsimp [n]; omega
  have hyN : n / 372 = d.year.toInt.toNat := by dsimp [n]; omega
  have hmN : n / 31 % 12 + 1 = d.month.toNat := by dsimp [n]; omega
  have hdN : n % 31 + 1 = d.day.toNat := by dsimp [n]; omega
  have he : indexedDate n = d := by
    unfold indexedDate
    rw [hyN, hmN, hdN]
    have hyear : Int32.ofNat d.year.toInt.toNat = d.year := by
      have hnonneg : 0 ≤ d.year.toInt := by simpa using hy0'
      change Int32.ofInt (↑d.year.toInt.toNat) = d.year
      rw [Int.toNat_of_nonneg hnonneg, Int32.ofInt_toInt]
    simp only [hyear, UInt8.ofNat_toNat]
  have hc := List.all_eq_true.mp all_dates n (List.mem_range.mpr hn)
  rw [valid_fuel] at h
  simp only [dateCheck, he, h, ↓reduceIte] at hc
  simp only [epoch_fuel, from_fuel]
  cases hepoch : date_epoch_days d 0 with
  | none => simp [hepoch] at hc
  | some r => cases r with
    | Err e => simp [hepoch] at hc
    | Ok days => exact ⟨days, rfl, by simpa [hepoch] using hc⟩

end Oak.Stdlib.Time
