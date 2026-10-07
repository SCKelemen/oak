import Oak.Stdlib.TimeMagnitudeLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

/-- The single leading sign chosen by format_iso_period. -/
def period_negative (p : Period) : Bool :=
  decide (p.months < 0) || decide (p.days < 0) || decide (p.time.nanos < 0)

def period_positive (p : Period) : Bool :=
  decide (p.months > 0) || decide (p.days > 0) || decide (p.time.nanos > 0)

/-- Exactly the sign condition required by the period formatter. -/
def period_sign_coherent (p : Period) : Prop :=
  ¬((period_negative p && period_positive p) = true)

theorem magnitude_time_with_sign (n : Int64) (negative : Bool) (fuel : Nat)
    (hn : negative = true → n ≤ 0) (hp : negative = false → 0 ≤ n) :
    ∃ m, magnitude_i64 n fuel = some m ∧
      m ≤ (if negative then 9223372036854775808 else 9223372036854775807) ∧
      signed_time_component negative m = n := by
  refine ⟨if n < 0 then 0-n.toUInt64 else n.toUInt64, by simp [magnitude_i64], ?_⟩
  unfold signed_time_component
  bv_decide

theorem magnitude_calendar_with_sign (n : Int32) (negative : Bool) (fuel : Nat)
    (hn : negative = true → n ≤ 0) (hp : negative = false → 0 ≤ n) :
    ∃ m, magnitude_i64 n.toInt64 fuel = some m ∧
      m ≤ (if negative then 2147483648 else 2147483647) ∧
      signed_calendar_component negative m = n := by
  refine ⟨if n.toInt64 < 0 then 0-n.toInt64.toUInt64 else n.toInt64.toUInt64,
    by simp [magnitude_i64], ?_⟩
  unfold signed_calendar_component
  bv_decide

/-- For every period accepted by the formatter's sign check, the unsigned
    magnitudes and the parser's sign conversions recover every original field.
    This is a component contract, not yet a serialized-text round-trip theorem. -/
theorem period_components_roundtrip (p : Period) (fuel : Nat) (hc : period_sign_coherent p) :
    ∃ months days nanos,
      magnitude_i64 p.months.toInt64 fuel = some months ∧
      magnitude_i64 p.days.toInt64 fuel = some days ∧
      magnitude_i64 p.time.nanos fuel = some nanos ∧
      months ≤ (if period_negative p then 2147483648 else 2147483647) ∧
      days ≤ (if period_negative p then 2147483648 else 2147483647) ∧
      nanos ≤ (if period_negative p then 9223372036854775808 else 9223372036854775807) ∧
      (⟨signed_calendar_component (period_negative p) months,
        signed_calendar_component (period_negative p) days,
        ⟨signed_time_component (period_negative p) nanos⟩⟩ : Period) = p := by
  have hs : (period_negative p = true → p.months ≤ 0 ∧ p.days ≤ 0 ∧ p.time.nanos ≤ 0) ∧
      (period_negative p = false → 0 ≤ p.months ∧ 0 ≤ p.days ∧ 0 ≤ p.time.nanos) := by
    rcases p with ⟨months, days, ⟨nanos⟩⟩
    unfold period_sign_coherent period_negative period_positive at *
    bv_decide
  obtain ⟨months, hm, hmb, hmr⟩ := magnitude_calendar_with_sign p.months (period_negative p) fuel
    (fun h => (hs.1 h).1) (fun h => (hs.2 h).1)
  obtain ⟨days, hd, hdb, hdr⟩ := magnitude_calendar_with_sign p.days (period_negative p) fuel
    (fun h => (hs.1 h).2.1) (fun h => (hs.2 h).2.1)
  obtain ⟨nanos, hn, hnb, hnr⟩ := magnitude_time_with_sign p.time.nanos (period_negative p) fuel
    (fun h => (hs.1 h).2.2) (fun h => (hs.2 h).2.2)
  refine ⟨months, days, nanos, hm, hd, hn, hmb, hdb, hnb, ?_⟩
  rw [hmr, hdr, hnr]

/-- The component proof's sign precondition is the extracted formatter guard. -/
theorem period_mixed_sign_error (p : Period) (dst : Array UInt8) (fuel : Nat)
    (hc : ¬period_sign_coherent p) :
    format_iso_period dst p fuel = some (.Err .InvalidDuration, dst) := by
  have h : (period_negative p && period_positive p) = true := Classical.not_not.mp hc
  unfold period_negative period_positive at h
  simp only [format_iso_period, h, ite_true, bind, pure, Option.bind_some]

theorem period_format_success_sign_coherent (p : Period) (dst out : Array UInt8) (n : UInt32) (fuel : Nat)
    (hf : format_iso_period dst p fuel = some (.Ok n, out)) : period_sign_coherent p := by
  apply Classical.byContradiction
  intro hc
  rw [period_mixed_sign_error p dst fuel hc] at hf
  cases hf

end Oak.Stdlib.Time
