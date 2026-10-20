import Oak.Stdlib.TimeParserBoundsLaws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
/-- Every successful parse is constructed from magnitudes within the selected
signed limits, including the extra unit of range for negative minima. -/
theorem parse_iso_components_bounded_result (src : Array UInt8) (fixed : Bool) (fuel : Nat)
    (p : Period) (h : parse_iso_components src fixed fuel = some (.Ok p)) :
    ∃ (negative : Bool) (months days nanos : UInt64),
      months ≤ (if negative then 2147483648 else 2147483647) ∧
      days ≤ (if negative then 2147483648 else 2147483647) ∧
      nanos ≤ (if negative then 9223372036854775808 else 9223372036854775807) ∧
      p = { months := (if negative then 0-months else months).toUInt32.toInt32,
            days := (if negative then 0-days else days).toUInt32.toInt32,
            time := { nanos := (if negative then 0-nanos else nanos).toInt64 } } := by
  unfold parse_iso_components at h
  simp only [bind, pure, Option.bind_eq_some_iff] at h
  rcases h with ⟨⟨at_, negative⟩, _, ⟨result, pos⟩, hr, h⟩
  simp only [Option.some.injEq] at h
  subst result
  split at hr
  · simp at hr
  · simp only [Option.bind_eq_some_iff] at hr
    rcases hr with ⟨⟨end_, months, days, nanos, it, ts, any, week, rank, valid, overflow⟩, hl, result, hr, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, _⟩
    have hc : (0 : UInt64) ≤ (if negative then 2147483648 else 2147483647) := by cases negative <;> decide
    have ht : (0 : UInt64) ≤ (if negative then 9223372036854775808 else 9223372036854775807) := by cases negative <;> decide
    have hb := parse_iso_components_loop_bounds src fixed src.size.toUInt32 _ _ fuel
      (at_+1) 0 0 0 false false false false 0 true false _ hc hc ht hl
    split at hr
    · simp at hr
    · split at hr
      · simp at hr
      · simp only [duration_nanos, pure, Option.bind_some, Option.some.injEq,
          Result_Period_TimeError.Ok.injEq] at hr
        exact ⟨negative, months, days, nanos, hb.1, hb.2.1, hb.2.2, hr.symm⟩

/-- The public fixed-duration parser returns the selected signed conversion of
an in-range magnitude, including the negative Int64 minimum. -/
theorem parse_iso_duration_bounded_result (src : Array UInt8) (fuel : Nat)
    (d : Duration) (h : parse_iso_duration src fuel = some (.Ok d)) :
    ∃ (negative : Bool) (nanos : UInt64),
      nanos ≤ (if negative then 9223372036854775808 else 9223372036854775807) ∧
      d.nanos = (if negative then 0-nanos else nanos).toInt64 := by
  simp only [parse_iso_duration, bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨result, hr, h⟩
  cases result with
  | Err e => cases h
  | Ok p =>
    simp only [pure, Option.some.injEq, Result_Duration_TimeError.Ok.injEq] at h
    subst d
    obtain ⟨negative, months, days, nanos, _, _, hn, rfl⟩ :=
      parse_iso_components_bounded_result src true fuel p hr
    exact ⟨negative, nanos, hn, rfl⟩
end Oak.Stdlib.Time
