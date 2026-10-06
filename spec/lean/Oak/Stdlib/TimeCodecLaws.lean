import Oak.Stdlib.TimeCalendarLaws
import Oak.Stdlib.TimeBufferLaws
import Oak.Stdlib.TimeDecimalLaws

/-! # Temporal codec contracts
Universal canonical date round trips through a ten-byte destination, valid
results from successful date/time/local-datetime parsing, and imported storage
contracts for all six formatters. The date parser's ordinal/week branches use
the Gregorian certificates; decimal field bounds use native LRAT certificates.
See 114-temporal.md for the remaining grammar and arithmetic proof obligations.
-/
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Every valid civil date formats to the canonical ten-byte calendar spelling. -/
theorem format_date_canonical (d : Date) (dst : Array UInt8) (fuel : Nat)
    (hv : date_valid d fuel = some true) (hs : dst.size = 10) :
    format_iso_date dst d (fuel + 11) =
      some (.Ok 10, calendar_text d.year.toUInt32 d.month.toUInt32 d.day.toUInt32) := by
  have hv' : date_valid d (fuel + 11) = some true := hv
  unfold format_iso_date
  simp only [bind, pure]
  rw [hv', Option.bind_some]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [write_calendar_text d fuel, Option.bind_some]
  rw [copy_calendar_text dst _ _ _ fuel hs]
  rfl

/-- All valid dates round-trip, including year zero. Eleven units of extraction
    fuel suffice. Decimal identities inherit the native LRAT trust boundary. -/
theorem date_codec_roundtrip (d : Date) (dst : Array UInt8) (fuel : Nat)
    (hv : date_valid d fuel = some true) (hs : dst.size = 10) :
    ∃ text, format_iso_date dst d (fuel + 11) = some (.Ok 10, text) ∧
      parse_iso_date text (fuel + 11) = some (.Ok d) := by
  refine ⟨calendar_text d.year.toUInt32 d.month.toUInt32 d.day.toUInt32,
    format_date_canonical d dst fuel hv hs, ?_⟩
  obtain ⟨hy0, hy, hm0, hm, hd0, hd⟩ := valid_date_fields d fuel hv
  have hy' : d.year.toUInt32 < 10000 := by bv_decide
  have hm' : d.month.toUInt32 < 100 := by bv_decide
  have hd' : d.day.toUInt32 < 100 := by bv_decide
  rw [parse_calendar_text _ _ _ fuel hy' hm' hd']
  simpa using date_create_accept d (fuel + 11) hv

private theorem date_create_valid (y : Int32) (m d : UInt8) (out : Date) (fuel : Nat)
    (h : date_create y m d fuel = some (.Ok out)) :
    date_valid out fuel = some true := by
  unfold date_create at h
  simp only [bind, pure, Option.bind_eq_some_iff] at h
  obtain ⟨ok, hok, h⟩ := h
  cases ok <;> simp_all

private theorem time_of_day_valid (hh mm ss : UInt8) (ns : UInt32) (out : Time) (fuel : Nat)
    (h : time_of_day hh mm ss ns fuel = some (.Ok out)) :
    time_valid out fuel = some true := by
  unfold time_of_day at h
  simp only [bind, pure, Option.bind_eq_some_iff] at h
  obtain ⟨ok, hok, h⟩ := h
  cases ok <;> simp_all

private theorem epoch_result_valid (days : Int64) (out : Date) (fuel : Nat)
    (h : date_from_epoch_days days fuel = some (.Ok out)) :
    date_valid out fuel = some true := by
  by_cases hl : days < -719528
  · rw [epoch_days_reject days fuel (Or.inl hl)] at h
    cases h
  by_cases hh : days > 2932896
  · rw [epoch_days_reject days fuel (Or.inr hh)] at h
    cases h
  obtain ⟨d, hd, hv, _⟩ := epoch_date_roundtrip days fuel
    (Int64.not_lt.mp hl) (Int64.not_lt.mp hh)
  have he : d = out := by simpa [h, eq_comm] using hd
  subst d
  exact hv

private theorem ordinal_result_valid (y : Int32) (n : UInt32) (out : Date) (fuel : Nat)
    (h : date_from_ordinal y n fuel = some (.Ok out)) :
    date_valid out fuel = some true := by
  unfold date_from_ordinal at h
  simp only [bind, pure, Option.bind_eq_some_iff] at h
  obtain ⟨leap, _, h⟩ := h
  cases leap <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h
  all_goals
    split at h
    · cases h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨days, _, h⟩ := h
      exact epoch_result_valid _ _ _ h

private theorem week_result_valid (w : WeekDate) (out : Date) (fuel : Nat)
    (h : date_from_week w fuel = some (.Ok out)) :
    date_valid out fuel = some true := by
  unfold date_from_week at h
  simp only [bind, pure] at h
  split at h
  · cases h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h
    split at h
    · cases h
    · exact epoch_result_valid _ _ _ h

/-- Every successful date parse returns a valid civil date. This includes the
    ordinal/week branches but does not assert grammar completeness. -/
theorem parse_date_valid (src : Array UInt8) (out : Date) (fuel : Nat)
    (h : parse_iso_date src fuel = some (.Ok out)) :
    date_valid out fuel = some true := by
  unfold parse_iso_date at h
  simp only [bind, pure] at h
  grind only [Option.bind_eq_some_iff, date_create_valid, ordinal_result_valid, week_result_valid]

/-- Every successful clock parse returns supported fields and nanoseconds. -/
theorem parse_time_valid (src : Array UInt8) (out : Time) (fuel : Nat)
    (h : parse_iso_time src fuel = some (.Ok out)) :
    time_valid out fuel = some true := by
  unfold parse_iso_time at h
  simp only [bind, pure] at h
  grind only [Option.bind_eq_some_iff, time_of_day_valid]

/-- Successful local datetime parsing composes the two validity contracts. -/
theorem parse_datetime_valid (src : Array UInt8) (out : DateTime) (fuel : Nat)
    (h : parse_iso_datetime src fuel = some (.Ok out)) :
    datetime_valid out fuel = some true := by
  unfold parse_iso_datetime at h
  simp only [bind, pure] at h
  split at h
  · cases h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨d, hd, h⟩ := h
    cases d with
    | Err e => cases h
    | Ok day =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, h⟩ := h
      cases t with
      | Err e => cases h
      | Ok clock =>
        cases h
        simp [datetime_valid, parse_date_valid _ _ _ hd, parse_time_valid _ _ _ ht]

end Oak.Stdlib.Time
