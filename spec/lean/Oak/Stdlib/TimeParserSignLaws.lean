import Oak.Stdlib.TimeParserResultLaws
import Oak.Stdlib.TimePeriodSignLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

/-- Bounded magnitudes converted under one sign cannot become mixed-sign fields.
    This machine-conversion fact uses the pinned native LRAT checker. -/
theorem bounded_period_sign_coherent (negative : Bool) (months days nanos : UInt64)
    (hm : months ≤ (if negative then 2147483648 else 2147483647))
    (hd : days ≤ (if negative then 2147483648 else 2147483647))
    (hn : nanos ≤ (if negative then 9223372036854775808 else 9223372036854775807)) :
    period_sign_coherent
      { months := (if negative then 0-months else months).toUInt32.toInt32,
        days := (if negative then 0-days else days).toUInt32.toInt32,
        time := { nanos := (if negative then 0-nanos else nanos).toInt64 } } := by
  unfold period_sign_coherent period_negative period_positive
  bv_decide

/-- Every successful shared component parse satisfies the formatter's sign
precondition, for both period and fixed-duration modes. -/
theorem parse_iso_components_sign_coherent (src : Array UInt8) (fixed : Bool) (fuel : Nat)
    (p : Period) (h : parse_iso_components src fixed fuel = some (.Ok p)) :
    period_sign_coherent p := by
  obtain ⟨negative, months, days, nanos, hm, hd, hn, rfl⟩ :=
    parse_iso_components_bounded_result src fixed fuel p h
  exact bounded_period_sign_coherent negative months days nanos hm hd hn

/-- The public period parser produces only sign-coherent periods. This is a
success law; it does not claim grammar completeness or a text round trip. -/
theorem parse_iso_period_sign_coherent (src : Array UInt8) (fuel : Nat)
    (p : Period) (h : parse_iso_period src fuel = some (.Ok p)) : period_sign_coherent p := by
  apply parse_iso_components_sign_coherent src false fuel p
  simpa only [parse_iso_period, bind, pure, Option.bind_fun_some] using h

end Oak.Stdlib.Time
