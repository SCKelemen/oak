import Oak.Stdlib.TimeTimestampTextLaws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 100000

/-- Local datetime formatting composes the date and fractional-clock prefixes. -/
theorem datetime_encoding (dt : DateTime) (fuel : Nat)
    (hv : datetime_valid dt fuel = some true) :
    ∃ text : Array UInt8, 19 ≤ text.size ∧ text.size ≤ 29 ∧
      parse_iso_datetime text (fuel+40) = some (.Ok dt) ∧
      ∀ dst, format_iso_datetime dst dt (fuel+40) =
        copy_time_text dst (text ++ Array.replicate (29-text.size) 0) text.size.toUInt32 (fuel+40) := by
  obtain ⟨hd, ht⟩ := datetime_valid_fields dt fuel hv
  obtain ⟨clock, hl, hh, hp, hw⟩ := clock_encoding_shifted dt.time fuel ht
  let cal := calendar_text dt.date.year.toUInt32 dt.date.month.toUInt32 dt.date.day.toUInt32
  let pre := cal ++ #[84]
  have hpre : pre.size = 11 := by simp [pre, cal, calendar_text]
  have hsize : (datetime_text dt.date clock).size = 11+clock.size := by simp [datetime_text, calendar_text]
  refine ⟨datetime_text dt.date clock, by rw [hsize]; omega, by rw [hsize]; omega,
    parse_datetime_text dt.date dt.time clock fuel hd hl hh hp, ?_⟩
  intro dst
  have hvalid : datetime_valid dt (fuel+40) = some true := hv
  have hdate := write_date_with_padding dt.date 19 (Or.inl rfl) fuel
  have htime := hw pre 0 hpre (Or.inl rfl)
  have hjoin : (cal ++ Array.replicate 19 0).setIfInBounds 10 84 = pre ++ Array.replicate 18 0 := by
    simp [cal, pre, calendar_text, Array.replicate_succ]
  unfold format_iso_datetime
  simp only [bind, pure]
  rw [hvalid, Option.bind_some]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hdate, Option.bind_some]
  simp only [Prod.eta, Option.bind_fun_some]
  rw [hjoin, htime]
  simp only [  Option.bind_some,   Nat.add_zero]
  have hsub : 29-(11+clock.size) = 18-clock.size := by omega
  simp only [hsize, hsub]
  rfl

/-- Every valid local datetime round-trips through a sufficiently large destination. -/
theorem datetime_codec_roundtrip (dt : DateTime) (dst : Array UInt8) (fuel : Nat)
    (hv : datetime_valid dt fuel = some true) (hd : 29 ≤ dst.size) (hs : dst.size < 4294967296) :
    ∃ n out, format_iso_datetime dst dt (fuel+40) = some (.Ok n, out) ∧
      19 ≤ n.toNat ∧ n.toNat ≤ 29 ∧ out.size = dst.size ∧
      parse_iso_datetime (out.extract 0 n.toNat) (fuel+40) = some (.Ok dt) ∧
      ∀ k, n.toNat ≤ k → out[k]? = dst[k]? := by
  obtain ⟨text, hl, hh, hp, hw⟩ := datetime_encoding dt fuel hv
  have hlen : text.size.toUInt32.toNat = text.size := UInt32.toNat_ofNat_of_lt' (by change text.size < 4294967296; omega)
  obtain ⟨out, hc, ho, he⟩ := copy_time_text_complete dst
    (text ++ Array.replicate (29-text.size) 0) text.size.toUInt32 (fuel+40)
    (by rw [hlen]; omega) hs (by simp [hlen]) (by rw [hlen]; omega)
  have he' : out.extract 0 text.size.toUInt32.toNat = text := by
    rw [he, hlen]
    simp [Array.extract_append]
  have hf : format_iso_datetime dst dt (fuel+40) = some (.Ok text.size.toUInt32, out) := by
    rw [hw, hc]
  refine ⟨text.size.toUInt32, out, hf, by simpa [hlen] using hl,
    by simpa [hlen] using hh, ho, ?_, ?_⟩
  · rw [he']
    exact hp
  · exact (format_iso_datetime_frame dst out dt (.Ok text.size.toUInt32) (fuel+40) hf).2

end Oak.Stdlib.Time
