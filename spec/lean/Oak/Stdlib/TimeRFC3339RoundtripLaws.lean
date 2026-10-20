import Oak.Stdlib.TimeOffsetLaws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def rfc_suffix (z : OffsetDateTime) : Array UInt8 :=
  match z.offset_kind with
  | .UtcDesignator => #[90]
  | _ => numeric_offset_text (offset_magnitude z / 60) (offset_magnitude z % 60) (offset_negative z)

theorem rfc_format_text (z : OffsetDateTime) (clock : Array UInt8) (fuel : Nat)
    (hv : offset_datetime_valid z fuel = some true)
    (hl : 8 ≤ clock.size) (hh : clock.size ≤ 18)
    (hw : ∀ (pre : Array UInt8), pre.size = 11 →
      write_time (pre ++ Array.replicate 24 0) 11 z.datetime.time (fuel+40) =
        some ((11+clock.size).toUInt32, pre ++ clock ++ Array.replicate (24-clock.size) 0)) :
    ∀ dst, let text := datetime_text z.datetime.date clock ++ rfc_suffix z
      format_rfc3339_datetime dst z (fuel+40) =
        copy_time_text dst (text ++ Array.replicate (35-text.size) 0) text.size.toUInt32 (fuel+40) := by
  intro dst
  obtain ⟨hd, _, _, _⟩ := offset_valid_fields z fuel hv
  have hd' : datetime_valid z.datetime (fuel+40) = some true := hd
  have hv' : offset_datetime_valid z (fuel+40) = some true := hv
  let cal := calendar_text z.datetime.date.year.toUInt32 z.datetime.date.month.toUInt32 z.datetime.date.day.toUInt32
  let pre := cal ++ #[84]
  let base := datetime_text z.datetime.date clock
  have hpre : pre.size = 11 := by simp [pre, cal, calendar_text]
  have hsize : base.size = 11+clock.size := by simp [base, datetime_text, calendar_text]
  have hbl : 19 ≤ base.size := by omega
  have hbh : base.size ≤ 29 := by omega
  have hdate := write_date_with_padding z.datetime.date 25 (Or.inr rfl) fuel
  have hjoin : (cal ++ Array.replicate 25 0).setIfInBounds 10 84 = pre ++ Array.replicate 24 0 := by
    simp [cal, pre, calendar_text, Array.replicate_succ]
  have hsub : 35-(11+clock.size) = 24-clock.size := by omega
  have htime : write_time (pre ++ Array.replicate 24 0) 11 z.datetime.time (fuel+40) =
      some (base.size.toUInt32, base ++ Array.replicate (35-base.size) 0) := by
    rw [hsize, hsub]
    exact hw pre hpre
  unfold format_rfc3339_datetime
  simp only [bind, pure]
  rw [hd', Option.bind_some]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hv', Option.bind_some]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hdate, Option.bind_some]
  simp only [Prod.eta, Option.bind_fun_some]
  rw [hjoin, htime, Option.bind_some]
  simp only [Prod.eta]
  change _ = copy_time_text dst (base ++ rfc_suffix z ++ Array.replicate (35-(base ++ rfc_suffix z).size) 0) (base ++ rfc_suffix z).size.toUInt32 (fuel+40)
  have hlen : base.size.toUInt32.toNat = base.size := UInt32.toNat_ofNat_of_lt' (by change base.size < 4294967296; omega)
  have hp1 : 35-(base.size+1) = 34-base.size := by omega
  have hp6 : 35-(base.size+6) = 29-base.size := by omega
  cases hk : z.offset_kind
  · simp only [rfc_suffix, hk, ite_true, Option.bind_some]
    rw [hlen, write_zulu_suffix_complete base hbl hbh]
    change copy_time_text dst (base ++ #[90] ++ Array.replicate (34-base.size) 0) (base.size.toUInt32+1) (fuel+40) = _
    simp [ hp1]
  all_goals
    have hn := write_numeric_suffix_complete base (offset_magnitude z/60) (offset_magnitude z%60) (offset_negative z) fuel hbl hbh
    simp only [write_numeric_suffix, offset_negative, offset_magnitude, hk, bind, pure] at hn
    simp only [Bool.false_eq_true, ite_false, decide_eq_true_eq]
    rw [hn, Option.bind_some]
    simp only [Prod.fst]
    have htlen : (rfc_suffix z).size = 6 := by simp [rfc_suffix, hk, numeric_offset_text]
    simp only [Array.size_append, htlen, hp6]
    simp only [rfc_suffix, hk, offset_negative, offset_magnitude]

/-- Canonical RFC3339 text preserves the civil fields and the offset assertion. -/
theorem rfc3339_encoding (z : OffsetDateTime) (fuel : Nat)
    (hv : offset_datetime_valid z fuel = some true) :
    ∃ text : Array UInt8, 20 ≤ text.size ∧ text.size ≤ 35 ∧
      parse_rfc3339_datetime text (fuel+40) = some (.Ok z) ∧
      ∀ dst, format_rfc3339_datetime dst z (fuel+40) =
        copy_time_text dst (text ++ Array.replicate (35-text.size) 0) text.size.toUInt32 (fuel+40) := by
  obtain ⟨hdt, hol, hoh, hkind⟩ := offset_valid_fields z fuel hv
  obtain ⟨hd, ht⟩ := datetime_valid_fields z.datetime fuel hdt
  obtain ⟨clock, hl, hh, hw, hz, hn⟩ := rfc_clock_encoding z.datetime.time fuel ht
  have hsl : 1 ≤ (rfc_suffix z).size ∧ (rfc_suffix z).size ≤ 6 := by
    cases hk : z.offset_kind <;> simp [rfc_suffix, hk, numeric_offset_text]
  have hsz : (datetime_text z.datetime.date clock ++ rfc_suffix z).size = 11+clock.size+(rfc_suffix z).size := by
    simp [datetime_text, calendar_text, Nat.add_assoc]
  refine ⟨datetime_text z.datetime.date clock ++ rfc_suffix z, by rw [hsz]; omega,
    by rw [hsz]; omega, ?_, rfc_format_text z clock fuel hv hl hh hw⟩
  change _ = some (Result_OffsetDateTime_TimeError.Ok ⟨⟨z.datetime.date,z.datetime.time⟩,z.offset_minutes,z.offset_kind⟩)
  cases hk : z.offset_kind
  · have he : z.offset_minutes = 0 := by simpa [hk] using hkind
    simpa [rfc_suffix, hk, he] using hz z.datetime.date hd
  · obtain ⟨hmagh, hmagm, hvalue, htag⟩ := numeric_offset_reconstruct z.offset_minutes hol hoh
    have hp := hn z.datetime.date (offset_magnitude z/60) (offset_magnitude z%60)
      (decide (z.offset_minutes < 0)) hd hmagh hmagm
    simpa only [rfc_suffix, hk, offset_negative, Bool.or_false, offset_magnitude, hvalue, htag] using hp
  · have he : z.offset_minutes = 0 := by simpa [hk] using hkind
    have hzero : (0 : Int32).toUInt32 = 0 := by decide
    have hp := hn z.datetime.date 0 0 true hd (by decide) (by decide)
    simpa [rfc_suffix, hk, offset_negative, offset_magnitude, he, hzero, numeric_offset_value, numeric_offset_kind] using hp

/-- Every valid RFC3339 value round-trips, including its offset kind, through
    any destination with at least thirty-five bytes. -/
theorem rfc3339_codec_roundtrip (z : OffsetDateTime) (dst : Array UInt8) (fuel : Nat)
    (hv : offset_datetime_valid z fuel = some true) (hd : 35 ≤ dst.size) (hs : dst.size < 4294967296) :
    ∃ n out, format_rfc3339_datetime dst z (fuel+40) = some (.Ok n, out) ∧
      20 ≤ n.toNat ∧ n.toNat ≤ 35 ∧ out.size = dst.size ∧
      parse_rfc3339_datetime (out.extract 0 n.toNat) (fuel+40) = some (.Ok z) ∧
      ∀ k, n.toNat ≤ k → out[k]? = dst[k]? := by
  obtain ⟨text, hl, hh, hp, hw⟩ := rfc3339_encoding z fuel hv
  have hlen : text.size.toUInt32.toNat = text.size := UInt32.toNat_ofNat_of_lt' (by change text.size < 4294967296; omega)
  obtain ⟨out, hc, ho, he⟩ := copy_time_text_complete dst
    (text ++ Array.replicate (35-text.size) 0) text.size.toUInt32 (fuel+40)
    (by rw [hlen]; omega) hs (by simp [hlen]) (by rw [hlen]; omega)
  have he' : out.extract 0 text.size.toUInt32.toNat = text := by
    rw [he, hlen]
    simp [Array.extract_append]
  have hf : format_rfc3339_datetime dst z (fuel+40) = some (.Ok text.size.toUInt32, out) := by
    rw [hw, hc]
  refine ⟨text.size.toUInt32, out, hf, by simpa [hlen] using hl,
    by simpa [hlen] using hh, ho, ?_, ?_⟩
  · rw [he']
    exact hp
  · exact (format_rfc3339_datetime_frame dst out z (.Ok text.size.toUInt32) (fuel+40) hf).2

end Oak.Stdlib.Time
