import Oak.Stdlib.TimeRoundtripLaws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem write_clock_shift_0 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : t.nanos = 0) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (19, pre ++ clock_text t f 0 ++ Array.replicate (10+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text,  decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_clock_shift_1 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 1)) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (21, pre ++ clock_text t f 1 ++ Array.replicate (8+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, ht, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text, fraction_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_clock_shift_2 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 2)) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (22, pre ++ clock_text t f 2 ++ Array.replicate (7+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, ht, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text, fraction_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_clock_shift_3 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 3)) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (23, pre ++ clock_text t f 3 ++ Array.replicate (6+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, ht, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text, fraction_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_clock_shift_4 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 4)) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (24, pre ++ clock_text t f 4 ++ Array.replicate (5+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, ht, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text, fraction_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_clock_shift_5 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 5)) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (25, pre ++ clock_text t f 5 ++ Array.replicate (4+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, ht, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text, fraction_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_clock_shift_6 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 6)) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (26, pre ++ clock_text t f 6 ++ Array.replicate (3+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, ht, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text, fraction_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_clock_shift_7 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 7)) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (27, pre ++ clock_text t f 7 ++ Array.replicate (2+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, ht, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text, fraction_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_clock_shift_8 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 8)) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (28, pre ++ clock_text t f 8 ++ Array.replicate (1+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, ht, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text, fraction_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_clock_shift_9 (pre : Array UInt8) (hp : pre.size = 11) (extra : Nat) (he : extra = 0 ∨ extra = 6)
    (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 9)) :
    write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
      some (29, pre ++ clock_text t f 9 ++ Array.replicate (0+extra) 0) := by
  rcases he with rfl | rfl <;>
    simp [write_time, ht, hn, put_digits, put_digits.loop1, hp,
      Array.setIfInBounds_append]
  all_goals simp [clock_text, fraction_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_date_with_padding (d : Date) (extra : Nat) (he : extra = 19 ∨ extra = 25) (fuel : Nat) :
    write_date (Array.replicate (10+extra) 0) 0 d (fuel + 40) =
      some ((), calendar_text d.year.toUInt32 d.month.toUInt32 d.day.toUInt32 ++ Array.replicate extra 0) := by
  rcases he with rfl | rfl <;>
    simp [write_date, put_digits, put_digits.loop1, calendar_text, decimal_byte,
      Array.replicate_succ]

/-- The clock writer composes after an eleven-byte date/T prefix. -/
theorem clock_encoding_shifted (t : Time) (fuel : Nat) (hv : time_valid t fuel = some true) :
    ∃ text : Array UInt8, 8 ≤ text.size ∧ text.size ≤ 18 ∧
      parse_iso_time text (fuel + 40) = some (.Ok t) ∧
      ∀ (pre : Array UInt8) (extra : Nat), pre.size = 11 → (extra = 0 ∨ extra = 6) →
        write_time (pre ++ Array.replicate (18+extra) 0) 11 t (fuel + 40) =
          some ((11+text.size).toUInt32, pre ++ text ++ Array.replicate (18-text.size+extra) 0) := by
  have hfields : t.hour < 24 ∧ t.minute < 60 ∧ t.second < 60 ∧ t.nanos < 1000000000 := by
    simpa [time_valid, and_assoc] using hv
  obtain ⟨hh, hm, hs, hn⟩ := hfields
  by_cases hz : t.nanos = 0
  · refine ⟨clock_text t 0 0, by simp [clock_text], by simp [clock_text],
      parse_clock_0 t 0 fuel hh hm hs hz, ?_⟩
    intro pre extra hp hext
    simpa [clock_text] using write_clock_shift_0 pre hp extra hext t 0 fuel hz
  · have hp : 0 < t.nanos := by bv_decide
    obtain ⟨f, w, hw0, hw9, hf, he, _, ht⟩ := trim_time_fraction t.nanos fuel hp hn
    have hc : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8 ∨ w = 9 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨clock_text t f 1, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text],
        parse_clock_1 t f fuel hh hm hs hf he, ?_⟩
      intro pre extra hpre hext
      simpa [clock_text, fraction_text] using write_clock_shift_1 pre hpre extra hext t f fuel hp ht
    · refine ⟨clock_text t f 2, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text],
        parse_clock_2 t f fuel hh hm hs hf he, ?_⟩
      intro pre extra hpre hext
      simpa [clock_text, fraction_text] using write_clock_shift_2 pre hpre extra hext t f fuel hp ht
    · refine ⟨clock_text t f 3, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text],
        parse_clock_3 t f fuel hh hm hs hf he, ?_⟩
      intro pre extra hpre hext
      simpa [clock_text, fraction_text] using write_clock_shift_3 pre hpre extra hext t f fuel hp ht
    · refine ⟨clock_text t f 4, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text],
        parse_clock_4 t f fuel hh hm hs hf he, ?_⟩
      intro pre extra hpre hext
      simpa [clock_text, fraction_text] using write_clock_shift_4 pre hpre extra hext t f fuel hp ht
    · refine ⟨clock_text t f 5, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text],
        parse_clock_5 t f fuel hh hm hs hf he, ?_⟩
      intro pre extra hpre hext
      simpa [clock_text, fraction_text] using write_clock_shift_5 pre hpre extra hext t f fuel hp ht
    · refine ⟨clock_text t f 6, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text],
        parse_clock_6 t f fuel hh hm hs hf he, ?_⟩
      intro pre extra hpre hext
      simpa [clock_text, fraction_text] using write_clock_shift_6 pre hpre extra hext t f fuel hp ht
    · refine ⟨clock_text t f 7, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text],
        parse_clock_7 t f fuel hh hm hs hf he, ?_⟩
      intro pre extra hpre hext
      simpa [clock_text, fraction_text] using write_clock_shift_7 pre hpre extra hext t f fuel hp ht
    · refine ⟨clock_text t f 8, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text],
        parse_clock_8 t f fuel hh hm hs hf he, ?_⟩
      intro pre extra hpre hext
      simpa [clock_text, fraction_text] using write_clock_shift_8 pre hpre extra hext t f fuel hp ht
    · refine ⟨clock_text t f 9, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text],
        parse_clock_9 t f fuel hh hm hs hf he, ?_⟩
      intro pre extra hpre hext
      simpa [clock_text, fraction_text] using write_clock_shift_9 pre hpre extra hext t f fuel hp ht

theorem parse_valid_calendar_text (d : Date) (fuel : Nat) (hv : date_valid d fuel = some true) :
    parse_iso_date (calendar_text d.year.toUInt32 d.month.toUInt32 d.day.toUInt32)
      (fuel + 40) = some (.Ok d) := by
  obtain ⟨text, hf, hp⟩ := date_codec_roundtrip d (Array.replicate 10 0) (fuel+29) hv (by simp)
  rw [format_date_canonical d _ (fuel+29) hv (by simp)] at hf
  cases hf
  simpa [Nat.add_assoc] using hp

/-- Extended local datetime spelling with a previously proved clock prefix. -/
def datetime_text (d : Date) (clock : Array UInt8) : Array UInt8 :=
  calendar_text d.year.toUInt32 d.month.toUInt32 d.day.toUInt32 ++ #[84] ++ clock

theorem parse_datetime_text (d : Date) (t : Time) (clock : Array UInt8) (fuel : Nat)
    (hd : date_valid d fuel = some true) (hl : 8 ≤ clock.size) (hh : clock.size ≤ 18)
    (ht : parse_iso_time clock (fuel + 40) = some (.Ok t)) :
    parse_iso_datetime (datetime_text d clock) (fuel + 40) = some (.Ok ⟨d,t⟩) := by
  have hsize : (datetime_text d clock).size = 11+clock.size := by simp [datetime_text, calendar_text]
  have hlen : (datetime_text d clock).size.toUInt32.toNat = 11+clock.size := by
    rw [hsize]
    exact UInt32.toNat_ofNat_of_lt' (by change 11+clock.size < 4294967296; omega)
  have hsmall : ¬ (datetime_text d clock).size.toUInt32 < 19 := by
    rw [UInt32.lt_iff_toNat_lt, hlen]
    change ¬ 11+clock.size < 19
    omega
  have hdate : (datetime_text d clock).extract 0 10 =
      calendar_text d.year.toUInt32 d.month.toUInt32 d.day.toUInt32 := by
    simp [datetime_text, calendar_text, Array.extract_append]
  have htime : (datetime_text d clock).extract 11 (datetime_text d clock).size.toUInt32.toNat = clock := by
    rw [hlen]
    simp [datetime_text, calendar_text, Array.extract_append]
  have h4 : (datetime_text d clock).getD 4 0 = 45 := by simp [datetime_text, calendar_text, Array.getElem?_append]
  have h7 : (datetime_text d clock).getD 7 0 = 45 := by simp [datetime_text, calendar_text, Array.getElem?_append]
  have h10 : (datetime_text d clock).getD 10 0 = 84 := by simp [datetime_text, calendar_text, Array.getElem?_append]
  have htime' : (datetime_text d clock).extract 11 ((datetime_text d clock).size % 4294967296) = clock := by simpa using htime
  simp [parse_iso_datetime, hsmall, h4, h7, h10, hdate, htime',
    parse_valid_calendar_text d fuel hd, ht]

theorem datetime_valid_fields (dt : DateTime) (fuel : Nat)
    (hv : datetime_valid dt fuel = some true) :
    date_valid dt.date fuel = some true ∧ time_valid dt.time fuel = some true := by
  simp only [datetime_valid, bind, pure, Option.bind_eq_some_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  cases a <;> cases b <;> simp only [Bool.and_self, Bool.and_false, Bool.and_true, Option.some.injEq, Bool.false_eq_true] at hab
  exact ⟨ha, hb⟩


end Oak.Stdlib.Time
