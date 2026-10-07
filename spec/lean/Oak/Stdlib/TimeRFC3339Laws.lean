import Oak.Stdlib.TimeTimestampLaws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def numeric_offset_text (h m : UInt32) (negative : Bool) : Array UInt8 :=
  #[if negative then 45 else 43, decimal_byte (h/10), decimal_byte h, 58,
    decimal_byte (m/10), decimal_byte m]
def numeric_offset_value (h m : UInt32) (negative : Bool) : Int32 :=
  if negative then -(h*60+m).toInt32 else (h*60+m).toInt32
def numeric_offset_kind (h m : UInt32) (negative : Bool) : OffsetKind :=
  if negative && (numeric_offset_value h m negative == 0) then .UnknownLocal else .Numeric

theorem parse_rfc_numeric_0 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hn : t.nanos = 0)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 0) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_0 t f fuel hh hm hs hn
  simp only [calendar_text] at hdate
  simp [clock_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime,  datetime_text, calendar_text,
    clock_text,  numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_0 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hn : t.nanos = 0)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 0) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_0 t f fuel hh hm hs hn
  simp only [calendar_text] at hdate
  simp [clock_text] at htime
  simp [parse_rfc3339_datetime,  datetime_text, calendar_text,
    clock_text,    hdate, htime]

theorem parse_rfc_numeric_1 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 10) (hn : t.nanos = f*100000000)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 1) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_1 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_1 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 10) (hn : t.nanos = f*100000000)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 1) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_1 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_numeric_2 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 100) (hn : t.nanos = f*10000000)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 2) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_2 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_2 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 100) (hn : t.nanos = f*10000000)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 2) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_2 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_numeric_3 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 1000) (hn : t.nanos = f*1000000)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 3) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_3 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_3 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 1000) (hn : t.nanos = f*1000000)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 3) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_3 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_numeric_4 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 10000) (hn : t.nanos = f*100000)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 4) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_4 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_4 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 10000) (hn : t.nanos = f*100000)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 4) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_4 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_numeric_5 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 100000) (hn : t.nanos = f*10000)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 5) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_5 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_5 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 100000) (hn : t.nanos = f*10000)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 5) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_5 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_numeric_6 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 1000000) (hn : t.nanos = f*1000)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 6) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_6 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_6 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 1000000) (hn : t.nanos = f*1000)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 6) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_6 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_numeric_7 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 10000000) (hn : t.nanos = f*100)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 7) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_7 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_7 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 10000000) (hn : t.nanos = f*100)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 7) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_7 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_numeric_8 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 100000000) (hn : t.nanos = f*10)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 8) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_8 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_8 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 100000000) (hn : t.nanos = f*10)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 8) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_8 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_numeric_9 (d : Date) (t : Time) (f oh om : UInt32) (negative : Bool) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 1000000000) (hn : t.nanos = f*1)
    (hoh : oh < 24) (hom : om < 60)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 9) ++ numeric_offset_text oh om negative)
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩) := by
  have hoh' : oh < 100 := by bv_decide
  have hom' : om < 100 := by bv_decide
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_9 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  cases negative <;>
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, numeric_offset_text, numeric_offset_value, numeric_offset_kind,
    read_digits, read_digits.loop1, decimal_byte_value, decimal_two oh hoh', decimal_two om hom', hoh, hom,
    decimal_byte_bounds, is_digit, hdate, htime]

theorem parse_rfc_zulu_9 (d : Date) (t : Time) (f : UInt32) (fuel : Nat)
    (hd : date_valid d fuel = some true)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 1000000000) (hn : t.nanos = f*1)
    : parse_rfc3339_datetime (datetime_text d (clock_text t f 9) ++ #[90])
      (fuel+40) = some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩) := by
  have hdate := parse_valid_calendar_text d fuel hd
  have htime := parse_clock_9 t f fuel hh hm hs hf hn
  simp only [calendar_text] at hdate
  simp [clock_text, fraction_text] at htime
  simp [parse_rfc3339_datetime, parse_rfc3339_datetime.loop1, datetime_text, calendar_text,
    clock_text, fraction_text, decimal_byte_bounds, is_digit, hdate, htime]


/-- A canonical fractional clock works inside RFC3339 for every legal suffix. -/
theorem rfc_clock_encoding (t : Time) (fuel : Nat) (hv : time_valid t fuel = some true) :
    ∃ text : Array UInt8, 8 ≤ text.size ∧ text.size ≤ 18 ∧
      (∀ (pre : Array UInt8), pre.size = 11 →
        write_time (pre ++ Array.replicate 24 0) 11 t (fuel+40) =
          some ((11+text.size).toUInt32, pre ++ text ++ Array.replicate (24-text.size) 0)) ∧
      (∀ d, date_valid d fuel = some true →
        parse_rfc3339_datetime (datetime_text d text ++ #[90]) (fuel+40) =
          some (.Ok ⟨⟨d,t⟩,0,.UtcDesignator⟩)) ∧
      (∀ d oh om negative, date_valid d fuel = some true → oh < 24 → om < 60 →
        parse_rfc3339_datetime (datetime_text d text ++ numeric_offset_text oh om negative) (fuel+40) =
          some (.Ok ⟨⟨d,t⟩,numeric_offset_value oh om negative,numeric_offset_kind oh om negative⟩)) := by
  have hfields : t.hour < 24 ∧ t.minute < 60 ∧ t.second < 60 ∧ t.nanos < 1000000000 := by
    simpa [time_valid, and_assoc] using hv
  obtain ⟨hh, hm, hs, hn⟩ := hfields
  by_cases hz : t.nanos = 0
  · refine ⟨clock_text t 0 0, by simp [clock_text], by simp [clock_text], ?_, ?_, ?_⟩
    · intro pre hpre
      simpa [clock_text, fraction_text] using write_clock_shift_0 pre hpre 6 (Or.inr rfl) t 0 fuel hz
    · intro d hd
      exact parse_rfc_zulu_0 d t 0 fuel hd hh hm hs hz
    · intro d oh om negative hd hoh hom
      exact parse_rfc_numeric_0 d t 0 oh om negative fuel hd hh hm hs hz hoh hom
  · have hp : 0 < t.nanos := by bv_decide
    obtain ⟨f, w, hw0, hw9, hf, he, _, ht⟩ := trim_time_fraction t.nanos fuel hp hn
    have hc : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8 ∨ w = 9 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨clock_text t f 1, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_, ?_, ?_⟩
      · intro pre hpre
        simpa [clock_text, fraction_text] using write_clock_shift_1 pre hpre 6 (Or.inr rfl) t f fuel hp ht
      · intro d hd
        exact parse_rfc_zulu_1 d t f fuel hd hh hm hs hf he
      · intro d oh om negative hd hoh hom
        exact parse_rfc_numeric_1 d t f oh om negative fuel hd hh hm hs hf he hoh hom
    · refine ⟨clock_text t f 2, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_, ?_, ?_⟩
      · intro pre hpre
        simpa [clock_text, fraction_text] using write_clock_shift_2 pre hpre 6 (Or.inr rfl) t f fuel hp ht
      · intro d hd
        exact parse_rfc_zulu_2 d t f fuel hd hh hm hs hf he
      · intro d oh om negative hd hoh hom
        exact parse_rfc_numeric_2 d t f oh om negative fuel hd hh hm hs hf he hoh hom
    · refine ⟨clock_text t f 3, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_, ?_, ?_⟩
      · intro pre hpre
        simpa [clock_text, fraction_text] using write_clock_shift_3 pre hpre 6 (Or.inr rfl) t f fuel hp ht
      · intro d hd
        exact parse_rfc_zulu_3 d t f fuel hd hh hm hs hf he
      · intro d oh om negative hd hoh hom
        exact parse_rfc_numeric_3 d t f oh om negative fuel hd hh hm hs hf he hoh hom
    · refine ⟨clock_text t f 4, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_, ?_, ?_⟩
      · intro pre hpre
        simpa [clock_text, fraction_text] using write_clock_shift_4 pre hpre 6 (Or.inr rfl) t f fuel hp ht
      · intro d hd
        exact parse_rfc_zulu_4 d t f fuel hd hh hm hs hf he
      · intro d oh om negative hd hoh hom
        exact parse_rfc_numeric_4 d t f oh om negative fuel hd hh hm hs hf he hoh hom
    · refine ⟨clock_text t f 5, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_, ?_, ?_⟩
      · intro pre hpre
        simpa [clock_text, fraction_text] using write_clock_shift_5 pre hpre 6 (Or.inr rfl) t f fuel hp ht
      · intro d hd
        exact parse_rfc_zulu_5 d t f fuel hd hh hm hs hf he
      · intro d oh om negative hd hoh hom
        exact parse_rfc_numeric_5 d t f oh om negative fuel hd hh hm hs hf he hoh hom
    · refine ⟨clock_text t f 6, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_, ?_, ?_⟩
      · intro pre hpre
        simpa [clock_text, fraction_text] using write_clock_shift_6 pre hpre 6 (Or.inr rfl) t f fuel hp ht
      · intro d hd
        exact parse_rfc_zulu_6 d t f fuel hd hh hm hs hf he
      · intro d oh om negative hd hoh hom
        exact parse_rfc_numeric_6 d t f oh om negative fuel hd hh hm hs hf he hoh hom
    · refine ⟨clock_text t f 7, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_, ?_, ?_⟩
      · intro pre hpre
        simpa [clock_text, fraction_text] using write_clock_shift_7 pre hpre 6 (Or.inr rfl) t f fuel hp ht
      · intro d hd
        exact parse_rfc_zulu_7 d t f fuel hd hh hm hs hf he
      · intro d oh om negative hd hoh hom
        exact parse_rfc_numeric_7 d t f oh om negative fuel hd hh hm hs hf he hoh hom
    · refine ⟨clock_text t f 8, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_, ?_, ?_⟩
      · intro pre hpre
        simpa [clock_text, fraction_text] using write_clock_shift_8 pre hpre 6 (Or.inr rfl) t f fuel hp ht
      · intro d hd
        exact parse_rfc_zulu_8 d t f fuel hd hh hm hs hf he
      · intro d oh om negative hd hoh hom
        exact parse_rfc_numeric_8 d t f oh om negative fuel hd hh hm hs hf he hoh hom
    · refine ⟨clock_text t f 9, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_, ?_, ?_⟩
      · intro pre hpre
        simpa [clock_text, fraction_text] using write_clock_shift_9 pre hpre 6 (Or.inr rfl) t f fuel hp ht
      · intro d hd
        exact parse_rfc_zulu_9 d t f fuel hd hh hm hs hf he
      · intro d oh om negative hd hoh hom
        exact parse_rfc_numeric_9 d t f oh om negative fuel hd hh hm hs hf he hoh hom

end Oak.Stdlib.Time
