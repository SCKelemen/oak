import Oak.Stdlib.TimeFractionTrimLaws
import Oak.Stdlib.TimeCopyLaws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem parse_clock_0 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hn : t.nanos = 0) :
    parse_iso_time (clock_text t f 0) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  cases t
  simp [parse_iso_time,  read_digits, read_digits.loop1,
    clock_text,  decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem parse_clock_1 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 10) (hn : t.nanos = f * 100000000) :
    parse_iso_time (clock_text t f 1) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hfrac := fraction_digits_1 f hf
  try simp only [UInt32.mul_one] at hfrac
  have hns : f * 100000000 < 1000000000 := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_mul] at hf ⊢
    simp at hf ⊢
    have hx : f.toNat * 100000000 < 1000000000 := by omega
    have hx' : f.toNat * 100000000 < 4294967296 := by omega
    simpa [Nat.mod_eq_of_lt hx'] using hx
  cases t
  simp [parse_iso_time, parse_iso_time.loop1, read_digits, read_digits.loop1,
    clock_text, fraction_text, decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, hfrac, hns,  time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem parse_clock_2 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 100) (hn : t.nanos = f * 10000000) :
    parse_iso_time (clock_text t f 2) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hfrac := fraction_digits_2 f hf
  try simp only [UInt32.mul_one] at hfrac
  have hns : f * 10000000 < 1000000000 := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_mul] at hf ⊢
    simp at hf ⊢
    have hx : f.toNat * 10000000 < 1000000000 := by omega
    have hx' : f.toNat * 10000000 < 4294967296 := by omega
    simpa [Nat.mod_eq_of_lt hx'] using hx
  cases t
  simp [parse_iso_time, parse_iso_time.loop1, read_digits, read_digits.loop1,
    clock_text, fraction_text, decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, hfrac, hns,  time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem parse_clock_3 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 1000) (hn : t.nanos = f * 1000000) :
    parse_iso_time (clock_text t f 3) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hfrac := fraction_digits_3 f hf
  try simp only [UInt32.mul_one] at hfrac
  have hns : f * 1000000 < 1000000000 := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_mul] at hf ⊢
    simp at hf ⊢
    have hx : f.toNat * 1000000 < 1000000000 := by omega
    have hx' : f.toNat * 1000000 < 4294967296 := by omega
    simpa [Nat.mod_eq_of_lt hx'] using hx
  cases t
  simp [parse_iso_time, parse_iso_time.loop1, read_digits, read_digits.loop1,
    clock_text, fraction_text, decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, hfrac, hns,  time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem parse_clock_4 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 10000) (hn : t.nanos = f * 100000) :
    parse_iso_time (clock_text t f 4) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hfrac := fraction_digits_4 f hf
  try simp only [UInt32.mul_one] at hfrac
  have hns : f * 100000 < 1000000000 := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_mul] at hf ⊢
    simp at hf ⊢
    have hx : f.toNat * 100000 < 1000000000 := by omega
    have hx' : f.toNat * 100000 < 4294967296 := by omega
    simpa [Nat.mod_eq_of_lt hx'] using hx
  cases t
  simp [parse_iso_time, parse_iso_time.loop1, read_digits, read_digits.loop1,
    clock_text, fraction_text, decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, hfrac, hns,  time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem parse_clock_5 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 100000) (hn : t.nanos = f * 10000) :
    parse_iso_time (clock_text t f 5) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hfrac := fraction_digits_5 f hf
  try simp only [UInt32.mul_one] at hfrac
  have hns : f * 10000 < 1000000000 := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_mul] at hf ⊢
    simp at hf ⊢
    have hx : f.toNat * 10000 < 1000000000 := by omega
    have hx' : f.toNat * 10000 < 4294967296 := by omega
    simpa [Nat.mod_eq_of_lt hx'] using hx
  cases t
  simp [parse_iso_time, parse_iso_time.loop1, read_digits, read_digits.loop1,
    clock_text, fraction_text, decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, hfrac, hns,  time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem parse_clock_6 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 1000000) (hn : t.nanos = f * 1000) :
    parse_iso_time (clock_text t f 6) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hfrac := fraction_digits_6 f hf
  try simp only [UInt32.mul_one] at hfrac
  have hns : f * 1000 < 1000000000 := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_mul] at hf ⊢
    simp at hf ⊢
    have hx : f.toNat * 1000 < 1000000000 := by omega
    have hx' : f.toNat * 1000 < 4294967296 := by omega
    simpa [Nat.mod_eq_of_lt hx'] using hx
  cases t
  simp [parse_iso_time, parse_iso_time.loop1, read_digits, read_digits.loop1,
    clock_text, fraction_text, decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, hfrac, hns,  time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem parse_clock_7 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 10000000) (hn : t.nanos = f * 100) :
    parse_iso_time (clock_text t f 7) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hfrac := fraction_digits_7 f hf
  try simp only [UInt32.mul_one] at hfrac
  have hns : f * 100 < 1000000000 := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_mul] at hf ⊢
    simp at hf ⊢
    have hx : f.toNat * 100 < 1000000000 := by omega
    have hx' : f.toNat * 100 < 4294967296 := by omega
    simpa [Nat.mod_eq_of_lt hx'] using hx
  cases t
  simp [parse_iso_time, parse_iso_time.loop1, read_digits, read_digits.loop1,
    clock_text, fraction_text, decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, hfrac, hns,  time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem parse_clock_8 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 100000000) (hn : t.nanos = f * 10) :
    parse_iso_time (clock_text t f 8) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hfrac := fraction_digits_8 f hf
  try simp only [UInt32.mul_one] at hfrac
  have hns : f * 10 < 1000000000 := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_mul] at hf ⊢
    simp at hf ⊢
    have hx : f.toNat * 10 < 1000000000 := by omega
    have hx' : f.toNat * 10 < 4294967296 := by omega
    simpa [Nat.mod_eq_of_lt hx'] using hx
  cases t
  simp [parse_iso_time, parse_iso_time.loop1, read_digits, read_digits.loop1,
    clock_text, fraction_text, decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, hfrac, hns,  time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem parse_clock_9 (t : Time) (f : UInt32) (fuel : Nat)
    (hh : t.hour < 24) (hm : t.minute < 60) (hs : t.second < 60)
    (hf : f < 1000000000) (hn : t.nanos = f * 1) :
    parse_iso_time (clock_text t f 9) (fuel + 40) = some (.Ok t) := by
  have hh' : t.hour.toUInt32 < 100 := by bv_decide
  have hm' : t.minute.toUInt32 < 100 := by bv_decide
  have hs' : t.second.toUInt32 < 100 := by bv_decide
  have hhb : t.hour.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hmb : t.minute.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hsb : t.second.toUInt32 ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have hfrac := fraction_digits_9 f hf
  try simp only [UInt32.mul_one] at hfrac
  have hns : f * 1 < 1000000000 := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_mul] at hf ⊢
    simp at hf ⊢
    have hx : f.toNat * 1 < 1000000000 := by omega
    have hx' : f.toNat * 1 < 4294967296 := by omega
    simpa [Nat.mod_eq_of_lt hx'] using hx
  cases t
  simp [parse_iso_time, parse_iso_time.loop1, read_digits, read_digits.loop1,
    clock_text, fraction_text, decimal_byte_digit, decimal_byte_value,
    decimal_two _ hh', decimal_two _ hm', decimal_two _ hs',
    hhb, hmb, hsb, hfrac,  hf, time_of_day, time_valid, hh, hm, hs]
  simpa using hn.symm

theorem write_clock_0 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : t.nanos = 0) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (8, clock_text t f 0 ++ Array.replicate 10 0) := by
  simp [write_time, hn, put_digits, put_digits.loop1, clock_text,
     decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]

theorem write_clock_1 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 1)) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (10, clock_text t f 1 ++ Array.replicate 8 0) := by
  simp [write_time, ht, hn, put_digits, put_digits.loop1, clock_text,
    fraction_text, decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]

theorem write_clock_2 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 2)) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (11, clock_text t f 2 ++ Array.replicate 7 0) := by
  simp [write_time, ht, hn, put_digits, put_digits.loop1, clock_text,
    fraction_text, decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]

theorem write_clock_3 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 3)) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (12, clock_text t f 3 ++ Array.replicate 6 0) := by
  simp [write_time, ht, hn, put_digits, put_digits.loop1, clock_text,
    fraction_text, decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]

theorem write_clock_4 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 4)) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (13, clock_text t f 4 ++ Array.replicate 5 0) := by
  simp [write_time, ht, hn, put_digits, put_digits.loop1, clock_text,
    fraction_text, decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]

theorem write_clock_5 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 5)) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (14, clock_text t f 5 ++ Array.replicate 4 0) := by
  simp [write_time, ht, hn, put_digits, put_digits.loop1, clock_text,
    fraction_text, decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]

theorem write_clock_6 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 6)) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (15, clock_text t f 6 ++ Array.replicate 3 0) := by
  simp [write_time, ht, hn, put_digits, put_digits.loop1, clock_text,
    fraction_text, decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]

theorem write_clock_7 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 7)) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (16, clock_text t f 7 ++ Array.replicate 2 0) := by
  simp [write_time, ht, hn, put_digits, put_digits.loop1, clock_text,
    fraction_text, decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]

theorem write_clock_8 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 8)) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (17, clock_text t f 8 ++ Array.replicate 1 0) := by
  simp [write_time, ht, hn, put_digits, put_digits.loop1, clock_text,
    fraction_text, decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]

theorem write_clock_9 (t : Time) (f : UInt32) (fuel : Nat)
    (hn : 0 < t.nanos)
    (ht : write_time.loop1 t.nanos 9 (fuel + 40) = some (f, 9)) :
    write_time (Array.replicate 18 0) 0 t (fuel + 40) =
      some (18, clock_text t f 9 ++ Array.replicate 0 0) := by
  simp [write_time, ht, hn, put_digits, put_digits.loop1, clock_text,
    fraction_text, decimal_byte, Array.replicate_succ, Array.setIfInBounds, Array.set]


/-- The actual clock writer produces a bounded parseable prefix for every
    valid time, including all nanosecond values and every trimming depth. -/
theorem clock_encoding (t : Time) (fuel : Nat) (hv : time_valid t fuel = some true) :
    ∃ text : Array UInt8, 8 ≤ text.size ∧ text.size ≤ 18 ∧
      write_time (Array.replicate 18 0) 0 t (fuel + 40) =
        some (text.size.toUInt32, text ++ Array.replicate (18-text.size) 0) ∧
      parse_iso_time text (fuel + 40) = some (.Ok t) := by
  have hfields : t.hour < 24 ∧ t.minute < 60 ∧ t.second < 60 ∧ t.nanos < 1000000000 := by
    simpa [time_valid, and_assoc] using hv
  obtain ⟨hh, hm, hs, hn⟩ := hfields
  by_cases hz : t.nanos = 0
  · refine ⟨clock_text t 0 0, by simp [clock_text], by simp [clock_text], ?_,
      parse_clock_0 t 0 fuel hh hm hs hz⟩
    simpa [clock_text] using write_clock_0 t 0 fuel hz
  · have hp : 0 < t.nanos := by bv_decide
    obtain ⟨f, w, hw0, hw9, hf, he, _, ht⟩ := trim_time_fraction t.nanos fuel hp hn
    have hc : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8 ∨ w = 9 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨clock_text t f 1, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_,
        parse_clock_1 t f fuel hh hm hs hf he⟩
      simpa [clock_text, fraction_text] using write_clock_1 t f fuel hp ht
    · refine ⟨clock_text t f 2, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_,
        parse_clock_2 t f fuel hh hm hs hf he⟩
      simpa [clock_text, fraction_text] using write_clock_2 t f fuel hp ht
    · refine ⟨clock_text t f 3, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_,
        parse_clock_3 t f fuel hh hm hs hf he⟩
      simpa [clock_text, fraction_text] using write_clock_3 t f fuel hp ht
    · refine ⟨clock_text t f 4, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_,
        parse_clock_4 t f fuel hh hm hs hf he⟩
      simpa [clock_text, fraction_text] using write_clock_4 t f fuel hp ht
    · refine ⟨clock_text t f 5, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_,
        parse_clock_5 t f fuel hh hm hs hf he⟩
      simpa [clock_text, fraction_text] using write_clock_5 t f fuel hp ht
    · refine ⟨clock_text t f 6, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_,
        parse_clock_6 t f fuel hh hm hs hf he⟩
      simpa [clock_text, fraction_text] using write_clock_6 t f fuel hp ht
    · refine ⟨clock_text t f 7, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_,
        parse_clock_7 t f fuel hh hm hs hf he⟩
      simpa [clock_text, fraction_text] using write_clock_7 t f fuel hp ht
    · refine ⟨clock_text t f 8, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_,
        parse_clock_8 t f fuel hh hm hs hf he⟩
      simpa [clock_text, fraction_text] using write_clock_8 t f fuel hp ht
    · refine ⟨clock_text t f 9, by simp [clock_text, fraction_text], by simp [clock_text, fraction_text], ?_,
        parse_clock_9 t f fuel hh hm hs hf he⟩
      simpa [clock_text, fraction_text] using write_clock_9 t f fuel hp ht

end Oak.Stdlib.Time
