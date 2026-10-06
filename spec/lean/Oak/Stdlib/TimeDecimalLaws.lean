import Oak.Stdlib.TimeCalendarExtracted
import Std.Tactic.BVDecide

/-! # Canonical decimal calendar text
Fixed-width digit reconstruction and the ten-byte formatter/parser bridge.
The bounded bit-vector lemmas use the pinned toolchain's native LRAT checker;
they are not kernel-only arithmetic proofs. No grammar completeness is claimed.
-/
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- One ASCII decimal digit, as written by put_digits. -/
def decimal_byte (n : UInt32) : UInt8 := 48 + (n % 10).toUInt8

private theorem decimal_byte_bounds (n : UInt32) :
    48 ≤ decimal_byte n ∧ decimal_byte n ≤ 57 := by
  unfold decimal_byte
  bv_decide

private theorem decimal_byte_value (n : UInt32) :
    ((decimal_byte n).toUInt32 - 48) % 256 = n % 10 := by
  unfold decimal_byte
  bv_decide

private theorem decimal_byte_digit (n : UInt32) (fuel : Nat) :
    is_digit (decimal_byte n) fuel = some true := by
  obtain ⟨hl, hh⟩ := decimal_byte_bounds n
  simp [is_digit, hl, hh]

/-- The fixed-width canonical calendar spelling. -/
def calendar_text (y m d : UInt32) : Array UInt8 :=
  #[decimal_byte (y / 10 / 10 / 10), decimal_byte (y / 10 / 10),
    decimal_byte (y / 10), decimal_byte y, 45,
    decimal_byte (m / 10), decimal_byte m, 45,
    decimal_byte (d / 10), decimal_byte d]

private theorem decimal_two (v : UInt32) (h : v < 100) :
    (v / 10 % 10) * 10 + v % 10 = v := by bv_decide
private theorem decimal_four (v : UInt32) (h : v < 10000) :
    (((v / 10 / 10 / 10 % 10) * 10 + v / 10 / 10 % 10) * 10 +
      v / 10 % 10) * 10 + v % 10 = v := by bv_decide

theorem read_calendar_year (y m d : UInt32) (fuel : Nat) (hy : y < 10000) :
    read_digits (calendar_text y m d) 0 4 (fuel + 11) = some y := by
  simp [read_digits, read_digits.loop1, calendar_text, decimal_byte_digit,
    decimal_byte_value, decimal_four y hy, BAD_DIGITS]

theorem write_calendar_text (d : Date) (fuel : Nat) :
    write_date (Array.replicate 10 0) 0 d (fuel + 11) =
      some ((), calendar_text d.year.toUInt32 d.month.toUInt32 d.day.toUInt32) := by
  simp [write_date, put_digits, put_digits.loop1, calendar_text, decimal_byte,
    Array.replicate_succ, Array.setIfInBounds, Array.set]

private theorem decimal_byte_not_week (n : UInt32) : decimal_byte n ≠ 87 := by
  have h := decimal_byte_bounds n
  bv_decide

/-- Parsing the canonical calendar spelling recovers its numeric fields. -/
theorem parse_calendar_text (y m d : UInt32) (fuel : Nat)
    (hy : y < 10000) (hm : m < 100) (hd : d < 100) :
    parse_iso_date (calendar_text y m d) (fuel + 11) =
      date_create y.toInt32 m.toUInt8 d.toUInt8 (fuel + 11) := by
  have ybad : y ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have mbad : m ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  have dbad : d ≠ BAD_DIGITS := by unfold BAD_DIGITS; bv_decide
  simp [parse_iso_date, read_digits, read_digits.loop1, calendar_text,
    decimal_byte_digit, decimal_byte_value, decimal_four y hy,
    decimal_two m hm, decimal_two d hd, decimal_byte_not_week,
    ybad, mbad, dbad]

/-- Copying all ten canonical bytes returns the exact calendar spelling. -/
theorem copy_calendar_text (dst : Array UInt8) (y m d : UInt32) (fuel : Nat)
    (h : dst.size = 10) :
    copy_time_text dst (calendar_text y m d) 10 (fuel + 11) =
      some (.Ok 10, calendar_text y m d) := by
  simp [copy_time_text, copy_time_text.loop1, h]
  apply Array.ext_getElem?
  intro i
  simp only [Array.getElem?_setIfInBounds, Array.size_setIfInBounds, h]
  by_cases hi : i < 10
  · have hi0 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases hi0 with hi0 | hi0 | hi0 | hi0 | hi0 | hi0 | hi0 | hi0 | hi0 | hi0 <;>
      subst i <;> simp [calendar_text]
  · have hi0 : ∀ j, j < 10 → j ≠ i := by omega
    have hr : (calendar_text y m d).size ≤ i := by simpa [calendar_text] using Nat.le_of_not_gt hi
    simp [hi0, Array.getElem?_eq_none (by omega : dst.size ≤ i), Array.getElem?_eq_none hr]

end Oak.Stdlib.Time
