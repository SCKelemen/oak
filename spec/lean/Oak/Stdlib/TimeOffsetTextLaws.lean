import Oak.Stdlib.TimeRFC3339Laws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The numeric suffix writer, factored from the extracted formatter. -/
def write_numeric_suffix (buf : Array UInt8) (pos h m : UInt32) (negative : Bool) (fuel : Nat) :
    Option (Array UInt8 × UInt32) := do
  let buf := buf.setIfInBounds pos.toNat (if negative then 45 else 43)
  let (_, buf) ← put_digits buf (pos+1) h 2 fuel
  let buf := buf.setIfInBounds (pos+3).toNat 58
  let (_, buf) ← put_digits buf (pos+4) m 2 fuel
  pure (buf, pos+6)

theorem write_numeric_suffix_complete (pre : Array UInt8) (h m : UInt32) (negative : Bool) (fuel : Nat)
    (hl : 19 ≤ pre.size) (hh : pre.size ≤ 29) :
    write_numeric_suffix (pre ++ Array.replicate (35-pre.size) 0) pre.size.toUInt32 h m negative (fuel+40) =
      some (pre ++ numeric_offset_text h m negative ++ Array.replicate (29-pre.size) 0, (pre.size+6).toUInt32) := by
  have hc : pre.size = 19 ∨ pre.size = 20 ∨ pre.size = 21 ∨ pre.size = 22 ∨ pre.size = 23 ∨ pre.size = 24 ∨ pre.size = 25 ∨ pre.size = 26 ∨ pre.size = 27 ∨ pre.size = 28 ∨ pre.size = 29 := by omega
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    simp [write_numeric_suffix, hc, put_digits, put_digits.loop1]
  all_goals simp [numeric_offset_text, decimal_byte, Array.replicate_succ,
    Array.setIfInBounds, Array.set]

theorem write_zulu_suffix_complete (pre : Array UInt8)
    (hl : 19 ≤ pre.size) (hh : pre.size ≤ 29) :
    (pre ++ Array.replicate (35-pre.size) 0).setIfInBounds pre.size 90 =
      pre ++ #[90] ++ Array.replicate (34-pre.size) 0 := by
  have hc : pre.size = 19 ∨ pre.size = 20 ∨ pre.size = 21 ∨ pre.size = 22 ∨ pre.size = 23 ∨ pre.size = 24 ∨ pre.size = 25 ∨ pre.size = 26 ∨ pre.size = 27 ∨ pre.size = 28 ∨ pre.size = 29 := by omega
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    simp [hc]
  all_goals simp [Array.replicate_succ, Array.setIfInBounds, Array.set]

end Oak.Stdlib.Time
