import Oak.Stdlib.BytesExtracted

/-!
# Oak.Stdlib.BytesLaws — laws of the extracted `bytes` package

`BytesExtracted.lean` is generated from `stdlib/bytes.oak`. These theorems are
therefore about the implementation compiled by Oak, subject to the extractor
and compiler correspondence described by `docs/spec/95-extraction.md`.
-/

namespace Oak.Stdlib.Bytes

/-- An offset beyond the logical length is rejected without ever forming the
potentially wrapping sum `offset + width`. -/
theorem range_fits_offset_past_end (length offset width : UInt32) (fuel : Nat)
    (h : offset > length) :
    range_fits length offset width fuel = some false := by
  simp [range_fits, h]

/-- A zero-width range at the end is valid. -/
theorem range_fits_empty_at_end (length : UInt32) (fuel : Nat) :
    range_fits length length 0 fuel = some true := by
  simp [range_fits]

/-- A short destination is rejected before the copy loop and is returned
byte-for-byte unchanged, independently of the available loop fuel. -/
theorem copy_short_atomic (dst src : Array UInt8) (fuel : Nat)
    (h : dst.size.toUInt32 < src.size.toUInt32) :
    copy_into dst src fuel = some (.Err .DestinationTooSmall, dst) := by
  simp [copy_into, h]

/-- Different logical lengths compare unequal without entering the comparison
loop, independently of the available loop fuel. -/
theorem equal_length_mismatch (left right : Array UInt8) (fuel : Nat)
    (h : left.size.toUInt32 ≠ right.size.toUInt32) :
    equal left right fuel = some false := by
  simp [equal, h]

/-- Searching an empty byte sequence completes immediately and reports ordinary
absence. One fuel step is enough to evaluate the loop guard. -/
theorem find_empty (needle : UInt8) (fuel : Nat) :
    find #[] needle (fuel + 1) = some .None := by
  simp [find, find.loop1]

/-- Copying an empty byte sequence succeeds without changing the destination.
One fuel step is enough to evaluate the loop guard. -/
theorem copy_empty (dst : Array UInt8) (fuel : Nat) :
    copy_into dst #[] (fuel + 1) = some (.Ok 0, dst) := by
  simp [copy_into, copy_into.loop1]

/-- A rejected offset copy returns every destination byte unchanged. The
hypothesis is the exact guard computed by the extracted Oak implementation. -/
theorem copy_at_failure_atomic (dst src : Array UInt8) (offset : UInt32)
    (fuel : Nat)
    (h : range_fits dst.size.toUInt32 offset src.size.toUInt32 fuel =
      some false) :
    copy_at dst offset src fuel = some (.Err .OutOfBounds, dst) := by
  simp [copy_at, h]

/-- An invalid destination range prevents either overlap loop from starting,
so a failed move returns the complete original storage. -/
theorem move_invalid_destination_atomic (storage : Array UInt8)
    (dst src count : UInt32) (fuel : Nat)
    (h : dst > storage.size.toUInt32) :
    move_within storage dst src count fuel =
      some (.Err .OutOfBounds, storage) := by
  simp [move_within, range_fits, h]

/-- Empty byte sequences compare equal. One fuel step evaluates the loop
guard, independently of the remaining budget. -/
theorem compare_empty (fuel : Nat) :
    compare #[] #[] (fuel + 1) = some 0 := by
  simp [compare, compare.loop1]

end Oak.Stdlib.Bytes
