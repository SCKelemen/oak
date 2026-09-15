import Oak.Stdlib.BufferExtracted

/-!
# Oak.Stdlib.BufferLaws — laws of the extracted `buffer` package

The cursor is a compact runtime witness of the live interval. These theorems
pin failure atomicity and sticky builder state to the implementation compiled
by Oak, so later bulk-copy or target-specific optimizations must preserve the
same storage and cursor frames.
-/

namespace Oak.Stdlib.Buffer

/-- A valid singleton cursor reports exactly the width of its live interval. -/
theorem live_len_valid (cursor : Cursor) (capacity : UInt32) (fuel : Nat)
    (horder : cursor.start ≤ cursor.end_)
    (hend : cursor.end_ ≤ capacity) :
    live_len #[cursor] capacity fuel =
      some (cursor.end_ - cursor.start, #[cursor]) := by
  simp [live_len, check, horder, hend]

/-- Tail space is capacity minus the validated end offset. -/
theorem tail_space_valid (cursor : Cursor) (capacity : UInt32) (fuel : Nat)
    (horder : cursor.start ≤ cursor.end_)
    (hend : cursor.end_ ≤ capacity) :
    tail_space #[cursor] capacity fuel =
      some (capacity - cursor.end_, #[cursor]) := by
  simp [tail_space, check, horder, hend]

/-- Insufficient contiguous tail capacity changes neither cursor nor storage. -/
theorem append_full_atomic (cursor : Cursor) (storage src : Array UInt8)
    (fuel : Nat)
    (horder : cursor.start ≤ cursor.end_)
    (hend : cursor.end_ ≤ storage.size.toUInt32)
    (hfull : ¬ src.size.toUInt32 ≤ storage.size.toUInt32 - cursor.end_) :
    append #[cursor] storage src fuel =
      some (.Err .Full, #[cursor], storage) := by
  simp [append, check, horder, hend, hfull]

/-- An exact peek rejects a short live interval before touching its output. -/
theorem peek_short_atomic (cursor : Cursor) (storage dst : Array UInt8)
    (fuel : Nat)
    (horder : cursor.start ≤ cursor.end_)
    (hend : cursor.end_ ≤ storage.size.toUInt32)
    (hshort : ¬ dst.size.toUInt32 ≤ cursor.end_ - cursor.start) :
    peek_into #[cursor] storage dst fuel =
      some (.Err .InsufficientData, #[cursor], dst) := by
  simp [peek_into, check, horder, hend, hshort]

/-- An oversized consume is atomic with respect to cursor state. -/
theorem consume_short_atomic (cursor : Cursor) (capacity count : UInt32)
    (fuel : Nat)
    (horder : cursor.start ≤ cursor.end_)
    (hend : cursor.end_ ≤ capacity)
    (hshort : ¬ count ≤ cursor.end_ - cursor.start) :
    consume #[cursor] capacity count fuel =
      some (.Err .InsufficientData, #[cursor]) := by
  simp [consume, check, horder, hend, hshort]

/-- Reset restores the valid empty cursor without inspecting storage. -/
theorem reset_singleton (cursor : Cursor) (fuel : Nat) :
    reset #[cursor] fuel = some ((), #[{ start := 0, end_ := 0 }]) := by
  simp [reset]

/-- Once failed, a builder append is a storage-preserving fixed point. -/
theorem append_byte_sticky (length : UInt32) (storage : Array UInt8)
    (value : UInt8) (fuel : Nat) :
    append_byte { length := length, failed := true } storage value fuel =
      some ({ length := length, failed := true }, storage) := by
  simp [append_byte]

/-- Sticky failure also prevents a bulk append from reading or writing bytes. -/
theorem append_bytes_sticky (length : UInt32) (storage src : Array UInt8)
    (fuel : Nat) :
    append_bytes { length := length, failed := true } storage src fuel =
      some ({ length := length, failed := true }, storage) := by
  simp [append_bytes]

/-- Finishing exposes either the exact successful prefix length or `Full`. -/
theorem finish_ok (length : UInt32) (fuel : Nat) :
    finish { length := length, failed := false } fuel = some (.Ok length) := by
  simp [finish]

theorem finish_failed (length : UInt32) (fuel : Nat) :
    finish { length := length, failed := true } fuel = some (.Err .Full) := by
  simp [finish]

end Oak.Stdlib.Buffer
