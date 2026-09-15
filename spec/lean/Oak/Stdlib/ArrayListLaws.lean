import Oak.Stdlib.ArrayListExtracted

/-!
# Oak.Stdlib.ArrayListLaws — laws of the extracted `array_list` package

These frame theorems pin the package's checked cursor invariant and failure
atomicity. A future bulk-move or target-specific realization must preserve the
same result, cursor, and storage when an operation is rejected.
-/

namespace Oak.Stdlib.ArrayList

/-- A valid singleton cursor passes validation without changing state. -/
theorem check_valid (cursor : Cursor) (capacity : UInt32) (fuel : Nat)
    (hvalid : cursor.length ≤ capacity) :
    check #[cursor] capacity fuel = some ((), #[cursor]) := by
  simp [check, hvalid]

/-- Pushing to a full backing array changes neither cursor nor storage. -/
theorem push_full_atomic (storage : Array UInt8) (value : UInt8) (fuel : Nat) :
    push_u8 #[{ length := storage.size.toUInt32 }] storage value fuel =
      some (.Err .Full, #[{ length := storage.size.toUInt32 }], storage) := by
  simp [push_u8, check]

/-- An out-of-bounds read preserves cursor state. -/
theorem get_oob (cursor : Cursor) (storage : Array UInt8)
    (index : UInt32) (fuel : Nat)
    (hvalid : cursor.length ≤ storage.size.toUInt32)
    (hoob : index ≥ cursor.length) :
    get_u8 #[cursor] storage index fuel =
      some (.Err .OutOfBounds, #[cursor]) := by
  simp [get_u8, check, hvalid, hoob]

/-- A rejected replacement is atomic with respect to cursor and storage. -/
theorem set_oob_atomic (cursor : Cursor) (storage : Array UInt8)
    (index : UInt32) (value : UInt8) (fuel : Nat)
    (hvalid : cursor.length ≤ storage.size.toUInt32)
    (hoob : index ≥ cursor.length) :
    set_u8 #[cursor] storage index value fuel =
      some (.Err .OutOfBounds, #[cursor], storage) := by
  simp [set_u8, check, hvalid, hoob]

/-- Popping an empty list leaves its cursor and backing storage unchanged. -/
theorem pop_empty_atomic (storage : Array UInt8) (fuel : Nat) :
    pop_u8 #[{ length := 0 }] storage fuel =
      some (.Err .Empty, #[{ length := 0 }], storage) := by
  simp [pop_u8, check]

/-- Insertion beyond the live prefix is rejected before shifting elements. -/
theorem insert_oob_atomic (cursor : Cursor) (storage : Array UInt8)
    (index : UInt32) (value : UInt8) (fuel : Nat)
    (hvalid : cursor.length ≤ storage.size.toUInt32)
    (hoob : index > cursor.length) :
    insert_u8 #[cursor] storage index value fuel =
      some (.Err .OutOfBounds, #[cursor], storage) := by
  simp [insert_u8, check, hvalid, hoob]

/-- Removal beyond the live prefix is rejected before moving elements. -/
theorem remove_oob_atomic (cursor : Cursor) (storage : Array UInt8)
    (index : UInt32) (fuel : Nat)
    (hvalid : cursor.length ≤ storage.size.toUInt32)
    (hoob : index ≥ cursor.length) :
    remove_u8 #[cursor] storage index fuel =
      some (.Err .OutOfBounds, #[cursor], storage) := by
  simp [remove_u8, check, hvalid, hoob]

/-- Constant-time removal has the same rejection frame as ordered removal. -/
theorem swap_remove_oob_atomic (cursor : Cursor) (storage : Array UInt8)
    (index : UInt32) (fuel : Nat)
    (hvalid : cursor.length ≤ storage.size.toUInt32)
    (hoob : index ≥ cursor.length) :
    swap_remove_u8 #[cursor] storage index fuel =
      some (.Err .OutOfBounds, #[cursor], storage) := by
  simp [swap_remove_u8, check, hvalid, hoob]

/-- Clearing a valid cursor resets only its live-prefix length. -/
theorem clear_valid (cursor : Cursor) (capacity : UInt32) (fuel : Nat)
    (hvalid : cursor.length ≤ capacity) :
    clear #[cursor] capacity fuel = some ((), #[{ length := 0 }]) := by
  simp [clear, check, hvalid]

end Oak.Stdlib.ArrayList
