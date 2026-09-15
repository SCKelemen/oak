import Oak.Stdlib.BitsetExtracted

/-!
# Oak.Stdlib.BitsetLaws — laws of the extracted `bitset` package

`BitsetExtracted.lean` is generated from `stdlib/bitset.oak`. These theorems
are therefore about the implementation compiled by Oak, subject to the
extractor/compiler correspondence described by `docs/spec/95-extraction.md`.
-/

namespace Oak.Stdlib.Bitset

private def required (bits : UInt32) : UInt32 :=
  if bits % 8 = 0 then bits / 8 else bits / 8 + 1

/-- Zero logical bits require no backing bytes. -/
theorem storage_bytes_zero (fuel : Nat) :
    storage_bytes 0 fuel = some 0 := by
  simp [storage_bytes]

/-- The largest logical bit count still has a representable byte count. -/
theorem storage_bytes_max (fuel : Nat) :
    storage_bytes 4294967295 fuel = some 536870912 := by
  simp [storage_bytes]

/-- Insufficient storage takes precedence over the index error and a failed
set returns every backing byte unchanged. -/
theorem set_short_atomic (storage : Array UInt8) (bits index : UInt32)
    (value : Bool) (fuel : Nat)
    (h : storage.size.toUInt32 < required bits) :
    set storage bits index value fuel =
      some (.Err .StorageTooSmall, storage) := by
  have h' : storage.size.toUInt32 <
      (if bits % 8 = 0 then bits / 8 else bits / 8 + 1) := by
    simpa [required] using h
  simp [set, storage_bytes, h']

/-- A read from insufficient storage reports the capacity error before
attempting to form or access the requested byte index. -/
theorem contains_short (storage : Array UInt8) (bits index : UInt32)
    (fuel : Nat) (h : storage.size.toUInt32 < required bits) :
    contains storage bits index fuel = some (.Err .StorageTooSmall) := by
  have h' : storage.size.toUInt32 <
      (if bits % 8 = 0 then bits / 8 else bits / 8 + 1) := by
    simpa [required] using h
  simp [contains, storage_bytes, h']

/-- Counting rejects insufficient storage before entering its loop, for every
fuel budget. -/
theorem count_short (storage : Array UInt8) (bits : UInt32) (fuel : Nat)
    (h : storage.size.toUInt32 < required bits) :
    count_ones storage bits fuel = some (.Err .StorageTooSmall) := by
  have h' : storage.size.toUInt32 <
      (if bits % 8 = 0 then bits / 8 else bits / 8 + 1) := by
    simpa [required] using h
  simp [count_ones, storage_bytes, h']

/-- With sufficient storage, an out-of-domain set reports the range error and
returns every backing byte unchanged. -/
theorem set_out_of_range_atomic (storage : Array UInt8) (bits index : UInt32)
    (value : Bool) (fuel : Nat)
    (hstorage : ¬ storage.size.toUInt32 < required bits)
    (hindex : index ≥ bits) :
    set storage bits index value fuel =
      some (.Err .BitOutOfRange, storage) := by
  have hstorage' : ¬ storage.size.toUInt32 <
      (if bits % 8 = 0 then bits / 8 else bits / 8 + 1) := by
    simpa [required] using hstorage
  simp [set, storage_bytes, hstorage', hindex]

/-- Counting an empty logical domain succeeds independently of backing bytes.
One fuel step is enough to evaluate the loop guard. -/
theorem count_zero (storage : Array UInt8) (fuel : Nat) :
    count_ones storage 0 (fuel + 1) = some (.Ok 0) := by
  simp [count_ones, storage_bytes, count_ones.loop1]

end Oak.Stdlib.Bitset
