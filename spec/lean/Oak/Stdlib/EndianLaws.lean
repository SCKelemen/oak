import Oak.Stdlib.EndianExtracted

/-!
# Oak.Stdlib.EndianLaws — laws of the extracted `endian` package

The fixed-width codecs validate the complete byte range before any access.
These theorems make failure atomicity an optimization precondition: a target
load/store realization may replace the scalar code only when it preserves the
same guard, byte order, result, and caller-owned storage.
-/

namespace Oak.Stdlib.Endian

/-- Every rejected little-endian 16-bit write preserves the full destination. -/
theorem write_u16_le_failure_atomic (dst : Array UInt8) (offset : UInt32)
    (value : UInt16) (fuel : Nat)
    (h : range_fits dst.size.toUInt32 offset 2 fuel = some false) :
    write_u16_le dst offset value fuel =
      some (.Err .BufferTooSmall, dst) := by
  simp [write_u16_le, h]

/-- Every rejected big-endian 16-bit write preserves the full destination. -/
theorem write_u16_be_failure_atomic (dst : Array UInt8) (offset : UInt32)
    (value : UInt16) (fuel : Nat)
    (h : range_fits dst.size.toUInt32 offset 2 fuel = some false) :
    write_u16_be dst offset value fuel =
      some (.Err .BufferTooSmall, dst) := by
  simp [write_u16_be, h]

/-- Every rejected little-endian 32-bit write preserves the full destination. -/
theorem write_u32_le_failure_atomic (dst : Array UInt8) (offset : UInt32)
    (value : UInt32) (fuel : Nat)
    (h : range_fits dst.size.toUInt32 offset 4 fuel = some false) :
    write_u32_le dst offset value fuel =
      some (.Err .BufferTooSmall, dst) := by
  simp [write_u32_le, h]

/-- Every rejected big-endian 32-bit write preserves the full destination. -/
theorem write_u32_be_failure_atomic (dst : Array UInt8) (offset : UInt32)
    (value : UInt32) (fuel : Nat)
    (h : range_fits dst.size.toUInt32 offset 4 fuel = some false) :
    write_u32_be dst offset value fuel =
      some (.Err .BufferTooSmall, dst) := by
  simp [write_u32_be, h]

/-- Every rejected little-endian 64-bit write preserves the full destination. -/
theorem write_u64_le_failure_atomic (dst : Array UInt8) (offset : UInt32)
    (value : UInt64) (fuel : Nat)
    (h : range_fits dst.size.toUInt32 offset 8 fuel = some false) :
    write_u64_le dst offset value fuel =
      some (.Err .BufferTooSmall, dst) := by
  simp [write_u64_le, h]

/-- Every rejected big-endian 64-bit write preserves the full destination. -/
theorem write_u64_be_failure_atomic (dst : Array UInt8) (offset : UInt32)
    (value : UInt64) (fuel : Nat)
    (h : range_fits dst.size.toUInt32 offset 8 fuel = some false) :
    write_u64_be dst offset value fuel =
      some (.Err .BufferTooSmall, dst) := by
  simp [write_u64_be, h]

/-- The little-endian definition fixes the least-significant byte first. -/
theorem read_u16_le_example :
    read_u16_le #[0x34, 0x12] 0 0 = some (.Ok 0x1234) := by
  native_decide

/-- The big-endian definition fixes the most-significant byte first. -/
theorem read_u32_be_example :
    read_u32_be #[0x12, 0x34, 0x56, 0x78] 0 0 =
      some (.Ok 0x12345678) := by
  native_decide

/-- Rejected reads return the same recoverable error and perform no access. -/
theorem read_u64_le_failure (src : Array UInt8) (offset : UInt32) (fuel : Nat)
    (h : range_fits src.size.toUInt32 offset 8 fuel = some false) :
    read_u64_le src offset fuel = some (.Err .BufferTooSmall) := by
  simp [read_u64_le, h]

end Oak.Stdlib.Endian
