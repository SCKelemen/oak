import Oak.Stdlib.APDUParserCorrectness

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
namespace Oak.Stdlib.APDUParserControls
open APDUExtracted

-- Each successful control states every field, including nonzero header bytes.
def expected (form : smartcard_sapdu__CommandCase) (at_ count : UInt32)
    (response : Option_u32) (n : UInt32) : smartcard_sapdu__Command :=
  ⟨0x80, 0xca, 1, 2, form, at_, count, response, n⟩

theorem case1 : smartcard_sapdu__decode #[0x80,0xca,1,2] 0 =
    some (.Ok (expected .Case1 4 0 .None 4)) := by decide

theorem case2_short_zero : smartcard_sapdu__decode #[0x80,0xca,1,2,0] 0 =
    some (.Ok (expected .Case2Short 5 0 (.Some 256) 5)) := by decide

theorem case3_short : smartcard_sapdu__decode #[0x80,0xca,1,2,1,0xaa] 0 =
    some (.Ok (expected .Case3Short 5 1 .None 6)) := by decide

theorem case4_short_zero : smartcard_sapdu__decode #[0x80,0xca,1,2,1,0xaa,0] 0 =
    some (.Ok (expected .Case4Short 5 1 (.Some 256) 7)) := by decide

theorem case2_extended_zero : smartcard_sapdu__decode #[0x80,0xca,1,2,0,0,0] 0 =
    some (.Ok (expected .Case2Extended 7 0 (.Some 65536) 7)) := by decide

theorem case3_extended : smartcard_sapdu__decode #[0x80,0xca,1,2,0,0,1,0xaa] 0 =
    some (.Ok (expected .Case3Extended 7 1 .None 8)) := by decide

theorem case4_extended_zero : smartcard_sapdu__decode #[0x80,0xca,1,2,0,0,1,0xaa,0,0] 0 =
    some (.Ok (expected .Case4Extended 7 1 (.Some 65536) 10)) := by decide

theorem too_long : smartcard_sapdu__decode (Array.replicate 65545 (0 : UInt8)) 0 =
    some (.Err .TooLong) := by
  apply APDUParserRefinement.decode_too_long_raw
  · simp
  · simp

theorem truncated_header : smartcard_sapdu__decode #[0x80,0xca,1] 0 =
    some (.Err .TruncatedHeader) := by decide

theorem truncated_extended_length : smartcard_sapdu__decode #[0x80,0xca,1,2,0,0] 0 =
    some (.Err .TruncatedLength) := by decide

theorem zero_data_length : smartcard_sapdu__decode #[0x80,0xca,1,2,0,0,0,0xaa] 0 =
    some (.Err .ZeroDataLength) := by decide

theorem truncated_short_data : smartcard_sapdu__decode #[0x80,0xca,1,2,2,0xaa] 0 =
    some (.Err .TruncatedData) := by decide

theorem trailing_short : smartcard_sapdu__decode #[0x80,0xca,1,2,1,0xaa,1,2] 0 =
    some (.Err .TrailingBytes) := by decide

theorem one_trailing_extended : smartcard_sapdu__decode #[0x80,0xca,1,2,0,0,1,0xaa,1] 0 =
    some (.Err .TruncatedLength) := by decide

theorem truncated_extended_data : smartcard_sapdu__decode #[0x80,0xca,1,2,0,0,2,0xaa] 0 =
    some (.Err .TruncatedData) := by decide

theorem trailing_extended : smartcard_sapdu__decode #[0x80,0xca,1,2,0,0,1,0xaa,1,2,3] 0 =
    some (.Err .TrailingBytes) := by decide

theorem case2_short_max : smartcard_sapdu__decode #[0x80,0xca,1,2,255] 17 =
    some (.Ok (expected .Case2Short 5 0 (.Some 255) 5)) := by decide

theorem case2_extended_max : smartcard_sapdu__decode #[0x80,0xca,1,2,0,255,255] 17 =
    some (.Ok (expected .Case2Extended 7 0 (.Some 65535) 7)) := by decide


theorem case2_extended_asymmetric : smartcard_sapdu__decode #[0x80,0xca,1,2,0,1,2] 0 =
    some (.Ok (expected .Case2Extended 7 0 (.Some 258) 7)) := by decide

theorem case4_extended_asymmetric : smartcard_sapdu__decode #[0x80,0xca,1,2,0,0,1,0xaa,1,2] 0 =
    some (.Ok (expected .Case4Extended 7 1 (.Some 258) 10)) := by decide

end Oak.Stdlib.APDUParserControls
