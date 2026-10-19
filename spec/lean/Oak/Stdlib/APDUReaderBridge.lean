import Oak.Stdlib.APDUExtracted
import Oak.Stdlib.BoundedReaderRefinement

/-! Uncompiled source draft. The generated modules are imported byte-for-byte.
These conversions preserve machine-width values; they do not reinterpret arrays,
errors, fuel or byte order. No semantic claim is accepted before the Lean gate. -/
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000

namespace Oak.Stdlib.APDUReaderBridge
open APDUExtracted

-- Finite carrier conversion, rather than generated-namespace rewriting.
def toReaderError : encoding_sreader__Error → BoundedReaderExtracted.encoding_sreader__Error
  | .InvalidWindow => .InvalidWindow
  | .InsufficientData => .InsufficientData

def toReaderWindow (s : encoding_sreader__Window) : BoundedReaderExtracted.encoding_sreader__Window :=
  { next := s.next, end_ := s.end_ }

def toReaderRange (p : encoding_sreader__RangeRead) : BoundedReaderExtracted.encoding_sreader__RangeRead :=
  { offset := p.offset, length := p.length, rest := toReaderWindow p.rest }

def toReaderWord (p : encoding_sreader__WordRead) : BoundedReaderExtracted.encoding_sreader__WordRead :=
  { value := p.value, rest := toReaderWindow p.rest }

def toReaderRemainingResult : Result_u32_encoding_sreader__Error → BoundedReaderExtracted.Result_u32_encoding_sreader__Error
  | .Ok n => .Ok n
  | .Err e => .Err (toReaderError e)

def toReaderRangeResult : Result_encoding_sreader__RangeRead_encoding_sreader__Error → BoundedReaderExtracted.Result_encoding_sreader__RangeRead_encoding_sreader__Error
  | .Ok p => .Ok (toReaderRange p)
  | .Err e => .Err (toReaderError e)

def toReaderWordResult : Result_encoding_sreader__WordRead_encoding_sreader__Error → BoundedReaderExtracted.Result_encoding_sreader__WordRead_encoding_sreader__Error
  | .Ok p => .Ok (toReaderWord p)
  | .Err e => .Err (toReaderError e)

def toReaderEndianResult : Result_u16_endian__Error → BoundedReaderExtracted.Result_u16_endian__Error
  | .Ok n => .Ok n
  | .Err .BufferTooSmall => .Err .BufferTooSmall

-- These structural equations need no size hypothesis: both sides use the same
-- UInt32 arithmetic, array and total getD operation. Natural-model transport below
-- adds the explicit representability hypothesis.
theorem range_fits_bridge (length offset width : UInt32) (fuel : Nat) :
    bytes__range_ufits length offset width fuel =
      BoundedReaderExtracted.bytes__range_ufits length offset width fuel := by
  rfl

theorem remaining_bridge (s : encoding_sreader__Window) (src : Array UInt8) (fuel : Nat) :
    Option.map toReaderRemainingResult (encoding_sreader__remaining s src fuel) =
      BoundedReaderExtracted.encoding_sreader__remaining (toReaderWindow s) src fuel := by
  cases hb : (decide (s.next > s.end_) || decide (s.end_ > src.size.toUInt32)) <;>
    simp [encoding_sreader__remaining,
      BoundedReaderExtracted.encoding_sreader__remaining,
      toReaderRemainingResult, toReaderError, toReaderWindow, hb]

theorem take_bridge (s : encoding_sreader__Window) (src : Array UInt8)
    (count : UInt32) (fuel : Nat) :
    Option.map toReaderRangeResult (encoding_sreader__take s src count fuel) =
      BoundedReaderExtracted.encoding_sreader__take (toReaderWindow s) src count fuel := by
  cases hb : (decide (s.next > s.end_) || decide (s.end_ > src.size.toUInt32)) <;>
    by_cases hc : count > s.end_ - s.next <;>
    simp [encoding_sreader__take, encoding_sreader__remaining,
      BoundedReaderExtracted.encoding_sreader__take,
      BoundedReaderExtracted.encoding_sreader__remaining,
      toReaderRangeResult, toReaderRange, toReaderError, toReaderWindow, hb, hc]

theorem endian_be16_bridge (src : Array UInt8) (offset : UInt32) (fuel : Nat) :
    Option.map toReaderEndianResult (endian__read_uu16_ube src offset fuel) =
      BoundedReaderExtracted.endian__read_uu16_ube src offset fuel := by
  cases hp : decide (offset > src.size.toUInt32) <;>
    cases hq : decide ((2 : UInt32) ≤ src.size.toUInt32 - offset) <;>
    simp [endian__read_uu16_ube, bytes__range_ufits,
      BoundedReaderExtracted.endian__read_uu16_ube,
      BoundedReaderExtracted.bytes__range_ufits, toReaderEndianResult, hp, hq]

theorem read_be16_bridge (s : encoding_sreader__Window) (src : Array UInt8) (fuel : Nat) :
    Option.map toReaderWordResult (encoding_sreader__read_uu16_ube s src fuel) =
      BoundedReaderExtracted.encoding_sreader__read_uu16_ube (toReaderWindow s) src fuel := by
  cases hb : (decide (s.next > s.end_) || decide (s.end_ > src.size.toUInt32)) <;>
    by_cases hc : (2 : UInt32) > s.end_ - s.next <;>
    by_cases hp : s.next ≤ src.size.toUInt32 <;>
    by_cases hq : (2 : UInt32) ≤ src.size.toUInt32 - s.next <;>
    simp [encoding_sreader__read_uu16_ube, encoding_sreader__take,
      encoding_sreader__remaining, endian__read_uu16_ube, bytes__range_ufits,
      BoundedReaderExtracted.encoding_sreader__read_uu16_ube,
      BoundedReaderExtracted.encoding_sreader__take,
      BoundedReaderExtracted.encoding_sreader__remaining,
      BoundedReaderExtracted.endian__read_uu16_ube,
      BoundedReaderExtracted.bytes__range_ufits,
      toReaderWordResult, toReaderWord, toReaderWindow, toReaderError, hb, hc, hp, hq]

-- Genuine reuse of accepted reader equations, with representation hypothesis.
theorem remaining_model (s : encoding_sreader__Window) (src : Array UInt8)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    Option.map BoundedReaderRefinement.liftRemainingResult
      (Option.map toReaderRemainingResult (encoding_sreader__remaining s src fuel)) =
      some (ReaderModel.remaining (BoundedReaderRefinement.liftWindow (toReaderWindow s)) src.size) := by
  rw [remaining_bridge]
  exact BoundedReaderRefinement.remaining_eq src (toReaderWindow s) fuel hSize

theorem take_model (s : encoding_sreader__Window) (src : Array UInt8)
    (count : UInt32) (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    Option.map BoundedReaderRefinement.liftRangeResult
      (Option.map toReaderRangeResult (encoding_sreader__take s src count fuel)) =
      some (ReaderModel.take (BoundedReaderRefinement.liftWindow (toReaderWindow s)) src.size count.toNat) := by
  rw [take_bridge]
  exact BoundedReaderRefinement.take_eq src (toReaderWindow s) count fuel hSize

theorem read_be16_model (s : encoding_sreader__Window) (src : Array UInt8)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    Option.map BoundedReaderRefinement.liftWordResult
      (Option.map toReaderWordResult (encoding_sreader__read_uu16_ube s src fuel)) =
      some (BoundedReaderRefinement.wordSpec src
        (BoundedReaderRefinement.liftWindow (toReaderWindow s))) := by
  rw [read_be16_bridge]
  exact BoundedReaderRefinement.read_eq src (toReaderWindow s) fuel hSize

-- read_u8 was not among the previous reader extraction roots. Its exact generated
-- equation is proved here from the actual take result; it is not claimed as old credit.
theorem read_u8_from_take (s : encoding_sreader__Window) (src : Array UInt8)
    (fuel : Nat) (p : encoding_sreader__RangeRead)
    (h : encoding_sreader__take s src 1 fuel = some (.Ok p)) :
    encoding_sreader__read_uu8 s src fuel =
      some (.Ok { value := src.getD p.offset.toNat 0, rest := p.rest }) := by
  simp [encoding_sreader__read_uu8, h]

theorem read_u8_error_from_take (s : encoding_sreader__Window) (src : Array UInt8)
    (fuel : Nat) (e : encoding_sreader__Error)
    (h : encoding_sreader__take s src 1 fuel = some (.Err e)) :
    encoding_sreader__read_uu8 s src fuel = some (.Err e) := by
  simp [encoding_sreader__read_uu8, h]

theorem read_u8_index_valid (s : encoding_sreader__Window) (src : Array UInt8)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) (p : encoding_sreader__RangeRead)
    (h : encoding_sreader__take s src 1 fuel = some (.Ok p)) :
    p.offset.toNat < src.size := by
  have hr : BoundedReaderExtracted.encoding_sreader__take (toReaderWindow s) src 1 fuel =
      some (.Ok (toReaderRange p)) := by
    have hb := take_bridge s src 1 fuel
    rw [h] at hb
    exact hb.symm
  have hb := BoundedReaderRefinement.take_success_bounds src (toReaderWindow s) 1 fuel
    hSize (toReaderRange p) hr
  have hl : p.length.toNat = 1 := by simpa [toReaderRange] using hb.2.1
  have he : p.offset.toNat + p.length.toNat ≤ src.size := by
    simpa [toReaderRange] using hb.2.2.2.2.2.2.1
  omega

-- Structural positive and precedence controls. These are proof terms, not executed tests.
theorem read_u8_zero_fuel :
    encoding_sreader__read_uu8 { next := 0, end_ := 1 } #[0x7f] 0 =
      some (.Ok { value := 0x7f, rest := { next := 1, end_ := 1 } }) := by
  decide

theorem read_u8_invalid_precedes_short :
    encoding_sreader__read_uu8 { next := 2, end_ := 1 } #[0x7f] 0 =
      some (.Err .InvalidWindow) := by
  decide

theorem read_u8_empty_window :
    encoding_sreader__read_uu8 { next := 1, end_ := 1 } #[0x7f] 0 =
      some (.Err .InsufficientData) := by
  decide

-- Injectivity prevents carrier transport from concealing distinct outcomes.
theorem toReaderError_injective : Function.Injective toReaderError := by
  intro a b h
  cases a <;> cases b <;> simp_all [toReaderError]

theorem toReaderWindow_injective : Function.Injective toReaderWindow := by
  intro a b h
  cases a with | mk an ae =>
    cases b with | mk bn be =>
      have hn := congrArg BoundedReaderExtracted.encoding_sreader__Window.next h
      have he := congrArg BoundedReaderExtracted.encoding_sreader__Window.end_ h
      simp only [toReaderWindow] at hn he
      cases hn
      cases he
      rfl

theorem toReaderRange_injective : Function.Injective toReaderRange := by
  intro a b h
  cases a with | mk ao al ar =>
    cases b with | mk bo bl br =>
      have ho := congrArg BoundedReaderExtracted.encoding_sreader__RangeRead.offset h
      have hl := congrArg BoundedReaderExtracted.encoding_sreader__RangeRead.length h
      have hr := congrArg BoundedReaderExtracted.encoding_sreader__RangeRead.rest h
      simp only [toReaderRange] at ho hl hr
      have he := toReaderWindow_injective hr
      cases ho
      cases hl
      cases he
      rfl

theorem toReaderRangeResult_injective : Function.Injective toReaderRangeResult := by
  intro a b h
  cases a with
  | Ok a =>
    cases b with
    | Ok b => exact congrArg Result_encoding_sreader__RangeRead_encoding_sreader__Error.Ok (toReaderRange_injective (BoundedReaderExtracted.Result_encoding_sreader__RangeRead_encoding_sreader__Error.Ok.inj h))
    | Err b => cases h
  | Err a =>
    cases b with
    | Ok b => cases h
    | Err b => exact congrArg Result_encoding_sreader__RangeRead_encoding_sreader__Error.Err (toReaderError_injective (BoundedReaderExtracted.Result_encoding_sreader__RangeRead_encoding_sreader__Error.Err.inj h))

theorem take_invalid_raw (src : Array UInt8) (s : encoding_sreader__Window)
    (count : UInt32) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hv : ¬ ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s))) :
    encoding_sreader__take s src count fuel = some (.Err .InvalidWindow) := by
  apply (BoundedReaderRefinement.optionMap_reflect toReaderRangeResult
    toReaderRangeResult_injective _ _).mpr
  rw [take_bridge]
  exact BoundedReaderRefinement.take_invalid_raw src (toReaderWindow s) count fuel hSize hv

theorem take_short_raw (src : Array UInt8) (s : encoding_sreader__Window)
    (count : UInt32) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hv : ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s)))
    (hc : count.toNat > s.end_.toNat - s.next.toNat) :
    encoding_sreader__take s src count fuel = some (.Err .InsufficientData) := by
  apply (BoundedReaderRefinement.optionMap_reflect toReaderRangeResult
    toReaderRangeResult_injective _ _).mpr
  rw [take_bridge]
  exact BoundedReaderRefinement.take_short_raw src (toReaderWindow s) count fuel hSize hv hc

theorem take_good_raw (src : Array UInt8) (s : encoding_sreader__Window)
    (count : UInt32) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hv : ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s)))
    (hc : count.toNat ≤ s.end_.toNat - s.next.toNat) :
    encoding_sreader__take s src count fuel =
      some (.Ok { offset := s.next, length := count, rest := { next := s.next + count, end_ := s.end_ } }) := by
  apply (BoundedReaderRefinement.optionMap_reflect toReaderRangeResult
    toReaderRangeResult_injective _ _).mpr
  rw [take_bridge]
  exact BoundedReaderRefinement.take_good_raw src (toReaderWindow s) count fuel hSize hv hc

-- This new byte observation shares the reader's natural value/rest carrier.
def liftByteResult : Result_encoding_sreader__ByteRead_encoding_sreader__Error →
    ReaderModel.Result BoundedReaderRefinement.WordObs
  | .Ok b => .Ok { value := b.value.toNat, rest := BoundedReaderRefinement.liftWindow (toReaderWindow b.rest) }
  | .Err e => .Err (BoundedReaderRefinement.liftError (toReaderError e))

-- A specification over the accepted natural take operation, not a copy of the
-- parser or the generated UInt32 implementation. Successful access validity is
-- established separately by read_u8_index_valid.
def byteSpec (src : Array UInt8) (w : ReaderModel.Window) :
    ReaderModel.Result BoundedReaderRefinement.WordObs :=
  match ReaderModel.take w src.size 1 with
  | .Err e => .Err e
  | .Ok p => .Ok { value := (src.getD p.offset 0).toNat, rest := p.rest }

theorem read_u8_model (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    Option.map liftByteResult (encoding_sreader__read_uu8 s src fuel) =
      some (byteSpec src (BoundedReaderRefinement.liftWindow (toReaderWindow s))) := by
  have ht := take_model s src 1 fuel hSize
  cases h : encoding_sreader__take s src 1 fuel with
  | none => simp [h] at ht
  | some r =>
    cases r with
    | Err e =>
      have hm : ReaderModel.take (BoundedReaderRefinement.liftWindow (toReaderWindow s)) src.size 1 =
          .Err (BoundedReaderRefinement.liftError (toReaderError e)) := by
        simpa [h, toReaderRangeResult, BoundedReaderRefinement.liftRangeResult] using ht.symm
      simp [encoding_sreader__read_uu8, h, liftByteResult, byteSpec, hm]
    | Ok p =>
      have hm : ReaderModel.take (BoundedReaderRefinement.liftWindow (toReaderWindow s)) src.size 1 =
          .Ok (BoundedReaderRefinement.liftRange (toReaderRange p)) := by
        simpa [h, toReaderRangeResult, BoundedReaderRefinement.liftRangeResult] using ht.symm
      simp [encoding_sreader__read_uu8, h, liftByteResult, byteSpec, hm,
        BoundedReaderRefinement.liftRange, toReaderRange]

theorem toReaderWord_injective : Function.Injective toReaderWord := by
  intro a b h
  cases a with | mk av ar =>
    cases b with | mk bv br =>
      have hv := congrArg BoundedReaderExtracted.encoding_sreader__WordRead.value h
      have hr := congrArg BoundedReaderExtracted.encoding_sreader__WordRead.rest h
      simp only [toReaderWord] at hv hr
      have he := toReaderWindow_injective hr
      cases hv
      cases he
      rfl

theorem toReaderWordResult_injective : Function.Injective toReaderWordResult := by
  intro a b h
  cases a with
  | Ok a =>
    cases b with
    | Ok b => exact congrArg Result_encoding_sreader__WordRead_encoding_sreader__Error.Ok (toReaderWord_injective (BoundedReaderExtracted.Result_encoding_sreader__WordRead_encoding_sreader__Error.Ok.inj h))
    | Err b => cases h
  | Err a =>
    cases b with
    | Ok b => cases h
    | Err b => exact congrArg Result_encoding_sreader__WordRead_encoding_sreader__Error.Err (toReaderError_injective (BoundedReaderExtracted.Result_encoding_sreader__WordRead_encoding_sreader__Error.Err.inj h))

theorem read_be16_short_raw (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hv : ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s)))
    (hs : s.end_.toNat - s.next.toNat < 2) :
    encoding_sreader__read_uu16_ube s src fuel = some (.Err .InsufficientData) := by
  apply (BoundedReaderRefinement.optionMap_reflect toReaderWordResult
    toReaderWordResult_injective _ _).mpr
  rw [read_be16_bridge]
  exact BoundedReaderRefinement.read_short_raw src (toReaderWindow s) fuel hSize hv hs

theorem read_be16_good_raw (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hg : BoundedReaderRefinement.Good src (BoundedReaderRefinement.liftWindow (toReaderWindow s))) :
    encoding_sreader__read_uu16_ube s src fuel =
      some (.Ok { value := BoundedReaderRefinement.be16ValueExpr (BoundedReaderRefinement.checkedHi src (BoundedReaderRefinement.liftWindow (toReaderWindow s)) hg) (BoundedReaderRefinement.checkedLo src (BoundedReaderRefinement.liftWindow (toReaderWindow s)) hg), rest := { next := s.next + (2 : UInt32), end_ := s.end_ } }) := by
  apply (BoundedReaderRefinement.optionMap_reflect toReaderWordResult
    toReaderWordResult_injective _ _).mpr
  rw [read_be16_bridge]
  exact BoundedReaderRefinement.read_good_raw src (toReaderWindow s) fuel hSize hg

theorem byte_model_index_valid (src : Array UInt8) (w : ReaderModel.Window)
    (p : ReaderModel.RangeRead) (h : ReaderModel.take w src.size 1 = .Ok p) :
    p.offset < src.size := by
  have hb := ReaderModel.take_ok_bounds w src.size 1 p h
  have hl := hb.2.1
  have he := hb.2.2.2.2.2.2.1
  omega

-- The definitive byte specification uses checked indexing, not default reads.
def byteCheckedSpec (src : Array UInt8) (w : ReaderModel.Window) :
    ReaderModel.Result BoundedReaderRefinement.WordObs :=
  match h : ReaderModel.take w src.size 1 with
  | .Err e => .Err e
  | .Ok p => .Ok { value := (src[p.offset]'(byte_model_index_valid src w p h)).toNat, rest := p.rest }

theorem byteSpec_eq_checked (src : Array UInt8) (w : ReaderModel.Window) :
    byteSpec src w = byteCheckedSpec src w := by
  unfold byteCheckedSpec
  split
  · rename_i e h
    simp only [byteSpec, h]
  · rename_i p h
    simp only [byteSpec, h]
    rw [BoundedReaderRefinement.getD_checked src p.offset 0
      (byte_model_index_valid src w p h)]

theorem read_u8_checked_model (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    Option.map liftByteResult (encoding_sreader__read_uu8 s src fuel) =
      some (byteCheckedSpec src (BoundedReaderRefinement.liftWindow (toReaderWindow s))) := by
  rw [read_u8_model src s fuel hSize, byteSpec_eq_checked]

theorem read_u8_checked_success (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) (p : encoding_sreader__RangeRead)
    (h : encoding_sreader__take s src 1 fuel = some (.Ok p)) :
    encoding_sreader__read_uu8 s src fuel =
      some (.Ok { value := src[p.offset.toNat]'(read_u8_index_valid s src fuel hSize p h), rest := p.rest }) := by
  rw [read_u8_from_take s src fuel p h,
    BoundedReaderRefinement.getD_checked src p.offset.toNat 0 (read_u8_index_valid s src fuel hSize p h)]

def liftByte (b : encoding_sreader__ByteRead) : BoundedReaderRefinement.WordObs :=
  { value := b.value.toNat, rest := BoundedReaderRefinement.liftWindow (toReaderWindow b.rest) }

theorem liftByte_injective : Function.Injective liftByte := by
  intro a b h
  cases a with | mk av ar =>
    cases b with | mk bv br =>
      have hv := congrArg BoundedReaderRefinement.WordObs.value h
      have hr := congrArg BoundedReaderRefinement.WordObs.rest h
      simp only [liftByte] at hv hr
      have hv' := BoundedReaderRefinement.u8_toNat_injective hv
      have hr' := toReaderWindow_injective (BoundedReaderRefinement.liftWindow_injective hr)
      cases hv'
      cases hr'
      rfl

theorem liftByteResult_injective : Function.Injective liftByteResult := by
  intro a b h
  cases a with
  | Ok a =>
    cases b with
    | Ok b => exact congrArg Result_encoding_sreader__ByteRead_encoding_sreader__Error.Ok (liftByte_injective (ReaderModel.Result.Ok.inj h))
    | Err b => cases h
  | Err a =>
    cases b with
    | Ok b => cases h
    | Err b => exact congrArg Result_encoding_sreader__ByteRead_encoding_sreader__Error.Err (toReaderError_injective (BoundedReaderRefinement.liftError_injective (ReaderModel.Result.Err.inj h)))

theorem read_u8_result_iff (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (r : Result_encoding_sreader__ByteRead_encoding_sreader__Error) :
    encoding_sreader__read_uu8 s src fuel = some r ↔
      byteCheckedSpec src (BoundedReaderRefinement.liftWindow (toReaderWindow s)) = liftByteResult r := by
  rw [BoundedReaderRefinement.optionMap_reflect liftByteResult liftByteResult_injective,
    read_u8_checked_model src s fuel hSize, Option.some.injEq]

theorem read_u8_total (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    encoding_sreader__read_uu8 s src fuel ≠ none := by
  intro h
  have hm := read_u8_checked_model src s fuel hSize
  simp [h] at hm

theorem read_u8_invalid_raw (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hv : ¬ ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s))) :
    encoding_sreader__read_uu8 s src fuel = some (.Err .InvalidWindow) := by
  exact read_u8_error_from_take s src fuel .InvalidWindow (take_invalid_raw src s 1 fuel hSize hv)

theorem read_u8_short_raw (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hv : ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s)))
    (hc : s.end_.toNat - s.next.toNat < 1) :
    encoding_sreader__read_uu8 s src fuel = some (.Err .InsufficientData) := by
  exact read_u8_error_from_take s src fuel .InsufficientData
    (take_short_raw src s 1 fuel hSize hv (by simpa using hc))

theorem read_u8_good_raw (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hv : ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s)))
    (hc : 1 ≤ s.end_.toNat - s.next.toNat) :
    encoding_sreader__read_uu8 s src fuel =
      some (.Ok { value := src.getD s.next.toNat 0, rest := { next := s.next + (1 : UInt32), end_ := s.end_ } }) := by
  exact read_u8_from_take s src fuel _ (take_good_raw src s 1 fuel hSize hv (by simpa using hc))

theorem read_u8_invalid_iff (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    encoding_sreader__read_uu8 s src fuel = some (.Err .InvalidWindow) ↔
      ¬ ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s)) := by
  by_cases hv : ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s))
  · by_cases hc : 1 ≤ s.end_.toNat - s.next.toNat
    · simp [read_u8_good_raw src s fuel hSize hv hc, hv]
    · have hs : s.end_.toNat - s.next.toNat < 1 := by omega
      simp [read_u8_short_raw src s fuel hSize hv hs, hv]
  · simp [read_u8_invalid_raw src s fuel hSize hv, hv]

theorem read_u8_insufficient_iff (src : Array UInt8) (s : encoding_sreader__Window)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    encoding_sreader__read_uu8 s src fuel = some (.Err .InsufficientData) ↔
      ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s)) ∧
      s.end_.toNat - s.next.toNat < 1 := by
  by_cases hv : ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow (toReaderWindow s))
  · by_cases hc : 1 ≤ s.end_.toNat - s.next.toNat
    · have hn : ¬ s.end_.toNat - s.next.toNat < 1 := by omega
      simp [read_u8_good_raw src s fuel hSize hv hc, hv, hn]
    · have hs : s.end_.toNat - s.next.toNat < 1 := by omega
      simp [read_u8_short_raw src s fuel hSize hv hs, hv, hs]
  · simp [read_u8_invalid_raw src s fuel hSize hv, hv]

end Oak.Stdlib.APDUReaderBridge
