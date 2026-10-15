import Oak.Stdlib.APDUReaderBridge
import Oak.Stdlib.APDULengthModel

/-! Source-only parser bridge draft. Imports are the accepted generated terms and
unchanged accepted models. The full observation retains all four header bytes.
No parser equality or kernel acceptance is claimed until the remaining obligations
are implemented and the separately authorized Lean/audit gate succeeds. -/
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000

namespace Oak.Stdlib.APDUParserRefinement
open APDUExtracted

def liftByte (v : UInt8) : APDUModel.Byte := ⟨v.toNat, v.toNat_lt⟩
def liftWord (v : UInt16) : APDUModel.Word := ⟨v.toNat, v.toNat_lt⟩
def sourceBytes (src : Array UInt8) : List APDUModel.Byte := src.toList.map liftByte

def liftCase : smartcard_sapdu__CommandCase → APDUModel.CommandCase
  | .Case1 => .case1
  | .Case2Short => .case2Short
  | .Case3Short => .case3Short
  | .Case4Short => .case4Short
  | .Case2Extended => .case2Extended
  | .Case3Extended => .case3Extended
  | .Case4Extended => .case4Extended

def liftError : smartcard_sapdu__Error → APDUModel.Error
  | .TooLong => .tooLong
  | .TruncatedHeader => .truncatedHeader
  | .TruncatedLength => .truncatedLength
  | .ZeroDataLength => .zeroDataLength
  | .TruncatedData => .truncatedData
  | .TrailingBytes => .trailingBytes

-- Option_u32 is the independently authenticated std.oak carrier, not Lean Option.
def liftResponse : Option_u32 → Option Nat
  | .Some v => some v.toNat
  | .None => none

structure HeaderObs where
  cla : APDUModel.Byte
  ins : APDUModel.Byte
  p1 : APDUModel.Byte
  p2 : APDUModel.Byte
  deriving DecidableEq, Repr

structure CommandObs where
  header : HeaderObs
  lengths : APDUModel.Lengths
  deriving DecidableEq, Repr

def liftHeader (h : smartcard_sapdu__Header) : HeaderObs :=
  ⟨liftByte h.cla, liftByte h.ins, liftByte h.p1, liftByte h.p2⟩

def liftCommand (c : smartcard_sapdu__Command) : CommandObs :=
  { header := ⟨liftByte c.cla, liftByte c.ins, liftByte c.p1, liftByte c.p2⟩, lengths := { form := liftCase c.form, dataAt := c.data_at.toNat, dataLength := c.data_length.toNat, responseLength := liftResponse c.response_length, consumed := c.consumed.toNat } }

def liftResult : Result_smartcard_sapdu__Command_smartcard_sapdu__Error →
    Except APDUModel.Error CommandObs
  | .Ok c => .ok (liftCommand c)
  | .Err e => .error (liftError e)

def headerOf (src : List APDUModel.Byte) : HeaderObs :=
  ⟨APDUModel.byteAt src 0, APDUModel.byteAt src 1,
   APDUModel.byteAt src 2, APDUModel.byteAt src 3⟩

-- Only a header wrapper around the unchanged specification. Rejection order,
-- all seven layouts and sentinel lengths remain those of APDUModel.decodeBytes.
def fullSpec (src : List APDUModel.Byte) : Except APDUModel.Error CommandObs :=
  match APDUModel.decodeBytes src with
  | .error e => .error e
  | .ok lengths => .ok ⟨headerOf src, lengths⟩

theorem liftByte_injective : Function.Injective liftByte := by
  intro a b h
  exact BoundedReaderRefinement.u8_toNat_injective (congrArg Fin.val h)

theorem liftWord_injective : Function.Injective liftWord := by
  intro a b h
  exact BoundedReaderRefinement.u16_toNat_injective (congrArg Fin.val h)

theorem liftCase_injective : Function.Injective liftCase := by
  intro a b h
  cases a <;> cases b <;> simp_all [liftCase]

theorem liftError_injective : Function.Injective liftError := by
  intro a b h
  cases a <;> cases b <;> simp_all [liftError]

theorem liftResponse_injective : Function.Injective liftResponse := by
  intro a b h
  cases a with
  | None => cases b <;> simp_all [liftResponse]
  | Some a =>
    cases b with
    | None => cases h
    | Some b => exact congrArg Option_u32.Some (BoundedReaderRefinement.u32_toNat_injective (Option.some.inj h))

theorem command_observation (h : smartcard_sapdu__Header)
    (form : smartcard_sapdu__CommandCase) (at_ count consumed : UInt32)
    (response : Option_u32) (fuel : Nat) :
    Option.map liftCommand (smartcard_sapdu__command h form at_ count response consumed fuel) =
      some { header := liftHeader h, lengths := { form := liftCase form, dataAt := at_.toNat, dataLength := count.toNat, responseLength := liftResponse response, consumed := consumed.toNat } } := by
  rfl

theorem command_header_preserved (h : smartcard_sapdu__Header)
    (form : smartcard_sapdu__CommandCase) (at_ count consumed : UInt32)
    (response : Option_u32) (fuel : Nat) :
    Option.map (fun c => (c.cla, c.ins, c.p1, c.p2))
      (smartcard_sapdu__command h form at_ count response consumed fuel) =
      some (h.cla, h.ins, h.p1, h.p2) := by
  rfl

theorem fullSpec_success_header (src : List APDUModel.Byte) (c : CommandObs)
    (h : fullSpec src = .ok c) : c.header = headerOf src := by
  unfold fullSpec at h
  split at h
  · cases h
  · cases h
    rfl

theorem liftCommand_injective : Function.Injective liftCommand := by
  intro a b h
  have hcla := liftByte_injective (congrArg (fun c : CommandObs => c.header.cla) h)
  have hins := liftByte_injective (congrArg (fun c : CommandObs => c.header.ins) h)
  have hp1 := liftByte_injective (congrArg (fun c : CommandObs => c.header.p1) h)
  have hp2 := liftByte_injective (congrArg (fun c : CommandObs => c.header.p2) h)
  have hf := liftCase_injective (congrArg (fun c : CommandObs => c.lengths.form) h)
  have ha := BoundedReaderRefinement.u32_toNat_injective (congrArg (fun c : CommandObs => c.lengths.dataAt) h)
  have hl := BoundedReaderRefinement.u32_toNat_injective (congrArg (fun c : CommandObs => c.lengths.dataLength) h)
  have hr := liftResponse_injective (congrArg (fun c : CommandObs => c.lengths.responseLength) h)
  have hn := BoundedReaderRefinement.u32_toNat_injective (congrArg (fun c : CommandObs => c.lengths.consumed) h)
  cases a
  cases b
  simp only at hcla hins hp1 hp2 hf ha hl hr hn
  cases hcla
  cases hins
  cases hp1
  cases hp2
  cases hf
  cases ha
  cases hl
  cases hr
  cases hn
  rfl

theorem liftResult_injective : Function.Injective liftResult := by
  intro a b h
  cases a with
  | Ok a =>
    cases b with
    | Ok b => exact congrArg Result_smartcard_sapdu__Command_smartcard_sapdu__Error.Ok (liftCommand_injective (Except.ok.inj h))
    | Err b => cases h
  | Err a =>
    cases b with
    | Ok b => cases h
    | Err b => exact congrArg Result_smartcard_sapdu__Command_smartcard_sapdu__Error.Err (liftError_injective (Except.error.inj h))

theorem fullSpec_success_lengths (src : List APDUModel.Byte) (c : CommandObs)
    (h : fullSpec src = .ok c) : APDUModel.decodeBytes src = .ok c.lengths := by
  unfold fullSpec at h
  split at h
  · cases h
  · rename_i lengths he
    cases h
    exact he

theorem fullSpec_shape_iff (src : List APDUModel.Byte) (k : APDUModel.CommandCase) :
    fullSpec src = .ok ⟨headerOf src, APDUModel.layout (APDUModel.observe src) k⟩ ↔
      APDUModel.Shape (APDUModel.observe src) k := by
  constructor
  · intro h
    exact (APDUModel.decode_success_iff (APDUModel.observe src) k).mp
      (fullSpec_success_lengths src _ h)
  · intro h
    have hd := (APDUModel.decode_success_iff (APDUModel.observe src) k).mpr h
    simp [fullSpec, APDUModel.decodeBytes, hd]

theorem fullSpec_success_bounds (src : List APDUModel.Byte) (c : CommandObs)
    (h : fullSpec src = .ok c) :
    4 ≤ src.length ∧ src.length ≤ 65544 ∧
    c.lengths.dataAt ≤ src.length ∧
    c.lengths.dataLength ≤ src.length - c.lengths.dataAt ∧
    c.lengths.dataAt + c.lengths.dataLength < 2 ^ 32 ∧
    c.lengths.consumed = src.length := by
  have hd := fullSpec_success_lengths src c h
  have hs := APDUModel.decode_sound (APDUModel.observe src) c.lengths hd
  have hf := APDUModel.shape_frame_bound (APDUModel.observe src) c.lengths.form hs.1
  have hb := APDUModel.decode_payload_safe (APDUModel.observe src) c.lengths hd
  exact ⟨hf.1, hf.2, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩

-- Early rejection is shown directly at the actual generated root, before any
-- header/tail terms need to be evaluated.
theorem decode_too_long_raw (src : Array UInt8) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hLong : 65544 < src.size) :
    smartcard_sapdu__decode src fuel = some (.Err .TooLong) := by
  have hg : src.size.toUInt32 > (65544 : UInt32) := by
    apply UInt32.lt_iff_toNat_lt.mpr
    simpa [BoundedReaderRefinement.size_toNat src hSize] using hLong
  simp [smartcard_sapdu__decode, hg]

theorem decode_short_header_raw (src : Array UInt8) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hShort : src.size < 4) :
    smartcard_sapdu__decode src fuel = some (.Err .TruncatedHeader) := by
  have hg : ¬ src.size.toUInt32 > (65544 : UInt32) := by
    intro h
    have hNat : 65544 < src.size := by
      simpa [BoundedReaderRefinement.size_toNat src hSize] using
        (UInt32.lt_iff_toNat_lt.mp h)
    omega
  have hs : src.size.toUInt32 < (4 : UInt32) := by
    apply UInt32.lt_iff_toNat_lt.mpr
    simpa [BoundedReaderRefinement.size_toNat src hSize] using hShort
  simp [smartcard_sapdu__decode, hg, hs]

end Oak.Stdlib.APDUParserRefinement
