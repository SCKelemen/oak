import Oak.Stdlib.APDUParserHelperProofs
import Oak.Stdlib.APDUModelErrorContracts

/-! Uncompiled composition draft over the exact generated parser. The two helper
contracts are proved separately, not assumed axioms. Final compilation requires
the completed helper source and independently reviewed declaration inventory. -/
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
namespace Oak.Stdlib.APDUParserCorrectness
open APDUExtracted APDUParserRefinement APDUParserHelperProofs

def sourceHeader (src : Array UInt8) : smartcard_sapdu__Header :=
  ⟨src.getD 0 0, src.getD 1 0, src.getD 2 0, src.getD 3 0⟩

theorem sourceHeader_observation (src : Array UInt8) :
    liftHeader (sourceHeader src) = headerOf (sourceBytes src) := by
  simp [sourceHeader, liftHeader, headerOf]

theorem sourceHeader_checked (src : Array UInt8) (h : 4 ≤ src.size) :
    sourceHeader src =
      ⟨src[0]'(by omega), src[1]'(by omega), src[2]'(by omega), src[3]'(by omega)⟩ := by
  simp [sourceHeader, BoundedReaderRefinement.getD_checked src 0 0 (by omega),
    BoundedReaderRefinement.getD_checked src 1 0 (by omega),
    BoundedReaderRefinement.getD_checked src 2 0 (by omega),
    BoundedReaderRefinement.getD_checked src 3 0 (by omega)]

-- The representability premise is intentionally not a successful-frame bound:
-- arrays longer than 65544 remain in the theorem's rejection domain.
theorem decode_eq (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    Option.map liftResult (smartcard_sapdu__decode src fuel) =
      some (fullSpec (sourceBytes src)) := by
  have hn := BoundedReaderRefinement.size_toNat src hSize
  by_cases hLong : 65544 < src.size
  · rw [decode_too_long_raw src fuel hSize hLong]
    simp [liftResult, liftError, fullSpec, APDUModel.decodeBytes, APDUModel.decode,
      APDUModel.observe, sourceBytes_length, hLong]
  · by_cases hShort : src.size < 4
    · rw [decode_short_header_raw src fuel hSize hShort]
      simp [liftResult, liftError, fullSpec, APDUModel.decodeBytes, APDUModel.decode,
        APDUModel.observe, sourceBytes_length, hLong, hShort]
    · have hg : ¬ src.size.toUInt32 > (65544 : UInt32) := by
        intro h
        have hNat : 65544 < src.size := by
          simpa [hn] using (UInt32.lt_iff_toNat_lt.mp h)
        exact hLong hNat
      have hs : ¬ src.size.toUInt32 < (4 : UInt32) := by
        intro h
        have hNat : src.size < 4 := by
          simpa [hn] using (UInt32.lt_iff_toNat_lt.mp h)
        exact hShort hNat
      have h4 : (src.size.toUInt32 == (4 : UInt32)) = decide (src.size = 4) := by
        rw [u32_beq_nat, hn]
        rfl
      have h5 : (src.size.toUInt32 == (5 : UInt32)) = decide (src.size = 5) := by
        rw [u32_beq_nat, hn]
        rfl
      by_cases hn4 : src.size = 4
      · simp [smartcard_sapdu__decode, hn4, smartcard_sapdu__command,
          liftResult, liftCommand, liftCase, liftResponse, fullSpec,
          APDUModel.decodeBytes, APDUModel.decode, APDUModel.observe, APDUModel.layout,
          headerOf, source_byteAt]
      · have hEntry : 5 ≤ src.size := by omega
        have hr := read_u8_source_good src 4 fuel hSize (by omega)
        by_cases hn5 : src.size = 5
        · simp [sourceWindow, hn5] at hr
          have hb := APDUModel.short_response_bounds (liftByte (src.getD 4 0))
          simp [hn5] at hb
          simp [smartcard_sapdu__decode, hn5, hr, short_response_raw, smartcard_sapdu__command,
            liftResult, liftCommand, liftCase, liftResponse, fullSpec,
            APDUModel.decodeBytes, APDUModel.decode, APDUModel.observe, APDUModel.layout,
            headerOf, source_byteAt] <;> omega
        · by_cases hz : src.getD 4 0 = (0 : UInt8)
          · have hm : (sourceInput src).first.val = 0 := by
              simp [sourceInput_first, liftByte, hz]
            have hModel : fullSpec (sourceBytes src) =
                attachHeader (liftHeader (sourceHeader src)) (extendedSpec (sourceInput src)) := by
              rw [sourceHeader_observation]
              change attachHeader (headerOf (sourceBytes src)) (APDUModel.decode (sourceInput src)) =
                attachHeader (headerOf (sourceBytes src)) (extendedSpec (sourceInput src))
              apply congrArg (attachHeader (headerOf (sourceBytes src)))
              simp only [APDUModel.decode, sourceInput_n, if_neg hLong, if_neg hShort,
                if_neg hn4, if_neg hn5, if_pos hm, extendedSpec]
            have hz' := hz
            simp only [Array.getD_eq_getD_getElem?] at hz'
            have hRaw : smartcard_sapdu__decode src fuel =
                smartcard_sapdu__extended (sourceHeader src) (sourceWindow src 5) src fuel := by
              simp [smartcard_sapdu__decode, hg, hs, h4, h5, hn4, hn5,
                show ({ next := 4, end_ := src.size.toUInt32 } : encoding_sreader__Window) = sourceWindow src 4 from rfl,
                hr, hz', sourceHeader]
            rw [hRaw, hModel]
            exact extended_eq src (sourceHeader src) fuel hSize hEntry
          · have hm : (sourceInput src).first.val ≠ 0 := by
              simpa [sourceInput_first, liftByte, ← u8_zero_iff] using hz
            have hc : (src.getD 4 0).toUInt32.toNat = (sourceInput src).first.val := by
              simp [sourceInput_first, liftByte, UInt8.toNat_toUInt32]
            have hModel : fullSpec (sourceBytes src) =
                attachHeader (liftHeader (sourceHeader src)) (APDUModel.shortData (sourceInput src)) := by
              rw [sourceHeader_observation]
              change attachHeader (headerOf (sourceBytes src)) (APDUModel.decode (sourceInput src)) =
                attachHeader (headerOf (sourceBytes src)) (APDUModel.shortData (sourceInput src))
              apply congrArg (attachHeader (headerOf (sourceBytes src)))
              simp only [APDUModel.decode, sourceInput_n, if_neg hLong, if_neg hShort,
                if_neg hn4, if_neg hn5, if_neg hm]
            have hz' := hz
            simp only [Array.getD_eq_getD_getElem?] at hz'
            have hRaw : smartcard_sapdu__decode src fuel =
                smartcard_sapdu__short_udata (sourceHeader src) (sourceWindow src 5) src
                  (src.getD 4 0).toUInt32 fuel := by
              simp [smartcard_sapdu__decode, hg, hs, h4, h5, hn4, hn5,
                show ({ next := 4, end_ := src.size.toUInt32 } : encoding_sreader__Window) = sourceWindow src 4 from rfl,
                hr, hz', sourceHeader]
            rw [hRaw, hModel]
            exact short_data_eq src (sourceHeader src) (src.getD 4 0).toUInt32 fuel hSize hEntry hc

theorem decode_total (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32) :
    smartcard_sapdu__decode src fuel ≠ none := by
  intro h
  have he := decode_eq src fuel hSize
  simp [h] at he

theorem decode_result_iff (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (r : Result_smartcard_sapdu__Command_smartcard_sapdu__Error) :
    smartcard_sapdu__decode src fuel = some r ↔ fullSpec (sourceBytes src) = liftResult r := by
  rw [BoundedReaderRefinement.optionMap_reflect liftResult liftResult_injective,
    decode_eq src fuel hSize, Option.some.injEq]

theorem decode_fuel_independent (src : Array UInt8) (a b : Nat) (hSize : src.size < 2 ^ 32) :
    smartcard_sapdu__decode src a = smartcard_sapdu__decode src b := by
  apply BoundedReaderRefinement.optionMap_injective liftResult liftResult_injective
  rw [decode_eq src a hSize, decode_eq src b hSize]

theorem fullSpec_error_iff (src : List APDUModel.Byte) (e : APDUModel.Error) :
    fullSpec src = .error e ↔ APDUModel.decodeBytes src = .error e := by
  unfold fullSpec
  cases APDUModel.decodeBytes src <;> simp

theorem decode_error_iff (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (e : smartcard_sapdu__Error) :
    smartcard_sapdu__decode src fuel = some (.Err e) ↔
      APDUModelErrorContracts.ErrorPredicate (sourceInput src) (liftError e) := by
  rw [decode_result_iff src fuel hSize]
  change fullSpec (sourceBytes src) = .error (liftError e) ↔ _
  rw [fullSpec_error_iff]
  exact APDUModelErrorContracts.decode_error_iff (sourceInput src) (liftError e)

theorem decode_form_iff (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (k : APDUModel.CommandCase) :
    (∃ c, smartcard_sapdu__decode src fuel = some (.Ok c) ∧
      liftCommand c = ⟨headerOf (sourceBytes src), APDUModel.layout (sourceInput src) k⟩) ↔
      APDUModel.Shape (sourceInput src) k := by
  constructor
  · rintro ⟨c, hc, ho⟩
    have hr := (decode_result_iff src fuel hSize (.Ok c)).mp hc
    change fullSpec (sourceBytes src) = .ok (liftCommand c) at hr
    rw [ho] at hr
    exact (fullSpec_shape_iff (sourceBytes src) k).mp hr
  · intro hk
    have hs := (fullSpec_shape_iff (sourceBytes src) k).mpr hk
    have he := decode_eq src fuel hSize
    rw [hs] at he
    rcases BoundedReaderRefinement.optionMap_some_witness liftResult
      (smartcard_sapdu__decode src fuel) _ he with ⟨r, hr, ho⟩
    cases r with
    | Err e => cases ho
    | Ok c => exact ⟨c, hr, Except.ok.inj ho⟩

theorem decode_success_bounds (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (c : smartcard_sapdu__Command) (hc : smartcard_sapdu__decode src fuel = some (.Ok c)) :
    4 ≤ src.size ∧ src.size ≤ 65544 ∧
    c.data_at.toNat ≤ src.size ∧ c.data_length.toNat ≤ src.size - c.data_at.toNat ∧
    c.data_at.toNat + c.data_length.toNat < 2 ^ 32 ∧ c.consumed.toNat = src.size := by
  have he := (decode_result_iff src fuel hSize (.Ok c)).mp hc
  have hb := fullSpec_success_bounds (sourceBytes src) (liftCommand c) he
  simpa [liftCommand] using hb

theorem decode_header_observation (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (c : smartcard_sapdu__Command) (hc : smartcard_sapdu__decode src fuel = some (.Ok c)) :
    (liftCommand c).header = liftHeader (sourceHeader src) := by
  have he := (decode_result_iff src fuel hSize (.Ok c)).mp hc
  rw [sourceHeader_observation]
  exact fullSpec_success_header (sourceBytes src) (liftCommand c) he

theorem decode_header_preserved (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (c : smartcard_sapdu__Command) (hc : smartcard_sapdu__decode src fuel = some (.Ok c)) :
    c.cla = src.getD 0 0 ∧ c.ins = src.getD 1 0 ∧
    c.p1 = src.getD 2 0 ∧ c.p2 = src.getD 3 0 := by
  have hh := decode_header_observation src fuel hSize c hc
  exact ⟨liftByte_injective (congrArg HeaderObs.cla hh),
    liftByte_injective (congrArg HeaderObs.ins hh),
    liftByte_injective (congrArg HeaderObs.p1 hh),
    liftByte_injective (congrArg HeaderObs.p2 hh)⟩

theorem decode_header_indices_valid (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (c : smartcard_sapdu__Command) (hc : smartcard_sapdu__decode src fuel = some (.Ok c)) :
    0 < src.size ∧ 1 < src.size ∧ 2 < src.size ∧ 3 < src.size := by
  have hb := (decode_success_bounds src fuel hSize c hc).1
  omega

theorem decode_success_response_bounds (src : Array UInt8) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (c : smartcard_sapdu__Command) (hc : smartcard_sapdu__decode src fuel = some (.Ok c))
    (r : UInt32) (hr : c.response_length = .Some r) :
    1 ≤ r.toNat ∧ r.toNat ≤ 65536 := by
  have he := (decode_result_iff src fuel hSize (.Ok c)).mp hc
  have hd := fullSpec_success_lengths (sourceBytes src) (liftCommand c) he
  have hs := APDUModel.decode_sound (sourceInput src) (liftCommand c).lengths hd
  have hresp : (APDUModel.layout (sourceInput src) (liftCommand c).lengths.form).responseLength = some r.toNat := by
    rw [← hs.2]
    simp [liftCommand, liftResponse, hr]
  have hb := APDUModel.layout_response_bounds (sourceInput src) (liftCommand c).lengths.form r.toNat hresp
  exact ⟨hb.1, hb.2.1⟩

end Oak.Stdlib.APDUParserCorrectness
