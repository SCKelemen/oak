import OakSailBridge.BitwiseExecution
/-! Actual Sail decoding of the seven non-bitwise instructions in the36-byte
production wrapper. Memory execution is deliberately not inferred from these
decoding theorems. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem decode_allocate : encdec_backwards 0xfa010113 = decoderChecks (.ITYPE (0xfa0, .Regidx 2, .Regidx 2, .ADDI)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches, encdec_iop_backwards,
    encdec_uop_backwards_matches, width_enc_backwards_matches, width_enc_backwards,
    bool_bit_backwards_matches, bool_bit_backwards, valid_load_encdec, Functions.xlen_bytes,
    Sail.BitVec.extractLsb, Functions.base_E_enabled, Functions.regidx_bit_width,
    Functions.xlen, Functions.not]

theorem decode_save_s1 : encdec_backwards 0x00913023 = decoderChecks (.STORE (0, .Regidx 9, .Regidx 2, 8)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches, encdec_iop_backwards,
    encdec_uop_backwards_matches, width_enc_backwards_matches, width_enc_backwards,
    bool_bit_backwards_matches, bool_bit_backwards, valid_load_encdec, Functions.xlen_bytes,
    Sail.BitVec.extractLsb, Functions.base_E_enabled, Functions.regidx_bit_width,
    Functions.xlen, Functions.not]

theorem decode_save_s2 : encdec_backwards 0x01213423 = decoderChecks (.STORE (8, .Regidx 18, .Regidx 2, 8)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches, encdec_iop_backwards,
    encdec_uop_backwards_matches, width_enc_backwards_matches, width_enc_backwards,
    bool_bit_backwards_matches, bool_bit_backwards, valid_load_encdec, Functions.xlen_bytes,
    Sail.BitVec.extractLsb, Functions.base_E_enabled, Functions.regidx_bit_width,
    Functions.xlen, Functions.not]

theorem decode_copy_right : encdec_backwards 0x00058913 = decoderChecks (.ITYPE (0, .Regidx 11, .Regidx 18, .ADDI)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches, encdec_iop_backwards,
    encdec_uop_backwards_matches, width_enc_backwards_matches, width_enc_backwards,
    bool_bit_backwards_matches, bool_bit_backwards, valid_load_encdec, Functions.xlen_bytes,
    Sail.BitVec.extractLsb, Functions.base_E_enabled, Functions.regidx_bit_width,
    Functions.xlen, Functions.not]

theorem decode_restore_s1 : encdec_backwards 0x00013483 = decoderChecks (.LOAD (0, .Regidx 2, .Regidx 9, false, 8)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches, encdec_iop_backwards,
    encdec_uop_backwards_matches, width_enc_backwards_matches, width_enc_backwards,
    bool_bit_backwards_matches, bool_bit_backwards, valid_load_encdec, Functions.xlen_bytes,
    Sail.BitVec.extractLsb, Functions.base_E_enabled, Functions.regidx_bit_width,
    Functions.xlen, Functions.not]

theorem decode_restore_s2 : encdec_backwards 0x00813903 = decoderChecks (.LOAD (8, .Regidx 2, .Regidx 18, false, 8)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches, encdec_iop_backwards,
    encdec_uop_backwards_matches, width_enc_backwards_matches, width_enc_backwards,
    bool_bit_backwards_matches, bool_bit_backwards, valid_load_encdec, Functions.xlen_bytes,
    Sail.BitVec.extractLsb, Functions.base_E_enabled, Functions.regidx_bit_width,
    Functions.xlen, Functions.not]

theorem decode_release_sp : encdec_backwards 0x06010113 = decoderChecks (.ITYPE (96, .Regidx 2, .Regidx 2, .ADDI)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches, encdec_iop_backwards,
    encdec_uop_backwards_matches, width_enc_backwards_matches, width_enc_backwards,
    bool_bit_backwards_matches, bool_bit_backwards, valid_load_encdec, Functions.xlen_bytes,
    Sail.BitVec.extractLsb, Functions.base_E_enabled, Functions.regidx_bit_width,
    Functions.xlen, Functions.not]

def framedWords (word : BitVec 32) : List (BitVec 32) :=
  [0xfa010113,0x00913023,0x01213423,0x00058913,word,
   0x00013483,0x00813903,0x06010113,0x00008067]

def framedInstructions (op : rop) : List instruction :=
  [.ITYPE (0xfa0, .Regidx 2, .Regidx 2, .ADDI),
   .STORE (0, .Regidx 9, .Regidx 2, 8),
   .STORE (8, .Regidx 18, .Regidx 2, 8),
   .ITYPE (0, .Regidx 11, .Regidx 18, .ADDI),
   .RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, op),
   .LOAD (0, .Regidx 2, .Regidx 9, false, 8),
   .LOAD (8, .Regidx 2, .Regidx 18, false, 8),
   .ITYPE (96, .Regidx 2, .Regidx 2, .ADDI),
   .JALR (0, .Regidx 1, .Regidx 0)]

def decodeWords : List (BitVec 32) → SailM (List instruction)
  | [] => pure []
  | word :: rest => do
      let i ← encdec_backwards word
      let tail ← decodeWords rest
      pure (i :: tail)

/-- Every instruction of the real wrapper decodes in the unchanged external
model. This does not imply execution of the loads/stores matches flat memory. -/
theorem framed_decode (s : State) (hc : ConfigOK s) (word : BitVec 32) (op : rop)
    (hop : encdec_backwards word = decoderChecks (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, op))) :
    (decodeWords (framedWords word)).run s = .ok (framedInstructions op) s := by
  simp only [framedWords, decodeWords, decode_allocate, decode_save_s1, decode_save_s2,
    decode_copy_right, hop, decode_restore_s1, decode_restore_s2, decode_release_sp, decode_ret,
    pure_bind, bind_assoc]
  repeat rw [bind_run_ok _ _ (decoderChecks_run s _ hc)]
  rfl
end OakSailBridge.BitwiseDecoded
