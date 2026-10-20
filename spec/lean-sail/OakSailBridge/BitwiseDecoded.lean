import LeanRV64D.InstsEnd

/-!
Concrete pinned Sail decoder and execution projections. This is deliberately
separate from fetch, physical memory, platform initialization, and source
parsing. No copied decoder or assumed decoder/execute equality is used.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

abbrev State := SequentialState RegisterType trivialChoiceSource

def setRegister (s : State) (r : Register) (v : RegisterType r) : State :=
  { s with regs := s.regs.insert r v }

theorem read_register (s : State) (r : Register) (v : RegisterType r)
    (h : s.regs.get? r = some v) : (readReg r : SailM (RegisterType r)).run s = .ok v s := by
  simp only [PreSail.readReg, EStateM.run, Bind.bind, MonadState.get, getThe, MonadStateOf.get,
    EStateM.bind, EStateM.get, h, Pure.pure, EStateM.pure]

theorem write_register (s : State) (r : Register) (v : RegisterType r) :
    (writeReg r v : SailM PUnit).run s = .ok () (setRegister s r v) := by rfl

theorem read_x10 : rX_bits (.Regidx 10) = readReg Register.x10 := by
  simp [rX_bits, rX, Sail.BitVec.toNatInt, regval_from_reg]

theorem read_x11 : rX_bits (.Regidx 11) = readReg Register.x11 := by
  simp [rX_bits, rX, Sail.BitVec.toNatInt, regval_from_reg]

theorem write_x10 (v : BitVec 64) : wX_bits (.Regidx 10) v = writeReg Register.x10 v := by rfl

theorem write_x0 (v : BitVec 64) : wX_bits (.Regidx 0) v = pure () := by rfl
theorem enabled_lpad_shape : currentlyEnabled .Ext_Zicfilp = (do
    let p ← readReg Register.cur_privilege
    get_xLPE p) := by
  have hand : Bool.and true = id := by funext b; cases b <;> rfl
  simp [currentlyEnabled, hartSupports, hand]

theorem enabled_pause : currentlyEnabled .Ext_Zihintpause = pure true := by
  simp [currentlyEnabled, hartSupports]

theorem enabled_zca_shape : currentlyEnabled .Ext_Zca = (do
    let misa ← readReg Register.misa
    pure (_get_Misa_C misa == 1#1)) := by
  simp [currentlyEnabled, hartSupports, Functions.not, Functions.xlen]

theorem enabled_lpad_run (s : State)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hc : s.regs.get? Register.mseccfg = some (0#64)) :
    (currentlyEnabled .Ext_Zicfilp).run s = .ok false s := by
  rw [enabled_lpad_shape]
  simp only [EStateM.run, Bind.bind, EStateM.bind, PreSail.readReg,
    MonadState.get, getThe, MonadStateOf.get, EStateM.get, hp, Pure.pure, EStateM.pure]
  simp only [get_xLPE, Bind.bind, EStateM.bind, PreSail.readReg,
    MonadState.get, getThe, MonadStateOf.get, EStateM.get, hc, Pure.pure, EStateM.pure]
  rfl

/-- RV64 MXL with base I, compressed instructions disabled. -/
def misaRV64I : BitVec 64 := 0x8000000000000100

theorem enabled_zca_run (s : State) (hm : s.regs.get? Register.misa = some misaRV64I) :
    (currentlyEnabled .Ext_Zca).run s = .ok false s := by
  rw [enabled_zca_shape]
  simp only [EStateM.run, Bind.bind, EStateM.bind, PreSail.readReg,
    MonadState.get, getThe, MonadStateOf.get, EStateM.get, hm, Pure.pure, EStateM.pure]
  rfl

def decoderChecks (instruction : instruction) : SailM LeanRV64D.instruction := do
  let _ ← currentlyEnabled .Ext_Zihintpause
  let _ ← currentlyEnabled .Ext_Zicfilp
  pure instruction

theorem decode_and : encdec_backwards 0x00b57533 =
    decoderChecks (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, .AND)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches,
    encdec_uop_backwards_matches, Sail.BitVec.extractLsb, Functions.base_E_enabled,
    Functions.regidx_bit_width, Functions.not]

theorem decode_or : encdec_backwards 0x00b56533 =
    decoderChecks (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, .OR)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches,
    encdec_uop_backwards_matches, Sail.BitVec.extractLsb, Functions.base_E_enabled,
    Functions.regidx_bit_width, Functions.not]

theorem decode_xor : encdec_backwards 0x00b54533 =
    decoderChecks (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, .XOR)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches,
    encdec_uop_backwards_matches, Sail.BitVec.extractLsb, Functions.base_E_enabled,
    Functions.regidx_bit_width, Functions.not]

theorem decode_ret : encdec_backwards 0x00008067 =
    decoderChecks (.JALR (0, .Regidx 1, .Regidx 0)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches,
    encdec_uop_backwards_matches, Sail.BitVec.extractLsb, Functions.base_E_enabled,
    Functions.regidx_bit_width, Functions.not]

/-- Fail-closed dispatch to the unchanged generated register and return bodies.
No arithmetic or return semantics are copied. Other instruction classes are
rejected rather than introducing unrelated opaque platform primitives. -/
def executeSupported (i : instruction) : SailM ExecutionResult :=
  match i with
  | .RTYPE (rs2, rs1, rd, op) => execute_RTYPE rs2 rs1 rd op
  | .JALR (imm, rs1, rd) => execute_JALR imm rs1 rd
  | _ => EStateM.throw Sail.Error.Unreachable

noncomputable def decoded (word : BitVec 32) : SailM ExecutionResult := do
  let instruction ← encdec_backwards word
  executeSupported instruction

end OakSailBridge.BitwiseDecoded
