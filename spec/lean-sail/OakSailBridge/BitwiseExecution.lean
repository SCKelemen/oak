import OakSailBridge.BitwiseDecoded
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1
theorem bind_run_ok {α β : Type} (action : SailM α) (next : α → SailM β)
    {s after : State} {value : α} (h : action.run s = .ok value after) :
    (action >>= next).run s = (next value).run after := by
  simp only [EStateM.run, Bind.bind, EStateM.bind] at h ⊢
  rw [h]

def ConfigOK (s : State) : Prop :=
  s.regs.get? Register.cur_privilege = some Privilege.Machine ∧
  s.regs.get? Register.mseccfg = some (0#64) ∧
  s.regs.get? Register.misa = some misaRV64I

theorem decoderChecks_run (s : State) (instruction : instruction) (h : ConfigOK s) :
    (decoderChecks instruction).run s = .ok instruction s := by
  unfold decoderChecks
  rw [enabled_pause]
  simp only [pure_bind]
  exact bind_run_ok _ _ (enabled_lpad_run s h.1 h.2.1)

theorem decode_and_run (s : State) (h : ConfigOK s) :
    (encdec_backwards 0x00b57533).run s =
      .ok (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, .AND)) s := by
  rw [decode_and]
  exact decoderChecks_run s _ h

theorem decode_ret_run (s : State) (h : ConfigOK s) :
    (encdec_backwards 0x00008067).run s = .ok (.JALR (0, .Regidx 1, .Regidx 0)) s := by
  rw [decode_ret]
  exact decoderChecks_run s _ h

theorem execute_and_shape : execute_RTYPE (.Regidx 11) (.Regidx 10) (.Regidx 10) .AND = (do
    let left ← readReg Register.x10
    let right ← readReg Register.x11
    writeReg Register.x10 (left &&& right)
    pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE, pure_bind, bind_assoc, read_x10, read_x11, write_x10]

theorem execute_and_run (s : State) (left right : BitVec 64)
    (hleft : s.regs.get? Register.x10 = some left)
    (hright : s.regs.get? Register.x11 = some right) :
    (execute_RTYPE (.Regidx 11) (.Regidx 10) (.Regidx 10) .AND).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x10 (left &&& right)) := by
  rw [execute_and_shape]
  rw [bind_run_ok _ _ (read_register s Register.x10 left hleft)]
  rw [bind_run_ok _ _ (read_register s Register.x11 right hright)]
  rfl
theorem execute_or_shape : execute_RTYPE (.Regidx 11) (.Regidx 10) (.Regidx 10) .OR = (do
    let left ← readReg Register.x10
    let right ← readReg Register.x11
    writeReg Register.x10 (left ||| right)
    pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE, pure_bind, bind_assoc, read_x10, read_x11, write_x10]

theorem execute_or_run (s : State) (left right : BitVec 64)
    (hleft : s.regs.get? Register.x10 = some left)
    (hright : s.regs.get? Register.x11 = some right) :
    (execute_RTYPE (.Regidx 11) (.Regidx 10) (.Regidx 10) .OR).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x10 (left ||| right)) := by
  rw [execute_or_shape]
  rw [bind_run_ok _ _ (read_register s Register.x10 left hleft)]
  rw [bind_run_ok _ _ (read_register s Register.x11 right hright)]
  rfl

theorem execute_xor_shape : execute_RTYPE (.Regidx 11) (.Regidx 10) (.Regidx 10) .XOR = (do
    let left ← readReg Register.x10
    let right ← readReg Register.x11
    writeReg Register.x10 (left ^^^ right)
    pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE, pure_bind, bind_assoc, read_x10, read_x11, write_x10]

theorem execute_xor_run (s : State) (left right : BitVec 64)
    (hleft : s.regs.get? Register.x10 = some left)
    (hright : s.regs.get? Register.x11 = some right) :
    (execute_RTYPE (.Regidx 11) (.Regidx 10) (.Regidx 10) .XOR).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x10 (left ^^^ right)) := by
  rw [execute_xor_shape]
  rw [bind_run_ok _ _ (read_register s Register.x10 left hleft)]
  rw [bind_run_ok _ _ (read_register s Register.x11 right hright)]
  rfl

theorem jump_run (s : State) (target : BitVec 64)
    (hm : s.regs.get? Register.misa = some misaRV64I)
    (h0 : Sail.BitVec.access target 0 = 0#1)
    (h1 : Sail.BitVec.access target 1 = 0#1) :
    (jump_to target).run s = .ok RETIRE_SUCCESS (setRegister s Register.nextPC target) := by
  unfold jump_to
  simp [ext_control_check_pc, h0, h1, bit_to_bool, bool_bit_backwards,
    LeanRV64D.assert, PreSail.assert]
  have hz := enabled_zca_run s hm
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
    Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    Pure.pure] at hz ⊢
  rw [hz]
  rfl
theorem read_x1 : rX_bits (.Regidx 1) = readReg Register.x1 := by
  simp [rX_bits, rX, Sail.BitVec.toNatInt, regval_from_reg]

theorem update_elp_run (s : State) (h : ConfigOK s) :
    (update_elp_state (.Regidx 1)).run s = .ok () s := by
  unfold update_elp_state
  rw [bind_run_ok _ _ (enabled_lpad_run s h.1 h.2.1)]
  rfl

/-- The return target meets IALIGN=32 after JALR clears bit zero. -/
def ReturnAligned (ra : BitVec 64) : Prop :=
  Sail.BitVec.access (Sail.BitVec.update ra 0 0#1) 0 = 0#1 ∧
  Sail.BitVec.access (Sail.BitVec.update ra 0 0#1) 1 = 0#1

theorem execute_ret_run (s : State) (ra next : BitVec 64)
    (hc : ConfigOK s)
    (hra : s.regs.get? Register.x1 = some ra)
    (hnext : s.regs.get? Register.nextPC = some next)
    (halign : ReturnAligned ra) :
    (execute_JALR 0 (.Regidx 1) (.Regidx 0)).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.nextPC (Sail.BitVec.update ra 0 0#1)) := by
  unfold execute_JALR
  rw [bind_run_ok _ _ (update_elp_run s hc)]
  change ((readReg Register.nextPC) >>= _).run s = _
  rw [bind_run_ok _ _ (read_register s Register.nextPC next hnext)]
  simp only [read_x1, sign_extend, Sail.BitVec.signExtend]
  rw [bind_run_ok _ _ (read_register s Register.x1 ra hra)]
  try simp only [pure_bind]
  have hz : (0 : BitVec 12).signExtend 64 = (0 : BitVec 64) := rfl
  rw [hz]
  rw [show ra + (0 : BitVec 64) = ra from _root_.BitVec.add_zero ra]
  rw [bind_run_ok _ _ (jump_run s _ hc.2.2 halign.1 halign.2)]
  rfl
theorem lookup_set_same (s : State) (r : Register) (v : RegisterType r) :
    (setRegister s r v).regs.get? r = some v := by
  exact Std.ExtDHashMap.get?_insert_self

theorem lookup_set_other (s : State) (r q : Register) (v : RegisterType r)
    (h : r ≠ q) : (setRegister s r v).regs.get? q = s.regs.get? q := by
  simp [setRegister, Std.ExtDHashMap.get?_insert, h]

theorem config_set_x10 (s : State) (v : BitVec 64) (h : ConfigOK s) :
    ConfigOK (setRegister s Register.x10 v) := by
  simpa [ConfigOK, setRegister, Std.ExtDHashMap.get?_insert] using h

theorem decoded_ret_run (s : State) (ra next : BitVec 64) (hc : ConfigOK s)
    (hra : s.regs.get? Register.x1 = some ra)
    (hnext : s.regs.get? Register.nextPC = some next) (ha : ReturnAligned ra) :
    (decoded 0x00008067).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.nextPC (Sail.BitVec.update ra 0 0#1)) := by
  unfold decoded
  rw [bind_run_ok _ _ (decode_ret_run s hc)]
  exact execute_ret_run s ra next hc hra hnext ha

/-- Driver for supplied instruction bodies, not the generated fetch/step loop.
PC is deliberately not ticked here; RET writes nextPC. -/
def bodies (first second : BitVec 32) : SailM ExecutionResult := do
  let result ← decoded first
  match result with
  | .Retire_Success () => decoded second
  | other => pure other

theorem decoded_and_run (s : State) (left right : BitVec 64) (hc : ConfigOK s)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right) :
    (decoded 0x00b57533).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x10 (left &&& right)) := by
  have hd : (encdec_backwards 0x00b57533).run s =
      .ok (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, .AND)) s := by
    rw [decode_and]
    exact decoderChecks_run s _ hc
  unfold decoded
  rw [bind_run_ok _ _ hd]
  exact execute_and_run s left right hl hr

theorem and_return (s : State) (left right ra next : BitVec 64) (hc : ConfigOK s)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right)
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (ha : ReturnAligned ra) :
    (bodies 0x00b57533 0x00008067).run s = .ok RETIRE_SUCCESS
      (setRegister (setRegister s Register.x10 (left &&& right)) Register.nextPC
        (Sail.BitVec.update ra 0 0#1)) := by
  unfold bodies
  rw [bind_run_ok _ _ (decoded_and_run s left right hc hl hr)]
  apply decoded_ret_run _ ra next (config_set_x10 s _ hc)
  · rw [lookup_set_other _ _ _ _ (by decide)]
    exact hra
  · rw [lookup_set_other _ _ _ _ (by decide)]
    exact hn
  · exact ha

theorem decoded_or_run (s : State) (left right : BitVec 64) (hc : ConfigOK s)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right) :
    (decoded 0x00b56533).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x10 (left ||| right)) := by
  have hd : (encdec_backwards 0x00b56533).run s =
      .ok (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, .OR)) s := by
    rw [decode_or]
    exact decoderChecks_run s _ hc
  unfold decoded
  rw [bind_run_ok _ _ hd]
  exact execute_or_run s left right hl hr

theorem or_return (s : State) (left right ra next : BitVec 64) (hc : ConfigOK s)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right)
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (ha : ReturnAligned ra) :
    (bodies 0x00b56533 0x00008067).run s = .ok RETIRE_SUCCESS
      (setRegister (setRegister s Register.x10 (left ||| right)) Register.nextPC
        (Sail.BitVec.update ra 0 0#1)) := by
  unfold bodies
  rw [bind_run_ok _ _ (decoded_or_run s left right hc hl hr)]
  apply decoded_ret_run _ ra next (config_set_x10 s _ hc)
  · rw [lookup_set_other _ _ _ _ (by decide)]
    exact hra
  · rw [lookup_set_other _ _ _ _ (by decide)]
    exact hn
  · exact ha

theorem decoded_xor_run (s : State) (left right : BitVec 64) (hc : ConfigOK s)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right) :
    (decoded 0x00b54533).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x10 (left ^^^ right)) := by
  have hd : (encdec_backwards 0x00b54533).run s =
      .ok (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, .XOR)) s := by
    rw [decode_xor]
    exact decoderChecks_run s _ hc
  unfold decoded
  rw [bind_run_ok _ _ hd]
  exact execute_xor_run s left right hl hr

theorem xor_return (s : State) (left right ra next : BitVec 64) (hc : ConfigOK s)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right)
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (ha : ReturnAligned ra) :
    (bodies 0x00b54533 0x00008067).run s = .ok RETIRE_SUCCESS
      (setRegister (setRegister s Register.x10 (left ^^^ right)) Register.nextPC
        (Sail.BitVec.update ra 0 0#1)) := by
  unfold bodies
  rw [bind_run_ok _ _ (decoded_xor_run s left right hc hl hr)]
  apply decoded_ret_run _ ra next (config_set_x10 s _ hc)
  · rw [lookup_set_other _ _ _ _ (by decide)]
    exact hra
  · rw [lookup_set_other _ _ _ _ (by decide)]
    exact hn
  · exact ha

end OakSailBridge.BitwiseDecoded
