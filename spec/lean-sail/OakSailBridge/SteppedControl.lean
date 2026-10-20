import OakSailBridge.FetchedInstruction
import LeanRV64D.Step

/-! Derived control-flow rules for unchanged generated single-step semantics.
The final composition discharges these intermediate fetch/decode/body rules. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem tick_pc_run (s : State) (target : BitVec 64)
    (hn : s.regs.get? Register.nextPC = some target) :
    (tick_pc ()).run s = .ok () (setRegister s Register.PC target) := by
  unfold tick_pc
  rw [bind_run_ok _ _ (read_register s Register.nextPC target hn)]
  rw [bind_run_ok _ _ (write_register s Register.PC target)]
  rw [bind_run_ok _ _ (read_register (setRegister s Register.PC target) Register.PC target
    (lookup_set_same _ _ _))]
  rfl


/-- Actual active-hart control path, retaining its real decoder and dispatcher. -/
theorem run_hart_active_success (s t : State) (step : Nat)
    (pc : BitVec 64) (word : BitVec 32) (inst : instruction)
    (hp : s.regs.get? Register.cur_privilege = some .Machine)
    (hpc : s.regs.get? Register.PC = some pc)
    (hi : (dispatchInterrupt .Machine).run s = .ok none s)
    (hf : (fetch ()).run s = .ok (.F_Base word) s)
    (hd : (ext_decode word).run s = .ok inst s)
    (hl : (is_landing_pad_expected ()).run s = .ok false s)
    (he : (execute inst).run (setRegister s Register.nextPC (pc + 4#64)) =
      .ok RETIRE_SUCCESS t) :
    (run_hart_active step).run s = .ok (.Step_Execute (RETIRE_SUCCESS, word)) t := by
  simp only [EStateM.run] at hi hf hd hl he
  unfold run_hart_active
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.pure, ExceptT.bindCont,
    liftM, monadLift, MonadLift.monadLift, Bind.bind, Functor.map,
    EStateM.bind, EStateM.map, EStateM.run, PreSail.readReg, PreSail.writeReg,
    MonadState.get, getThe, MonadStateOf.get, EStateM.get, EStateM.set, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    Pure.pure, EStateM.pure, hp, hpc, hi, hf, hd, hl, he,
    ext_fetch_hook, sail_instr_announce, fetch_callback, get_config_print_instr,
    Sail.BitVec.addInt, Sail.BitVec.signExtend, Sail.BitVec.zeroExtend,
    zero_extend, setRegister, RETIRE_SUCCESS] at *

/-- Actual try_step bookkeeping, including its unconditional increment-flag
write and final PC readback. Success premises below are discharged by the
instruction/profile composition, not treated as hardware assumptions. -/
theorem try_step_success (s t : State) (step : Nat) (exitWait : Bool)
    (word : BitVec 32) (target : BitVec 64)
    (hp : s.regs.get? Register.cur_privilege = some .Machine)
    (hc : (should_inc_minstret .Machine).run s = .ok false s)
    (ha : s.regs.get? Register.hart_state = some (.HART_ACTIVE ()))
    (hrun : (run_hart_active step).run (setRegister s Register.minstret_increment false) =
      .ok (.Step_Execute (RETIRE_SUCCESS, word)) t)
    (ht : t.regs.get? Register.hart_state = some (.HART_ACTIVE ()))
    (hi : t.regs.get? Register.minstret_increment = some false)
    (hn : t.regs.get? Register.nextPC = some target) :
    (try_step step exitWait).run s = .ok false (setRegister t Register.PC target) := by
  have hstart : (setRegister s Register.minstret_increment false).regs.get? Register.hart_state =
      some (.HART_ACTIVE ()) := by
    simpa [setRegister, Std.ExtDHashMap.get?_insert] using ha
  have hinc : (setRegister t Register.PC target).regs.get? Register.minstret_increment =
      some false := by simpa [setRegister, Std.ExtDHashMap.get?_insert] using hi
  have htick := tick_pc_run t target hn
  simp only [EStateM.run] at hc hrun htick
  unfold try_step
  simp [ext_pre_step_hook, ext_post_step_hook, instret_callback, get_config_rvfi,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.pure, ExceptT.bindCont,
    liftM, monadLift, MonadLift.monadLift, Bind.bind, Functor.map,
    EStateM.bind, EStateM.map, EStateM.run, PreSail.readReg, PreSail.writeReg,
    MonadState.get, getThe, MonadStateOf.get, EStateM.get, EStateM.set,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    Pure.pure, EStateM.pure, hp, hc, ha, hstart, hrun, ht, hi, hn, htick, hinc,
    hart_is_active, LeanRV64D.assert, PreSail.assert, RETIRE_SUCCESS, setRegister, Std.ExtDHashMap.get?_insert] at *

end OakSailBridge.BitwiseDecoded
