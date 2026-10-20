import OakSailBridge.FramedRegisters
/-! Concrete Machine-mode translation, with MPRV disabled. This does not
assume a memory operation succeeds and does not establish PMA/PMP permission. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem machine_effective (access : MemoryAccessType mem_payload) :
    effectivePrivilege access 0 .Machine = pure Privilege.Machine := by
  simp [effectivePrivilege, _get_Mstatus_MPRV, Sail.BitVec.extractLsb]

theorem machine_bare : translationMode .Machine = pure SATPMode.Bare := by rfl

theorem translate_load_run (s : State) (addr : BitVec 64)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64)) :
    (translateAddr (.Virtaddr addr) (.Load .Data)).run s =
      .ok (.Ok (.Physaddr addr, .PBMT_PMA, ())) s := by
  unfold translateAddr
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hm, hp]
  simp only [machine_effective, machine_bare, is_shadow_stack_access,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  rfl

theorem translate_store_run (s : State) (addr : BitVec 64)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64)) :
    (translateAddr (.Virtaddr addr) (.Store .Data)).run s =
      .ok (.Ok (.Physaddr addr, .PBMT_PMA, ())) s := by
  unfold translateAddr
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hm, hp]
  simp only [machine_effective, machine_bare, is_shadow_stack_access,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  rfl


theorem pmlen_load_run (s : State)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hc : s.regs.get? Register.mseccfg = some (0#64)) :
    (get_pmlen (.Load .Data) .Machine).run s = .ok 0 s := by
  unfold get_pmlen is_pmm_applicable
  try simp only [bind_assoc]
  rw [bind_run_ok _ _ (read_register s Register.mstatus 0 hm)]
  simp only [pure_bind]
  unfold get_pmm
  split
  · simp only [bind_assoc]
    rw [bind_run_ok _ _ (read_register s Register.mseccfg 0 hc)]
    rfl
  · rename_i h
    exact False.elim (h (by decide))

theorem transform_load_run (s : State) (addr : BitVec 64)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hc : s.regs.get? Register.mseccfg = some (0#64)) :
    (transform_effective_address (.Virtaddr addr) (.Load .Data)).run s =
      .ok (.Virtaddr addr) s := by
  unfold transform_effective_address
  try simp only [bind_assoc]
  rw [bind_run_ok _ _ (read_register s Register.mstatus 0 hm)]
  rw [bind_run_ok _ _ (read_register s Register.cur_privilege .Machine hp)]
  rw [machine_effective]
  simp only [pure_bind]
  rw [bind_run_ok _ _ (pmlen_load_run s hm hc)]
  rw [machine_bare]
  simp only [pure_bind]
  change EStateM.Result.ok (virtaddr.Virtaddr (addr.extractLsb' 0 64)) s =
    (EStateM.Result.ok (virtaddr.Virtaddr addr) s : EStateM.Result (Sail.Error exception) State virtaddr)
  simp

theorem pmlen_store_run (s : State)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hc : s.regs.get? Register.mseccfg = some (0#64)) :
    (get_pmlen (.Store .Data) .Machine).run s = .ok 0 s := by
  unfold get_pmlen is_pmm_applicable
  try simp only [bind_assoc]
  rw [bind_run_ok _ _ (read_register s Register.mstatus 0 hm)]
  simp only [pure_bind]
  unfold get_pmm
  split
  · simp only [bind_assoc]
    rw [bind_run_ok _ _ (read_register s Register.mseccfg 0 hc)]
    rfl
  · rename_i h
    exact False.elim (h (by decide))

theorem transform_store_run (s : State) (addr : BitVec 64)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hc : s.regs.get? Register.mseccfg = some (0#64)) :
    (transform_effective_address (.Virtaddr addr) (.Store .Data)).run s =
      .ok (.Virtaddr addr) s := by
  unfold transform_effective_address
  try simp only [bind_assoc]
  rw [bind_run_ok _ _ (read_register s Register.mstatus 0 hm)]
  rw [bind_run_ok _ _ (read_register s Register.cur_privilege .Machine hp)]
  rw [machine_effective]
  simp only [pure_bind]
  rw [bind_run_ok _ _ (pmlen_store_run s hm hc)]
  rw [machine_bare]
  simp only [pure_bind]
  change EStateM.Result.ok (virtaddr.Virtaddr (addr.extractLsb' 0 64)) s =
    (EStateM.Result.ok (virtaddr.Virtaddr addr) s : EStateM.Result (Sail.Error exception) State virtaddr)
  simp

end OakSailBridge.BitwiseDecoded
