import OakSailBridge.FetchedMemory
import LeanRV64D.Fetch
/-! Actual pinned instruction fetch, using concrete RAM and permissions.
No fetch-success hypothesis or replacement fetch interpreter is introduced. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem translate_fetch_run (s : State) (addr : BitVec 64)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64)) :
    (translateAddr (.Virtaddr addr) (.InstructionFetch ())).run s =
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

theorem fetch_bytes4_run (s : State) (pc : BitVec 64) (word : BitVec 32)
    (regions : List PMA_Region) (region : PMA_Region) (hc : MemoryConfig s regions)
    (hr : ExecutableRegion regions pc region) (hl : LowCodeRAM pc)
    (hb : ∀ i : Fin 4, s.mem.get? (pc.toNat + i.val) =
      some (word.extractLsb' (8 * i.val) 8)) :
    (fetch_bytes pc pc 4).run s = .ok (.FetchBytes_Success word) s := by
  have ht := translate_fetch_run s pc hc.privilege hc.status
  have hm := mem_fetch4_run s pc word regions region hc hr hl hb
  simp only [EStateM.run] at ht hm
  unfold fetch_bytes
  simp [ext_fetch_check_pc, SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    Pure.pure, EStateM.pure, ht, hm]

theorem enabled_ziccif : currentlyEnabled .Ext_Ziccif = (pure true : SailM Bool) := by
  simp [currentlyEnabled, hartSupports]

theorem aligned4_bits (pc : BitVec 64) (h : pc.toNat % 4 = 0) :
    Sail.BitVec.access pc 0 = (0#1) ∧ Sail.BitVec.access pc 1 = (0#1) := by
  have h0 : pc.toNat % 2 = 0 := by omega
  have h1 : pc.toNat / 2 % 2 = 0 := by omega
  constructor
  · change BitVec.ofBool (pc.getLsbD 0) = (0#1)
    simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, h0]
  · change BitVec.ofBool (pc.getLsbD 1) = (0#1)
    simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, h1]

/-- The actual fetch reads one full word because pinned Ziccif is enabled.
State is unchanged because all selected checks and the sequential RAM read are
proved read-only; the result has the actual instruction's low-bits condition. -/
theorem fetch_base_run (s : State) (pc : BitVec 64) (word : BitVec 32)
    (regions : List PMA_Region) (region : PMA_Region) (hc : MemoryConfig s regions)
    (hmisa : s.regs.get? Register.misa = some misaRV64I)
    (hpc : s.regs.get? Register.PC = some pc)
    (halign : pc.toNat % 4 = 0)
    (hr : ExecutableRegion regions pc region) (hl : LowCodeRAM pc)
    (hb : ∀ i : Fin 4, s.mem.get? (pc.toNat + i.val) =
      some (word.extractLsb' (8 * i.val) 8))
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false) :
    (fetch ()).run s = .ok (.F_Base word) s := by
  have hbits := aligned4_bits pc halign
  have hf := fetch_bytes4_run s pc word regions region hc hr hl hb
  have hz := enabled_zca_run s hmisa
  have ha : is_aligned_vaddr (.Virtaddr pc) 4 = true := hr.2.2
  simp only [EStateM.run] at hf hz
  unfold fetch
  simp [get_config_rvfi, ext_fetch_check_pc, enabled_ziccif,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.map, ExceptT.lift,
    ExceptT.mk, ExceptT.pure, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
    Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hpc, hbits.1, hbits.2, hz, ha, hf, hbase, Functions.not]

end OakSailBridge.BitwiseDecoded
