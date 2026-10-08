import OakSailBridge.FramedPhysicalMemory
import OakSailBridge.FramedPMP
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

private theorem addInt_zero {width : Nat} (addr : BitVec width) :
    Sail.BitVec.addInt addr 0 = addr := by
  simp [Sail.BitVec.addInt]

theorem checked_store8_run (s : State) (addr value : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hr : s.regs.get? Register.pma_regions = some regions)
    (hregion : RAMRegion regions addr region) (hlow : LowRAM addr)
    (ht : s.regs.get? Register.htif_tohost_base = some none)
    (hc : s.regs.get? Register.pmpcfg_n = some openPMPConfig)
    (ha : s.regs.get? Register.pmpaddr_n = some openPMPAddress) :
    (checked_mem_write (.Physaddr addr) 8 value (.Store .Data) .PBMT_PMA .Machine
      () false false false).run s = .ok (.Ok true) (store64 s addr.toNat value) := by
  have hperm := pma_priority_store s addr regions region hr hregion
  have hpmp := pmp_store_run s addr hc ha
  have hmmio := mmio_write_false s addr hlow ht
  have hwrite := write_ram8_run s addr value
  unfold checked_mem_write
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, ExceptT.pure,
    liftM, monadLift, MonadLift.monadLift, Bind.bind, Functor.map,
    EStateM.bind, EStateM.map, EStateM.run, Pure.pure, EStateM.pure] at hperm hpmp hmmio hwrite ⊢
  rw [hperm]
  simp only [aligned_split, EStateM.pure]
  simp only [write_kind_of_flags, misaligned_order, sys_misaligned_order_decreasing,
    untilFuelM, untilFuelM.go, LeanRV64D.assert, PreSail.assert,
    ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.bind,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  simp only [Bool.false_eq_true, if_false, Int.reduceToNat, Int.reduceSub]
  simp only [untilFuelM.go, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  simp [bits_of_physaddr, addInt_zero, Sail.BitVec.extractLsb,
    hpmp, hmmio, hwrite, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  try simp only [hpmp, hmmio, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  try simp only [_root_.BitVec.extractLsb, _root_.BitVec.extractLsb'_eq_self] at *
  try rw [hwrite]
  try rfl

theorem checked_load8_run (s : State) (addr value : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hr : s.regs.get? Register.pma_regions = some regions)
    (hregion : RAMRegion regions addr region) (hlow : LowRAM addr)
    (ht : s.regs.get? Register.htif_tohost_base = some none)
    (hc : s.regs.get? Register.pmpcfg_n = some openPMPConfig)
    (ha : s.regs.get? Register.pmpaddr_n = some openPMPAddress)
    (hbytes : ∀ i : Fin 8, s.mem.get? (addr.toNat + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (checked_mem_read (.Load .Data) .PBMT_PMA .Machine (.Physaddr addr) 8
      false false false false).run s = .ok (.Ok (value, ())) s := by
  have hperm := pma_priority_load s addr regions region hr hregion
  have hpmp := pmp_load_run s addr hc ha
  have hmmio := mmio_read_false s addr hlow ht
  have hread := read_ram8_run s addr value hbytes
  unfold checked_mem_read
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, ExceptT.pure,
    liftM, monadLift, MonadLift.monadLift, Bind.bind, Functor.map,
    EStateM.bind, EStateM.map, EStateM.run, Pure.pure, EStateM.pure] at hperm hpmp hmmio hread ⊢
  rw [hperm]
  simp only [aligned_split, EStateM.pure]
  simp only [read_kind_of_flags, misaligned_order, sys_misaligned_order_decreasing,
    untilFuelM, untilFuelM.go, LeanRV64D.assert, PreSail.assert,
    ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.bind,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  simp only [Bool.false_eq_true, if_false, Int.reduceToNat, Int.reduceSub]
  simp only [untilFuelM.go, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  simp [bits_of_physaddr, addInt_zero, Sail.BitVec.extractLsb,
    hpmp, hmmio, hread, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  try simp only [hpmp, hmmio, hread, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  try simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros]
  try rfl

theorem store_ea8_run (s : State) (addr : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hr : s.regs.get? Register.pma_regions = some regions)
    (hregion : RAMRegion regions addr region)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hc : s.regs.get? Register.pmpcfg_n = some openPMPConfig)
    (ha : s.regs.get? Register.pmpaddr_n = some openPMPAddress) :
    (mem_write_ea (.Physaddr addr) 8 (.Store .Data) .PBMT_PMA
      false false false).run s = .ok (.Ok ()) s := by
  have hperm := pma_priority_store s addr regions region hr hregion
  have hpmp := pmp_store_run s addr hc ha
  unfold mem_write_ea
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, ExceptT.pure,
    liftM, monadLift, MonadLift.monadLift, Bind.bind, Functor.map,
    EStateM.bind, EStateM.map, EStateM.run, Pure.pure, EStateM.pure] at hperm hpmp ⊢
  simp only [PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Bind.bind, EStateM.bind, EStateM.map, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Pure.pure, EStateM.pure, hm, hp]
  simp only [effectivePrivilege, _get_Mstatus_MPRV, Sail.BitVec.extractLsb]
  dsimp
  simp only [Pure.pure, EStateM.pure, EStateM.map, EStateM.bind, ExceptT.bindCont]
  rw [hperm]
  simp only [aligned_split, EStateM.pure]
  simp only [write_kind_of_flags, misaligned_order, sys_misaligned_order_decreasing,
    untilFuelM, untilFuelM.go, LeanRV64D.assert, PreSail.assert,
    ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.bind,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  simp only [Bool.false_eq_true, if_false, Int.reduceToNat, Int.reduceSub]
  simp only [untilFuelM.go, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  simp [bits_of_physaddr, addInt_zero, Sail.BitVec.extractLsb,
    hpmp, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  try rfl

end OakSailBridge.BitwiseDecoded
