import OakSailBridge.FramedCheckedMemory
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

/-- Explicit pinned platform register configuration. Memory content is not
assumed here, and each access separately checks region containment/alignment. -/
structure MemoryConfig (s : State) (regions : List PMA_Region) : Prop where
  privilege : s.regs.get? Register.cur_privilege = some Privilege.Machine
  status : s.regs.get? Register.mstatus = some (0#64)
  masking : s.regs.get? Register.mseccfg = some (0#64)
  regions : s.regs.get? Register.pma_regions = some regions
  htif : s.regs.get? Register.htif_tohost_base = some none
  pmpcfg : s.regs.get? Register.pmpcfg_n = some openPMPConfig
  pmpaddr : s.regs.get? Register.pmpaddr_n = some openPMPAddress

theorem mem_store8_run (s : State) (addr value : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region) (hc : MemoryConfig s regions)
    (hr : RAMRegion regions addr region) (hl : LowRAM addr) :
    (mem_write_value (.Physaddr addr) 8 value (.Store .Data) .PBMT_PMA
      false false false).run s = .ok (.Ok true) (store64 s addr.toNat value) := by
  unfold mem_write_value mem_write_value_meta
  rw [bind_run_ok _ _ (read_register s Register.mstatus 0 hc.status)]
  rw [bind_run_ok _ _ (read_register s Register.cur_privilege .Machine hc.privilege)]
  rw [machine_effective]
  simp only [pure_bind]
  unfold mem_write_value_priv_meta
  rw [bind_run_ok _ _ (checked_store8_run s addr value regions region hc.regions hr hl
    hc.htif hc.pmpcfg hc.pmpaddr)]
  rfl

theorem mem_load8_run (s : State) (addr value : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region) (hc : MemoryConfig s regions)
    (hr : RAMRegion regions addr region) (hl : LowRAM addr)
    (hb : ∀ i : Fin 8, s.mem.get? (addr.toNat + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (mem_read (.Load .Data) .PBMT_PMA (.Physaddr addr) 8
      false false false).run s = .ok (.Ok value) s := by
  unfold mem_read
  rw [bind_run_ok _ _ (read_register s Register.mstatus 0 hc.status)]
  rw [bind_run_ok _ _ (read_register s Register.cur_privilege .Machine hc.privilege)]
  rw [machine_effective]
  simp only [pure_bind]
  unfold mem_read_priv mem_read_priv_meta
  simp only [bind_assoc]
  rw [bind_run_ok _ _ (checked_load8_run s addr value regions region hc.regions hr hl
    hc.htif hc.pmpcfg hc.pmpaddr hb)]
  rfl

end OakSailBridge.BitwiseDecoded
