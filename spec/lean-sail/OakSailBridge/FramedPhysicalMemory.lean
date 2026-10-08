import OakSailBridge.FramedMemoryBytes
import OakSailBridge.FramedPermissions
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem write_ram8_shape (addr : BitVec 64) (value : BitVec 64) :
    Functions.write_ram .Write_plain (.Physaddr addr) 8 value () =
      (PreSail.writeBytes (n := 8) addr.toNat value : SailM Bool) := by rfl

theorem write_ram8_run (s : State) (addr value : BitVec 64) :
    (Functions.write_ram .Write_plain (.Physaddr addr) 8 value ()).run s =
      .ok true (store64 s addr.toNat value) := by
  rw [write_ram8_shape]
  exact writeBytes8_run s addr.toNat value

theorem read_ram8_shape (addr : BitVec 64) :
    Functions.read_ram .Read_plain (.Physaddr addr) 8 false = (do
      let (value, _) ← (PreSail.readBytes 8 addr.toNat : SailM (BitVec 64 × Option Bool))
      pure (value, ())) := by
  simp only [Functions.read_ram, pure_bind, PreSail.sail_mem_read, bind_assoc]
  try rfl

theorem read_ram8_run (s : State) (addr value : BitVec 64)
    (h : ∀ i : Fin 8, s.mem.get? (addr.toNat + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (Functions.read_ram .Read_plain (.Physaddr addr) 8 false).run s =
      .ok (value, ()) s := by
  rw [read_ram8_shape]
  rw [bind_run_ok _ _ (readBytes8_run s addr.toNat value h)]
  rfl

/-- Restrict stack bytes to the low RAM region, away from fixed CLINT and
signature MMIO windows. HTIF is separately disabled in state. -/
def LowRAM (addr : BitVec 64) : Prop := addr.toNat + 8 ≤ 0x02000000

theorem mmio_read_false (s : State) (addr : BitVec 64) (h : LowRAM addr)
    (ht : s.regs.get? Register.htif_tohost_base = some none) :
    (within_mmio_readable (.Physaddr addr) 8).run s = .ok false s := by
  have hc : within_clint (.Physaddr addr) 8 = (pure false : SailM Bool) := by
    change pure (decide (33554432 ≤ (addr.toNat : Int)) &&
      decide ((addr.toNat : Int) + 8 ≤ 34340864)) = pure false
    have hh : ¬ (33554432 : Int) ≤ addr.toNat := by unfold LowRAM at h; omega
    simp [hh]
  have hs : within_sig (.Physaddr addr) 8 = (pure false : SailM Bool) := by
    change pure (decide (201326592 ≤ (addr.toNat : Int)) &&
      decide ((addr.toNat : Int) + 8 ≤ 201326624)) = pure false
    have hh : ¬ (201326592 : Int) ≤ addr.toNat := by unfold LowRAM at h; omega
    simp [hh]
  simp only [within_mmio_readable, get_config_rvfi, hc, hs, pure_bind]
  unfold within_htif_readable within_htif_writable
  simp only [Bool.false_eq_true, if_false, bind_assoc]
  rw [bind_run_ok _ _ (read_register s Register.htif_tohost_base none ht)]
  rfl

theorem mmio_write_false (s : State) (addr : BitVec 64) (h : LowRAM addr)
    (ht : s.regs.get? Register.htif_tohost_base = some none) :
    (within_mmio_writable (.Physaddr addr) 8).run s = .ok false s := by
  have heq : within_mmio_writable (.Physaddr addr) 8 =
      within_mmio_readable (.Physaddr addr) 8 := by rfl
  rw [heq]
  exact mmio_read_false s addr h ht

theorem aligned_split (addr : BitVec 64) :
    split_misaligned (.Physaddr addr) 8 0 .CannotSplit = pure (1, 8) := by rfl

theorem pma_priority_load (s : State) (addr : BitVec 64) (regions : List PMA_Region)
    (region : PMA_Region) (hr : s.regs.get? Register.pma_regions = some regions)
    (h : RAMRegion regions addr region) :
    (check_pma_with_pmp_priority (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr addr) 8 false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
  unfold check_pma_with_pmp_priority
  rw [bind_run_ok _ _ (pma_load_run s addr regions region hr h)]
  rfl

theorem pma_priority_store (s : State) (addr : BitVec 64) (regions : List PMA_Region)
    (region : PMA_Region) (hr : s.regs.get? Register.pma_regions = some regions)
    (h : RAMRegion regions addr region) :
    (check_pma_with_pmp_priority (.Store .Data) .PBMT_PMA .Machine
      (.Physaddr addr) 8 false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
  unfold check_pma_with_pmp_priority
  rw [bind_run_ok _ _ (pma_store_run s addr regions region hr h)]
  rfl

end OakSailBridge.BitwiseDecoded
