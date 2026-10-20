import OakSailBridge.FramedVirtualMemory
import OakSailBridge.FramedState
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem read_x9 : rX_bits (.Regidx 9) = readReg Register.x9 := by
  simp [rX_bits, rX, Sail.BitVec.toNatInt, regval_from_reg]

theorem read_x18 : rX_bits (.Regidx 18) = readReg Register.x18 := by
  simp [rX_bits, rX, Sail.BitVec.toNatInt, regval_from_reg]

theorem execute_save_x9_run (s : State) (sp value : BitVec 64) (imm : BitVec 12)
    (regions : List PMA_Region) (region : PMA_Region) (hc : MemoryConfig s regions)
    (hx : s.regs.get? Register.x2 = some sp)
    (hv : s.regs.get? Register.x9 = some value)
    (hr : RAMRegion regions (sp + imm.signExtend 64) region)
    (hl : LowRAM (sp + imm.signExtend 64)) :
    (execute_STORE imm (.Regidx 9) (.Regidx 2) 8).run s =
      .ok RETIRE_SUCCESS (store64 s (sp + imm.signExtend 64).toNat value) := by
  unfold execute_STORE
  simp only [Functions.xlen_bytes, LeanRV64D.assert, PreSail.assert]
  simp only [show (8 ≤ 8) = True from propext (by decide), decide_true, if_true, pure_bind,
    read_x9, sign_extend, Sail.BitVec.signExtend, bind_assoc]
  rw [bind_run_ok _ _ (read_register s Register.x9 value hv)]
  simp only [pure_bind, Sail.BitVec.extractLsb, _root_.BitVec.extractLsb]
  have hm := vmem_stack_store8_run s sp (imm.signExtend 64) value
    regions region hx hc hr hl
  simp at hm ⊢
  rw [hm]
  rfl

theorem execute_save_x18_run (s : State) (sp value : BitVec 64) (imm : BitVec 12)
    (regions : List PMA_Region) (region : PMA_Region) (hc : MemoryConfig s regions)
    (hx : s.regs.get? Register.x2 = some sp)
    (hv : s.regs.get? Register.x18 = some value)
    (hr : RAMRegion regions (sp + imm.signExtend 64) region)
    (hl : LowRAM (sp + imm.signExtend 64)) :
    (execute_STORE imm (.Regidx 18) (.Regidx 2) 8).run s =
      .ok RETIRE_SUCCESS (store64 s (sp + imm.signExtend 64).toNat value) := by
  unfold execute_STORE
  simp only [Functions.xlen_bytes, LeanRV64D.assert, PreSail.assert]
  simp only [show (8 ≤ 8) = True from propext (by decide), decide_true, if_true, pure_bind,
    read_x18, sign_extend, Sail.BitVec.signExtend, bind_assoc]
  rw [bind_run_ok _ _ (read_register s Register.x18 value hv)]
  simp only [pure_bind, Sail.BitVec.extractLsb, _root_.BitVec.extractLsb]
  have hm := vmem_stack_store8_run s sp (imm.signExtend 64) value
    regions region hx hc hr hl
  simp at hm ⊢
  rw [hm]
  rfl

theorem execute_restore_x9_run (s : State) (sp value : BitVec 64) (imm : BitVec 12)
    (regions : List PMA_Region) (region : PMA_Region) (hc : MemoryConfig s regions)
    (hx : s.regs.get? Register.x2 = some sp)
    (hr : RAMRegion regions (sp + imm.signExtend 64) region)
    (hl : LowRAM (sp + imm.signExtend 64))
    (hb : ∀ i : Fin 8, s.mem.get? ((sp + imm.signExtend 64).toNat + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (execute_LOAD imm (.Regidx 2) (.Regidx 9) false 8).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x9 value) := by
  unfold execute_LOAD
  simp only [Functions.xlen_bytes, LeanRV64D.assert, PreSail.assert]
  simp only [show (8 ≤ 8) = True from propext (by decide), decide_true, if_true, pure_bind,
    sign_extend, Sail.BitVec.signExtend]
  rw [bind_run_ok _ _ (vmem_stack_load8_run s sp (imm.signExtend 64) value
    regions region hx hc hr hl hb)]
  simp [extend_value, sign_extend, Sail.BitVec.signExtend]
  rfl

theorem execute_restore_x18_run (s : State) (sp value : BitVec 64) (imm : BitVec 12)
    (regions : List PMA_Region) (region : PMA_Region) (hc : MemoryConfig s regions)
    (hx : s.regs.get? Register.x2 = some sp)
    (hr : RAMRegion regions (sp + imm.signExtend 64) region)
    (hl : LowRAM (sp + imm.signExtend 64))
    (hb : ∀ i : Fin 8, s.mem.get? ((sp + imm.signExtend 64).toNat + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (execute_LOAD imm (.Regidx 2) (.Regidx 18) false 8).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x18 value) := by
  unfold execute_LOAD
  simp only [Functions.xlen_bytes, LeanRV64D.assert, PreSail.assert]
  simp only [show (8 ≤ 8) = True from propext (by decide), decide_true, if_true, pure_bind,
    sign_extend, Sail.BitVec.signExtend]
  rw [bind_run_ok _ _ (vmem_stack_load8_run s sp (imm.signExtend 64) value
    regions region hx hc hr hl hb)]
  simp [extend_value, sign_extend, Sail.BitVec.signExtend]
  rfl

end OakSailBridge.BitwiseDecoded
