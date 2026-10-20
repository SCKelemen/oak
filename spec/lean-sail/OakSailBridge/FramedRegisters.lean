import OakSailBridge.FramedDecoded
/-! Actual generated ADDI execution for the production frame. These results
make no memory or fetch claim. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem read_x2 : rX_bits (.Regidx 2) = readReg Register.x2 := by
  simp [rX_bits, rX, Sail.BitVec.toNatInt, regval_from_reg]

theorem write_x2 (v : BitVec 64) : wX_bits (.Regidx 2) v = writeReg Register.x2 v := by rfl

theorem write_x18 (v : BitVec 64) : wX_bits (.Regidx 18) v = writeReg Register.x18 v := by rfl

theorem execute_sp_add_shape (imm : BitVec 12) :
    execute_ITYPE imm (.Regidx 2) (.Regidx 2) .ADDI = (do
      let sp ← readReg Register.x2
      writeReg Register.x2 (sp + imm.signExtend 64)
      pure RETIRE_SUCCESS) := by
  simp only [execute_ITYPE, pure_bind, bind_assoc, read_x2, write_x2,
    sign_extend, Sail.BitVec.signExtend]

theorem execute_sp_add_run (s : State) (sp : BitVec 64) (imm : BitVec 12)
    (h : s.regs.get? Register.x2 = some sp) :
    (execute_ITYPE imm (.Regidx 2) (.Regidx 2) .ADDI).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x2 (sp + imm.signExtend 64)) := by
  rw [execute_sp_add_shape, bind_run_ok _ _ (read_register s Register.x2 sp h)]
  rfl

theorem execute_copy_right_run (s : State) (right : BitVec 64)
    (h : s.regs.get? Register.x11 = some right) :
    (execute_ITYPE 0 (.Regidx 11) (.Regidx 18) .ADDI).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x18 right) := by
  have hs : execute_ITYPE 0 (.Regidx 11) (.Regidx 18) .ADDI = (do
      let right ← readReg Register.x11
      writeReg Register.x18 right
      pure RETIRE_SUCCESS) := by
    simp only [execute_ITYPE, pure_bind, bind_assoc, read_x11, write_x18,
      sign_extend, Sail.BitVec.signExtend]
    simp
  rw [hs, bind_run_ok _ _ (read_register s Register.x11 right h)]
  rfl

end OakSailBridge.BitwiseDecoded
