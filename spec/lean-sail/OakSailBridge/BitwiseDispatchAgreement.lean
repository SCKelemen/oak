import OakSailBridge.BitwiseDecoded

/-! Structural agreement with the generated full dispatcher, independently of
source inspection or a trusted dispatch assumption. Its audit deliberately
includes opaque primitives from other full-dispatcher branches; this is kept
separate from the narrow execution theorem's dependency closure. -/
set_option autoImplicit false
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions

theorem generated_rtype_dispatch (rs2 rs1 rd : regidx) (op : rop) :
    execute (.RTYPE (rs2, rs1, rd, op)) =
      executeSupported (.RTYPE (rs2, rs1, rd, op)) := by rfl

theorem generated_jalr_dispatch (imm : BitVec 12) (rs1 rd : regidx) :
    execute (.JALR (imm, rs1, rd)) =
      executeSupported (.JALR (imm, rs1, rd)) := by rfl
end OakSailBridge.BitwiseDecoded
