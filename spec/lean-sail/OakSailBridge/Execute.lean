import LeanRV64D.InstsEnd
import OakSailBridge.RiscV

/-!
# The execution bodies themselves

`OakSailBridge.RiscV` proves the data semantics of each instruction —
Oak's function of the register values equals the Sail expression the
model's `execute_*` body writes back. Here the bodies are no longer read
by inspection: each theorem rewrites the generated `execute_RTYPEW`,
`execute_RTYPE` and `execute_BTYPE` (LeanRV64D/InstsEnd.lean) to their
canonical monadic shape — read the two sources, write Oak's function of
them (or branch on Oak's `Br.holds`) — through the monad laws and the
data theorems, so the register-plumbing is checked too.
-/

set_option autoImplicit false

namespace OakSailBridge

open LeanRV64D
open LeanRV64D.Functions
open Sail

/-- Oak's function for a word (RV64 `*W`) register-register op. -/
def rtypew : ropw → X → X → X
  | .ADDW, a, b => addw a b
  | .SUBW, a, b => subw a b
  | .SLLW, a, b => sllw a b
  | .SRLW, a, b => srlw a b
  | .SRAW, a, b => sraw a b

/-- Oak's function for a full-width register-register op. -/
def rtype : rop → X → X → X
  | .ADD, a, b => a + b
  | .SUB, a, b => a - b
  | .AND, a, b => a &&& b
  | .OR, a, b => a ||| b
  | .XOR, a, b => a ^^^ b
  | .SLT, a, b => slt a b
  | .SLTU, a, b => sltu a b
  | .SLL, a, b => sll a b
  | .SRL, a, b => srl a b
  | .SRA, a, b => sra a b

/-- The branch condition each `bop` names, as Oak's `Br`. -/
def br : bop → Br
  | .BEQ => .beq
  | .BNE => .bne
  | .BLT => .blt
  | .BGE => .bge
  | .BLTU => .bltu
  | .BGEU => .bgeu

theorem execute_RTYPEW_canonical (rs2 rs1 rd : regidx) (op : ropw) :
    execute_RTYPEW rs2 rs1 rd op = (do
      let x1 ← rX_bits rs1
      let x2 ← rX_bits rs2
      wX_bits rd (rtypew op x1 x2)
      pure RETIRE_SUCCESS) := by
  unfold execute_RTYPEW
  cases op <;> simp only [rtypew, pure_bind, addw_bridge, subw_bridge, sllw_bridge, srlw_bridge, sraw_bridge]

theorem execute_RTYPE_canonical (rs2 rs1 rd : regidx) (op : rop) :
    execute_RTYPE rs2 rs1 rd op = (do
      let x1 ← rX_bits rs1
      let x2 ← rX_bits rs2
      wX_bits rd (rtype op x1 x2)
      pure RETIRE_SUCCESS) := by
  unfold execute_RTYPE
  -- The shift bridges (OakSailBridge.RiscV) take the model's shift amount
  -- as written, `extractLsb x2 (log2_xlen -i 1) 0`.
  cases op <;> simp only [rtype, bind_assoc, pure_bind, slt_bridge, sltu_bridge, sll_bridge, srl_bridge, sra_bridge]

theorem execute_BTYPE_canonical (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) :
    execute_BTYPE imm rs2 rs1 op = (do
      let x1 ← rX_bits rs1
      let x2 ← rX_bits rs2
      if Br.holds (br op) x1 x2 then jump_to ((← readReg Register.PC) + (sign_extend (m := 64) imm))
      else pure RETIRE_SUCCESS) := by
  unfold execute_BTYPE
  cases op <;> simp only [br, bind_assoc, pure_bind, beq_bridge, bne_bridge, blt_bridge, bge_bridge, bltu_bridge, bgeu_bridge] <;> rfl

end OakSailBridge
