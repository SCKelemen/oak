import OakSailFetchedFrame
import OakSailBridge.SteppedControl
import OakSailBridge.SteppedProfile
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailSteppedState
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode OakSailFetchedFrame
open Oak.BitwiseFunction (Op)
attribute [local irreducible] store64

/-- Actual bookkeeping fields; this pure record operation is used to describe
results, never to replace execution of generated try_step. -/
def controlState (s : State) (pc next : BitVec 64) : State :=
  setRegister (setRegister (setRegister s Register.PC pc) Register.nextPC next)
    Register.minstret_increment false

def bodyStage (s : State) (sp saved1 saved2 left right ra : BitVec 64) (op : Op) :
    Nat → State
  | 0 => s
  | 1 => setRegister s Register.x2 (sp - 96#64)
  | 2 => store64 (bodyStage s sp saved1 saved2 left right ra op 1) (sp - 96#64).toNat saved1
  | 3 => store64 (bodyStage s sp saved1 saved2 left right ra op 2) (sp - 96#64 + 8#64).toNat saved2
  | 4 => setRegister (bodyStage s sp saved1 saved2 left right ra op 3) Register.x18 right
  | 5 => setRegister (bodyStage s sp saved1 saved2 left right ra op 4) Register.x10
      (Oak.RiscVBitwiseFunction.eval64 op left right)
  | 6 => setRegister (bodyStage s sp saved1 saved2 left right ra op 5) Register.x9 saved1
  | 7 => setRegister (bodyStage s sp saved1 saved2 left right ra op 6) Register.x18 saved2
  | 8 => setRegister (bodyStage s sp saved1 saved2 left right ra op 7) Register.x2 sp
  | _ + 9 => setRegister (bodyStage s sp saved1 saved2 left right ra op 8) Register.nextPC
      (Sail.BitVec.update ra 0 0#1)
termination_by n => n
decreasing_by all_goals omega

def frameInst (op : Op) (i : Fin 9) : instruction :=
  (framedInstructions (OakSailComposition.sailOp op))[i.val]'(by simp [framedInstructions])

def progressionPC (code ra : BitVec 64) (n : Nat) : BitVec 64 :=
  if n < 9 then code + BitVec.ofNat 64 (4*n) else Sail.BitVec.update ra 0 0#1

end OakSailSteppedState
