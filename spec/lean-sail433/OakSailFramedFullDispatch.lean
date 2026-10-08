import OakSailFramedComposition

/-! Complete nine-instruction supplied execution through the unrestricted
pinned dispatcher. Its axiom closure includes the model's opaque primitives
from unused dispatcher branches; audit this separately from the bounded driver. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace OakSailFramedFullDispatch
open LeanRV64D LeanRV64D.Functions
open Oak.BitwiseFunction (Op eval)
open OakSailBridge.BitwiseDecoded
open OakSailComposition (sailOp unpackWords)
open OakSailFramedComposition

def runGeneratedInstructions : List instruction → SailM ExecutionResult
  | [] => pure RETIRE_SUCCESS
  | i :: rest => do
      let result ← execute i
      match result with
      | .Retire_Success () => runGeneratedInstructions rest
      | other => pure other

theorem generated_frame_agreement (op : Op) :
    runGeneratedInstructions (framedInstructions (sailOp op)) =
      runFrameInstructions (framedInstructions (sailOp op)) := by rfl

def suppliedGeneratedFrame (bytes : List (BitVec 8)) : SailM ExecutionResult :=
  match unpackWords 9 bytes with
  | none => EStateM.throw Sail.Error.Unreachable
  | some words => do
      let instructions ← decodeWords words
      runGeneratedInstructions instructions

theorem full_frame_agreement (op : Op) (s : State) (hc : ConfigOK s) :
    (suppliedGeneratedFrame (Oak.RiscVFramedBitwise.functionBytes op)).run s =
      (suppliedFrame (Oak.RiscVFramedBitwise.functionBytes op)).run s := by
  have hd : (decodeWords (framedWords (Oak.RiscVBitwiseFunction.bodyWord op))).run s =
      .ok (framedInstructions (sailOp op)) s := by
    cases op with
    | and => exact framed_decode s hc _ _ decode_and
    | or => exact framed_decode s hc _ _ decode_or
    | xor => exact framed_decode s hc _ _ decode_xor
  unfold suppliedGeneratedFrame suppliedFrame
  rw [OakSailComposition.unpack_framed]
  rw [bind_run_ok _ _ hd, bind_run_ok _ _ hd, generated_frame_agreement]

theorem accepted_typed_full_frame {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : List (BitVec 8)} (accepted : acceptsFrame source claim complete = true)
    (left right : BitVec 32) (fuel : Nat) (s : State)
    (sp saved1 saved2 ra next : BitVec 64)
    (regions : List PMA_Region) (first second : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s)
    (ha : FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (halign : ReturnAligned ra) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (eval claim.op left right) ∧
    (suppliedGeneratedFrame complete).run s =
      .ok RETIRE_SUCCESS (finalFrameState s (sp - (96#64)) saved1 saved2
        (Oak.RiscV.widen 32 false (eval claim.op left right)) (Sail.BitVec.update ra 0 0#1)) := by
  have run := accepted_typed_frame accepted left right fuel s sp saved1 saved2 ra next regions
    first second hc hcfg ha hsp h1 h2 hl hr hra hn halign
  have checked : Oak.RiscVFramedBitwise.accepts .rv64 .lp64d [32,32] 32 claim.op complete = true :=
    (Bool.and_eq_true_iff.mp accepted).2
  have bytes := ((Oak.RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mp checked).2.2.2.2
  refine ⟨run.1, run.2.1, ?_⟩
  rw [bytes, full_frame_agreement claim.op s hcfg]
  simpa only [bytes] using run.2.2

end OakSailFramedFullDispatch
