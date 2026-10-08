import OakSailBridge.FramedDecoded
import Oak.BitwiseSourceLowering
import Oak.RiscVFramedBitwise

/-!
# One Lean 4.33 kernel: admitted source meaning and actual Sail instruction bodies

This imports both the unchanged pinned external decoder/executor (rebuilt under
4.33) and the existing source/typed-expression proofs into one environment.
The projection selects the bitwise instruction and RET from the actual
36-byte admitted compiler function. It deliberately does NOT erase the seven
remaining instructions semantically: their physical memory/state correspondence
is still unproved. The result below concerns only the two supplied bodies.
No fetch/step-loop, executable loader, platform initialization, or production
verification authority follows from this projection.
-/
set_option autoImplicit false
noncomputable section
namespace OakSailComposition
open Oak.BitwiseFunction (Op eval)
open LeanRV64D
open OakSailBridge.BitwiseDecoded

abbrev NativeBytes := List (BitVec 8)

def littleWord (b0 b1 b2 b3 : BitVec 8) : BitVec 32 := b3 ++ b2 ++ b1 ++ b0

def suppliedBytes (bytes : NativeBytes) : SailM ExecutionResult :=
  match bytes with
  | [b0,b1,b2,b3,b4,b5,b6,b7] => bodies (littleWord b0 b1 b2 b3) (littleWord b4 b5 b6 b7)
  | _ => EStateM.throw Sail.Error.Unreachable

/-- Selection is justified byte-for-byte, not by substring interpretation. -/
def projectedBodies (complete : NativeBytes) : NativeBytes :=
  (complete.drop 16).take 4 ++ (complete.drop 32).take 4

theorem projection_exact (op : Op) :
    projectedBodies (Oak.RiscVFramedBitwise.functionBytes op) =
      Oak.RiscVBitwiseFunction.functionBytes op := by cases op <;> rfl

def unpackWords : Nat → NativeBytes → Option (List (BitVec 32))
  | 0, [] => some []
  | n+1, b0 :: b1 :: b2 :: b3 :: rest => do
      let words ← unpackWords n rest
      some (littleWord b0 b1 b2 b3 :: words)
  | _, _ => none

def suppliedDecode (bytes : NativeBytes) : SailM (List instruction) :=
  match unpackWords 9 bytes with
  | some words => decodeWords words
  | none => EStateM.throw Sail.Error.Unreachable

def sailOp : Op → rop | .and => .AND | .or => .OR | .xor => .XOR

theorem unpack_framed (op : Op) :
    unpackWords 9 (Oak.RiscVFramedBitwise.functionBytes op) =
      some (framedWords (Oak.RiscVBitwiseFunction.bodyWord op)) := by cases op <;> rfl

/-- Complete 36-byte decoding, distinct from the two-body execution projection. -/
theorem complete_framed_decoding (op : Op) (s : State) (hc : ConfigOK s) :
    (suppliedDecode (Oak.RiscVFramedBitwise.functionBytes op)).run s =
      .ok (framedInstructions (sailOp op)) s := by
  unfold suppliedDecode
  rw [unpack_framed]
  cases op with
  | and => exact framed_decode s hc _ _ decode_and
  | or => exact framed_decode s hc _ _ decode_or
  | xor => exact framed_decode s hc _ _ decode_xor

def afterBodies (s : State) (value ra : BitVec 64) : State :=
  setRegister (setRegister s Register.x10 value) Register.nextPC (Sail.BitVec.update ra 0 0#1)

theorem exact_byte_execution (op : Op) (s : State) (left right ra next : BitVec 64)
    (hc : ConfigOK s) (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right)
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (ha : ReturnAligned ra) :
    (suppliedBytes (Oak.RiscVBitwiseFunction.functionBytes op)).run s =
      .ok LeanRV64D.Functions.RETIRE_SUCCESS
        (afterBodies s (Oak.RiscVBitwiseFunction.eval64 op left right) ra) := by
  cases op with
  | and => exact and_return s left right ra next hc hl hr hra hn ha
  | or => exact or_return s left right ra next hc hl hr hra hn ha
  | xor => exact xor_return s left right ra next hc hl hr hra hn ha

def acceptsProjection (source : List UInt8) (claim : Oak.BitwiseSource.Decl)
    (complete : NativeBytes) : Bool :=
  decide (Oak.BitwiseSource.parse source = some claim) &&
    Oak.RiscVFramedBitwise.accepts .rv64 .lp64d [32,32] 32 claim.op complete

/-- Source, real 36-byte wrapper identity, and successful external execution of
its explicitly selected two instruction bodies. No whole-wrapper refinement is
asserted by omitting its stack operations. -/
theorem accepted_source_projection {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : NativeBytes} (accepted : acceptsProjection source claim complete = true)
    (left right : BitVec 32) (s : State) (ra next : BitVec 64)
    (hc : ConfigOK s)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (ha : ReturnAligned ra) :
    Oak.BitwiseSource.Means source claim left right (eval claim.op left right) ∧
    (suppliedBytes (projectedBodies complete)).run s =
      .ok LeanRV64D.Functions.RETIRE_SUCCESS
        (afterBodies s (Oak.RiscV.widen 32 false (eval claim.op left right)) ra) := by
  have h : Oak.BitwiseSource.parse source = some claim ∧
      Oak.RiscVFramedBitwise.accepts .rv64 .lp64d [32,32] 32 claim.op complete = true := by
    simpa [acceptsProjection] using accepted
  have grammar := Oak.BitwiseSource.parse_sound h.1
  refine ⟨⟨grammar, Oak.BitwiseSource.grammar_evaluation grammar left right⟩, ?_⟩
  have bytes := ((Oak.RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mp h.2).2.2.2.2
  rw [bytes, projection_exact]
  have result := exact_byte_execution claim.op s _ _ ra next hc hl hr hra hn ha
  rw [Oak.RiscVBitwiseFunction.eval64_widen] at result
  exact result

/-- The same checked declaration also evaluates in Oak's pre-existing typed
expression interpreter; this statement and the Sail result share one kernel. -/
theorem accepted_typed_projection {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : NativeBytes} (accepted : acceptsProjection source claim complete = true)
    (left right : BitVec 32) (fuel : Nat) (s : State) (ra next : BitVec 64)
    (hc : ConfigOK s)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (ha : ReturnAligned ra) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (eval claim.op left right) ∧
    (suppliedBytes (projectedBodies complete)).run s =
      .ok LeanRV64D.Functions.RETIRE_SUCCESS
        (afterBodies s (Oak.RiscV.widen 32 false (eval claim.op left right)) ra) := by
  have result := accepted_source_projection accepted left right s ra next hc hl hr hra hn ha
  have typed := (Oak.BitwiseSourceLowering.means_iff_existing source claim left right
    (eval claim.op left right) fuel).mp result.1
  exact ⟨typed.1, typed.2, result.2⟩

theorem result_observation (s : State) (value : BitVec 32) (ra : BitVec 64) :
    ((afterBodies s (Oak.RiscV.widen 32 false value) ra).regs.get? Register.x10).map
      (fun word => word.truncate 32) = some value := by
  unfold afterBodies
  rw [lookup_set_other _ _ _ _ (by decide), lookup_set_same]
  change some ((Oak.RiscV.widen 32 false value).truncate 32) = _
  rw [Oak.RiscV.widen_truncate_u32]

example (s : State) : (suppliedBytes []).run s = .error Sail.Error.Unreachable s := by rfl
example (s : State) : (suppliedBytes [0x33,0x75,0xb5,0,0x67,0x80,0]).run s =
    .error Sail.Error.Unreachable s := by rfl
example (s : State) : (suppliedBytes [0x33,0x75,0xb5,0,0x67,0x80,0,0,0]).run s =
    .error Sail.Error.Unreachable s := by rfl
example : ReturnAligned 0x2000 := by unfold ReturnAligned; decide +kernel
example : ¬ ReturnAligned 0x2002 := by unfold ReturnAligned; decide +kernel
example : acceptsProjection (Oak.BitwiseSource.render (Oak.BitwiseSource.fixture .and))
    (Oak.BitwiseSource.fixture .and) (Oak.RiscVFramedBitwise.functionBytes .and) = true := by decide +kernel
example : acceptsProjection (Oak.BitwiseSource.render (Oak.BitwiseSource.fixture .and))
    (Oak.BitwiseSource.fixture .and) (Oak.RiscVFramedBitwise.functionBytes .or) = false := by decide +kernel
example : acceptsProjection (Oak.BitwiseSource.render (Oak.BitwiseSource.fixture .and) ++ [32])
    (Oak.BitwiseSource.fixture .and) (Oak.RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
end OakSailComposition
