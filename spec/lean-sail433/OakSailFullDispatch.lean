import OakSailComposition
import OakSailBridge.BitwiseDispatchAgreement

/-! The same supplied-body result through the full generated `execute`
dispatcher. Unlike the narrow body theorem, this closure includes the export's
uninterpreted primitives from other dispatcher branches. The broader audit is
mandatory for this claim. This still does not execute the seven projected-out
wrapper instructions or the fetch/step loop. -/
set_option autoImplicit false
noncomputable section
namespace OakSailFullDispatch
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded
open OakSailComposition
open Oak.BitwiseFunction (Op eval)

def decodedFull (word : BitVec 32) : SailM ExecutionResult := do
  let i ← encdec_backwards word
  execute i

theorem full_and : decodedFull 0x00b57533 = decoded 0x00b57533 := by
  simp only [decodedFull, decoded, decode_and, decoderChecks, bind_assoc,
    pure_bind, generated_rtype_dispatch]
theorem full_or : decodedFull 0x00b56533 = decoded 0x00b56533 := by
  simp only [decodedFull, decoded, decode_or, decoderChecks, bind_assoc,
    pure_bind, generated_rtype_dispatch]
theorem full_xor : decodedFull 0x00b54533 = decoded 0x00b54533 := by
  simp only [decodedFull, decoded, decode_xor, decoderChecks, bind_assoc,
    pure_bind, generated_rtype_dispatch]
theorem full_ret : decodedFull 0x00008067 = decoded 0x00008067 := by
  simp only [decodedFull, decoded, decode_ret, decoderChecks, bind_assoc,
    pure_bind, generated_jalr_dispatch]

def fullBodies (first second : BitVec 32) : SailM ExecutionResult := do
  let result ← decodedFull first
  match result with
  | .Retire_Success () => decodedFull second
  | other => pure other

def suppliedFullBytes (bytes : NativeBytes) : SailM ExecutionResult :=
  match bytes with
  | [b0,b1,b2,b3,b4,b5,b6,b7] => fullBodies (littleWord b0 b1 b2 b3) (littleWord b4 b5 b6 b7)
  | _ => EStateM.throw Sail.Error.Unreachable

theorem full_leaf (op : Op) :
    suppliedFullBytes (Oak.RiscVBitwiseFunction.functionBytes op) =
      suppliedBytes (Oak.RiscVBitwiseFunction.functionBytes op) := by
  cases op with
  | and =>
      change fullBodies 0x00b57533 0x00008067 = bodies 0x00b57533 0x00008067
      simp only [fullBodies, bodies, full_and, full_ret]
      rfl
  | or =>
      change fullBodies 0x00b56533 0x00008067 = bodies 0x00b56533 0x00008067
      simp only [fullBodies, bodies, full_or, full_ret]
      rfl
  | xor =>
      change fullBodies 0x00b54533 0x00008067 = bodies 0x00b54533 0x00008067
      simp only [fullBodies, bodies, full_xor, full_ret]
      rfl

theorem accepted_source_full_projection {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : NativeBytes} (accepted : acceptsProjection source claim complete = true)
    (left right : BitVec 32) (s : State) (ra next : BitVec 64)
    (hc : ConfigOK s)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (ha : ReturnAligned ra) :
    Oak.BitwiseSource.Means source claim left right (eval claim.op left right) ∧
    (suppliedFullBytes (projectedBodies complete)).run s =
      .ok RETIRE_SUCCESS
        (afterBodies s (Oak.RiscV.widen 32 false (eval claim.op left right)) ra) := by
  have result := accepted_source_projection accepted left right s ra next hc hl hr hra hn ha
  have checked : Oak.RiscVFramedBitwise.accepts .rv64 .lp64d [32,32] 32 claim.op complete = true := by
    have := (Bool.and_eq_true_iff.mp accepted).2
    exact this
  have bytes := ((Oak.RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mp checked).2.2.2.2
  refine ⟨result.1, ?_⟩
  rw [bytes, projection_exact, full_leaf]
  simpa only [bytes, projection_exact] using result.2
end OakSailFullDispatch
