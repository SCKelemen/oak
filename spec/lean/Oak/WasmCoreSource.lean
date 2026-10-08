import Oak.WasmCoreBinary

/-! End-to-end success inside the pinned, manually transcribed restricted Core
formalization. This theorem does not prove its transcription/importer correct,
or verify the production compiler/runtime. See the explicit trust ledger. -/
set_option autoImplicit false
namespace Oak.WasmCoreSource
open Oak.BitwiseFunction
open Oak.WasmCoreModule

/-- One original source, one complete actual Wasm byte string, any pre-existing
store and all 2^64 input pairs. Validation/instantiation/invoke premises are
constructed proofs, not assumptions of a theorem named after the desired result. -/
theorem source_to_core {source bytes : BitwiseSource.Bytes} {claim : BitwiseSource.Decl}
    (accepted : BitwiseSource.accepts source claim .wasm .wasmLocals bytes = true)
    (s : Store) (a b : BitVec 32) (fuel : Nat) :
    BitwiseSource.Grammar source claim ∧
    LoweringRefinement.evalX (BitwiseSourceLowering.toExpr claim)
      (BitwiseSourceLowering.inputs a b) (fun _ => 0) fuel = some (eval claim.op a b) ∧
    WasmCoreBinary.BinaryModule bytes (module claim.name claim.op) ∧
    ModuleOk (module claim.name claim.op) [closedType] ∧
    Instantiation s (module claim.name claim.op) (allocate s claim.name claim.op)
      (allocatedInstance s claim.name) [] ∧
    exportAddress (allocatedInstance s claim.name) claim.name = some s.functions.length ∧
    Invoke (allocate s claim.name claim.op) s.functions.length [a,b]
      (.call [a,b] (.function s.functions.length) closedType) ∧
    CallSteps (allocate s claim.name claim.op)
      (.call [a,b] (.function s.functions.length) closedType)
      (.result [eval claim.op a b]) ∧
    WasmCoreBitwiseProjection.NumericResult (WasmCoreBitwiseProjection.binop claim.op)
      a b (eval claim.op a b) ∧
    BitwiseModule.invokeModule claim.name bytes a b = .ok (eval claim.op a b) := by
  have sourceResult := BitwiseSourceLowering.accepted_module_existing accepted a b fuel
  have admitted := (Bool.and_eq_true_iff.mp accepted).2
  have call := invocation_success s claim.name claim.op a b
  refine ⟨sourceResult.1, sourceResult.2.1, WasmCoreBinary.admitted_binary admitted,
    module_ok _ _, instantiate _ _ _, export_resolves _ _, call.1, call.2, ?_, sourceResult.2.2⟩
  rw [← WasmCoreBitwiseProjection.numeric_agrees]
  exact WasmCoreBitwiseProjection.numeric_bits _ _ _

end Oak.WasmCoreSource
