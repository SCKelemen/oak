import Oak.BitwiseSource
import Oak.AArch64BitwiseFunction
import Oak.RiscVFramedBitwise

/-!
# Source-bound three-target function-result parity

The source and Wasm module are consumed in full. Native byte lists must be
complete extracted function bodies, not whole ELF images: native symbol lookup,
relocation, entry-address selection, instruction fetch and external ISA models
remain separate obligations. RV64 explicitly requires the mapped 96-byte stack
frame premise of its actual 36-byte production wrapper. This never licenses a
production verified flag.
-/
set_option autoImplicit false
namespace Oak.BitwiseSourceParity
open Oak.BitwiseFunction
open Oak.BitwiseSource (Bytes Decl Means)

/-- Independent admission of one original source and all three actual byte lists.
Each target's own ABI/decoder is used; the RV64 leaf approximation is not used. -/
def accepts (source : Bytes) (claim : Decl) (wasm arm : Bytes)
    (rv : Oak.RiscVBitwiseFunction.Bytes) : Bool :=
  BitwiseSource.accepts source claim .wasm .wasmLocals wasm &&
  AArch64BitwiseFunction.accepts .arm64 .aapcs64U32 [32,32] 32 claim.op arm &&
  RiscVFramedBitwise.accepts .rv64 .lp64d [32,32] 32 claim.op rv

def armResult (bytes : Bytes) (state : AArch64BitwiseFunction.State) : Option (BitVec 32) :=
  (AArch64BitwiseFunction.invoke bytes state).map
    (fun after => (after.regs 0#5).truncate 32)

def rvResult (bytes : Oak.RiscVBitwiseFunction.Bytes)
    (state : RiscVFramedBitwise.State) (mappedRW : Nat → Nat → Bool) : Option (BitVec 32) :=
  (RiscVFramedBitwise.invoke mappedRW bytes state).map
    (fun after => (RiscVCallExecution.read after.core 10).truncate 32)

/-- Successful full-u32 observations on all targets, quantified over every input
pair and caller state satisfying the explicit ABI/frame preconditions. -/
theorem accepted_all_input_success {source wasm arm : Bytes} {claim : Decl}
    {rv : Oak.RiscVBitwiseFunction.Bytes}
    (accepted : accepts source claim wasm arm rv = true)
    (left right : BitVec 32) (armState : AArch64BitwiseFunction.State)
    (armLeft : (armState.regs 0#5).extractLsb' 0 32 = left)
    (armRight : (armState.regs 1#5).extractLsb' 0 32 = right)
    (pc : BitVec 64) (caller : BitVec 5 → BitVec 64)
    (memory : Oak.AArch64SpillMemory.Memory) (mappedRW : Nat → Nat → Bool)
    (safe : RiscVFramedBitwise.frameSafe mappedRW
      (RiscVFramedBitwise.entry left right pc caller memory) = true) :
    Means source claim left right (eval claim.op left right) ∧
    BitwiseModule.invokeModule claim.name wasm left right = .ok (eval claim.op left right) ∧
    armResult arm armState = some (eval claim.op left right) ∧
    rvResult rv (RiscVFramedBitwise.entry left right pc caller memory) mappedRW =
      some (eval claim.op left right) := by
  obtain ⟨both, rvAccepted⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨sourceAccepted, armAccepted⟩ := Bool.and_eq_true_iff.mp both
  have sourceResult := BitwiseSource.accepted_source_to_module sourceAccepted left right
  refine ⟨sourceResult.1, sourceResult.2, ?_, ?_⟩
  · unfold armResult
    rw [AArch64BitwiseFunction.accepted_execution armAccepted]
    change some (((AArch64BitwiseFunction.returned claim.op armState).regs 0#5).truncate 32) = _
    rw [AArch64BitwiseFunction.result_u32 claim.op armState left right armLeft armRight]
    simp
  · have bytes := ((RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mp rvAccepted).2.2.2.2
    rw [bytes]
    exact RiscVFramedBitwise.all_input_result claim.op left right pc caller memory mappedRW safe

/-- Native byte identity is checked in addition to source/module identity. -/
theorem accepted_native_bytes {source wasm arm : Bytes} {claim : Decl}
    {rv : Oak.RiscVBitwiseFunction.Bytes}
    (h : accepts source claim wasm arm rv = true) :
    arm = AArch64BitwiseFunction.functionBytes claim.op ∧
    rv = RiscVFramedBitwise.functionBytes claim.op := by
  obtain ⟨both, rvAccepted⟩ := Bool.and_eq_true_iff.mp h
  have armAccepted := (Bool.and_eq_true_iff.mp both).2
  have armFields :
      .arm64 = Target.arm64 ∧ AArch64BitwiseFunction.ABI.aapcs64U32 = .aapcs64U32 ∧
      [32,32] = [32,32] ∧ 32 = 32 ∧ arm = AArch64BitwiseFunction.functionBytes claim.op := by
    simpa [AArch64BitwiseFunction.accepts] using armAccepted
  exact ⟨armFields.2.2.2.2,
    ((RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mp rvAccepted).2.2.2.2⟩

theorem fixture_admitted (op : Op) :
    accepts (BitwiseSource.render (BitwiseSource.fixture op)) (BitwiseSource.fixture op)
      (BitwiseModule.moduleBytes op) (AArch64BitwiseFunction.functionBytes op)
      (RiscVFramedBitwise.functionBytes op) = true := by
  cases op <;> decide +kernel

example : accepts (BitwiseSource.render (BitwiseSource.fixture .and)) (BitwiseSource.fixture .and)
    (BitwiseModule.moduleBytes .or) (AArch64BitwiseFunction.functionBytes .and)
    (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
example : accepts (BitwiseSource.render (BitwiseSource.fixture .and)) (BitwiseSource.fixture .and)
    (BitwiseModule.moduleBytes .and) (AArch64BitwiseFunction.functionBytes .xor)
    (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
example : accepts (BitwiseSource.render (BitwiseSource.fixture .and)) (BitwiseSource.fixture .and)
    (BitwiseModule.moduleBytes .and) (AArch64BitwiseFunction.functionBytes .and)
    (RiscVFramedBitwise.functionBytes .or) = false := by decide +kernel
example : accepts (BitwiseSource.render (BitwiseSource.fixture .and)) (BitwiseSource.fixture .and)
    (BitwiseModule.moduleBytes .and) (AArch64BitwiseFunction.functionBytes .and)
    (RiscVBitwiseFunction.functionBytes .and) = false := by decide +kernel
example : accepts (BitwiseSource.render (BitwiseSource.fixture .and)) (BitwiseSource.fixture .and)
    (BitwiseModule.moduleBytes .and) (AArch64BitwiseFunction.functionBytes .and ++ [0])
    (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel

end Oak.BitwiseSourceParity
