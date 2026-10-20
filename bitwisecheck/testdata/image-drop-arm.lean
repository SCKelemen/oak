open Oak.BitwiseFunction (eval)
open Oak.BitwiseSource (Decl Means)
theorem weaker_contract {source wasm : Oak.BitwiseSource.Bytes}
    {arm rv : Oak.MinimalELF.Bytes} {d : Decl}
    (h : check source wasm arm rv = some d) :
    ∃ armLoaded rvLoaded,
      ImageBinding .arm64 (fromUInt8 d.name) arm
        (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) armLoaded ∧
      ImageBinding .rv64 (fromUInt8 d.name) rv
        (RiscVFramedBitwise.functionBytes d.op) rvLoaded ∧
      ∀ (left right : BitVec 32) (fuel : Nat)
        (armState : AArch64BitwiseFunction.State),
        (armState.regs 0#5).extractLsb' 0 32 = left →
        (armState.regs 1#5).extractLsb' 0 32 = right →
        ∀ (caller : BitVec 5 → BitVec 64) (memory : AArch64SpillMemory.Memory)
          (mappedRW : Nat → Nat → Bool),
          RiscVFramedBitwise.frameSafe mappedRW
            (rvEntry rvLoaded left right caller memory) = true →
          Means source d left right (eval d.op left right) ∧
          LoweringRefinement.evalX (BitwiseSourceLowering.toExpr d)
            (BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
              some (eval d.op left right) ∧
          BitwiseModule.invokeModule d.name wasm left right = .ok (eval d.op left right) ∧
          armResult arm armLoaded armState = some (eval d.op left right) ∧
          rvResult rv rvLoaded left right caller memory mappedRW = some (eval d.op left right) ∧
          RvContract rv rvLoaded d.op left right caller memory mappedRW := by
  obtain ⟨al, rl, ab, rb, success⟩ := accepted_all_input_success h
  refine ⟨al, rl, ab, rb, ?_⟩
  intro left right fuel armState armLeft armRight caller memory mappedRW safe
  obtain ⟨hs, ht, hw, ha, hr, armContract, rvContract⟩ :=
    success left right fuel armState armLeft armRight caller memory mappedRW safe
  exact ⟨hs, ht, hw, ha, hr, rvContract⟩
theorem all_inputs : type_of% (weaker_contract admitted) := weaker_contract admitted
