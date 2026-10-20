import OakSailClockedPrefix
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace OakSailClockedSource
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode OakSailSteppedState OakSailSteppedFrame
open OakSailClockTick OakSailPlatformCallback OakSailClockedPrefix

/-- Restricted original source and every compiler byte bind to nine bounded
iterations of the kernel-identified platform callback. This is not an execution
or termination claim for the opaque full platform loop. -/
theorem accepted_typed_clocked_prefix {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : List (BitVec 8)}
    (accepted : OakSailFramedComposition.acceptsFrame source claim complete = true)
    (left right : BitVec 32) (fuel : Nat) (s : State)
    (sp saved1 saved2 ra code : BitVec 64) (step : Nat) (c t d : BitVec 64)
    (regions : List PMA_Region) (first second : PMA_Region)
    (codeRegion : Fin 9 → PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (hclock : ClockProfile s c t d) (hdeadline : t.toNat + 4 < d.toNat)
    (ha : OakSailFramedComposition.FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra) (halign : ReturnAligned ra)
    (hpc : s.regs.get? Register.PC = some code)
    (hn : s.regs.get? Register.nextPC = some code)
    (hi : s.regs.get? Register.minstret_increment = some false)
    (placed : BytesAt s code.toNat complete) (aligned : code.toNat % 4 = 0)
    (bounded : code.toNat + 36 ≤ 2^64)
    (hsep : CodeStackDisjoint code (sp-96#64))
    (hexec : ∀ i : Fin 9, ExecutableRegion regions (codePC code i) (codeRegion i))
    (hlow : ∀ i : Fin 9, LowCodeRAM (codePC code i)) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    (boundedPlatform 9 (0,step)).run s = .ok (1,step)
      (clockState (finalSteppedState s sp saved1 saved2
        (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) ra)
        (c+4#64) (t+4#64)) := by
  have checked : Oak.BitwiseSource.parse source = some claim ∧
      Oak.RiscVFramedBitwise.accepts .rv64 .lp64d [32,32] 32 claim.op complete = true := by
    simpa [OakSailFramedComposition.acceptsFrame, OakSailComposition.acceptsProjection] using accepted
  have grammar := Oak.BitwiseSource.parse_sound checked.1
  have typed := (Oak.BitwiseSourceLowering.means_iff_existing source claim left right
    (Oak.BitwiseFunction.eval claim.op left right) fuel).mp
      ⟨grammar, Oak.BitwiseSource.grammar_evaluation grammar left right⟩
  have bytes := ((Oak.RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mp checked.2).2.2.2.2
  have hcode : FrameCodeAt s code claim.op :=
    ⟨by simpa only [bytes] using placed, aligned, bounded⟩
  have run := clocked_nine_steps claim.op s sp saved1 saved2 (Oak.RiscV.widen 32 false left)
    (Oak.RiscV.widen 32 false right) ra code step c t d regions first second codeRegion
    hc hcfg hp hclock hdeadline ha hsp h1 h2 hl hr hra halign hcode hsep hexec hlow
  rw [control_self s code hpc hn hi, Oak.RiscVBitwiseFunction.eval64_widen] at run
  exact ⟨grammar, typed.2, run⟩

end OakSailClockedSource
