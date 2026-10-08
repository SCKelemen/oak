import OakSailFetchedCode
import OakSailBridge.FetchedInstruction

/-! Actual fetch of each word of the admitted full compiler body, including
preservation across the proven stack writes. This is not a fetched execution
loop: the caller explicitly chooses each PC, and no PC ticking is inferred. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailFetchedFrame
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode
open Oak.BitwiseFunction (Op)
attribute [local irreducible] store64

theorem memoryConfig_pc (s : State) (pc : BitVec 64) (regions : List PMA_Region)
    (hc : MemoryConfig s regions) : MemoryConfig (setRegister s Register.PC pc) regions := by
  rcases hc with ⟨hp,hm,hmask,hr,ht,hc,ha⟩
  constructor <;> simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem frame_word_not_compressed (op : Op) (i : Fin 9) :
    isRVC (Sail.BitVec.extractLsb (frameWord op i) 15 0) = false := by
  have hi := i.isLt
  have ci : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
  rcases ci with hi|hi|hi|hi|hi|hi|hi|hi|hi <;>
    cases op <;> simp [frameWord, hi, framedWords] <;> decide +kernel

/-- All four bytes at each of the nine concrete addresses feed unchanged
external fetch. The whole body is present in RAM, not a substring claim. -/
theorem every_frame_word_fetch (s : State) (code : BitVec 64) (op : Op)
    (regions : List PMA_Region) (codeRegion : Fin 9 → PMA_Region)
    (hc : MemoryConfig s regions) (hm : s.regs.get? Register.misa = some misaRV64I)
    (hcode : FrameCodeAt s code op)
    (hexec : ∀ i : Fin 9, ExecutableRegion regions (codePC code i) (codeRegion i))
    (hlow : ∀ i : Fin 9, LowCodeRAM (codePC code i)) (i : Fin 9) :
    (fetch ()).run (setRegister s Register.PC (codePC code i)) =
      .ok (.F_Base (frameWord op i)) (setRegister s Register.PC (codePC code i)) := by
  apply fetch_base_run _ (codePC code i) (frameWord op i) regions (codeRegion i)
    (memoryConfig_pc s _ regions hc)
  · simpa [setRegister, Std.ExtDHashMap.get?_insert] using hm
  · exact lookup_set_same _ _ _
  · exact codePC_aligned code i hcode.2.2 hcode.2.1
  · exact hexec i
  · exact hlow i
  · exact codePC_bytes s code op i hcode
  · exact frame_word_not_compressed op i

/-- The exact two saved words cannot change any fetched code word under the
stated byte-range separation. This does not replace actual step sequencing. -/
theorem every_frame_word_fetch_after_stores (s : State)
    (code base saved1 saved2 result target : BitVec 64) (op : Op)
    (regions : List PMA_Region) (codeRegion : Fin 9 → PMA_Region)
    (hc : MemoryConfig s regions) (hm : s.regs.get? Register.misa = some misaRV64I)
    (hcode : FrameCodeAt s code op) (hsep : CodeStackDisjoint code base)
    (hexec : ∀ i : Fin 9, ExecutableRegion regions (codePC code i) (codeRegion i))
    (hlow : ∀ i : Fin 9, LowCodeRAM (codePC code i)) (i : Fin 9) :
    (fetch ()).run (setRegister (finalFrameState s base saved1 saved2 result target)
      Register.PC (codePC code i)) =
      .ok (.F_Base (frameWord op i))
        (setRegister (finalFrameState s base saved1 saved2 result target) Register.PC (codePC code i)) := by
  apply every_frame_word_fetch _ code op regions codeRegion
    (memoryConfig_finalFrameState s regions base saved1 saved2 result target hc)
  · rw [finalFrameState_register_other _ _ _ _ _ _ Register.misa (by decide) (by decide)]
    exact hm
  · exact frameCodeAt_finalState s code base saved1 saved2 result target op hcode hsep
  · exact hexec
  · exact hlow

/-- Bind original restricted source and every actual compiler-body byte to
successful fetch at each represented PC. ELF loading and PC progression are
not inferred from the abstract byte-placement premise. -/
theorem accepted_source_word_fetch {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : List (BitVec 8)}
    (accepted : OakSailFramedComposition.acceptsFrame source claim complete = true)
    (s : State) (code : BitVec 64) (regions : List PMA_Region)
    (codeRegion : Fin 9 → PMA_Region) (hc : MemoryConfig s regions)
    (hm : s.regs.get? Register.misa = some misaRV64I)
    (placed : BytesAt s code.toNat complete) (aligned : code.toNat % 4 = 0)
    (bounded : code.toNat + 36 ≤ 2^64)
    (hexec : ∀ i : Fin 9, ExecutableRegion regions (codePC code i) (codeRegion i))
    (hlow : ∀ i : Fin 9, LowCodeRAM (codePC code i)) :
    Oak.BitwiseSource.Grammar source claim ∧
    ∀ i : Fin 9, (fetch ()).run (setRegister s Register.PC (codePC code i)) =
      .ok (.F_Base (frameWord claim.op i)) (setRegister s Register.PC (codePC code i)) := by
  have acceptedParts : Oak.BitwiseSource.parse source = some claim ∧
      Oak.RiscVFramedBitwise.accepts .rv64 .lp64d [32,32] 32 claim.op complete = true := by
    simpa [OakSailFramedComposition.acceptsFrame, OakSailComposition.acceptsProjection] using accepted
  have bytes := ((Oak.RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mp acceptedParts.2).2.2.2.2
  refine ⟨Oak.BitwiseSource.parse_sound acceptedParts.1, ?_⟩
  intro i
  apply every_frame_word_fetch s code claim.op regions codeRegion hc hm
  · exact ⟨by simpa only [bytes] using placed, aligned, bounded⟩
  · exact hexec
  · exact hlow

/-- Original typed expression meaning and actual external fetch are checked
in this project's single kernel. PC sequencing is deliberately not a conclusion. -/
theorem accepted_typed_word_fetch {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : List (BitVec 8)}
    (accepted : OakSailFramedComposition.acceptsFrame source claim complete = true)
    (left right : BitVec 32) (fuel : Nat)
    (s : State) (code : BitVec 64) (regions : List PMA_Region)
    (codeRegion : Fin 9 → PMA_Region) (hc : MemoryConfig s regions)
    (hm : s.regs.get? Register.misa = some misaRV64I)
    (placed : BytesAt s code.toNat complete) (aligned : code.toNat % 4 = 0)
    (bounded : code.toNat + 36 ≤ 2^64)
    (hexec : ∀ i : Fin 9, ExecutableRegion regions (codePC code i) (codeRegion i))
    (hlow : ∀ i : Fin 9, LowCodeRAM (codePC code i)) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    ∀ i : Fin 9, (fetch ()).run (setRegister s Register.PC (codePC code i)) =
      .ok (.F_Base (frameWord claim.op i)) (setRegister s Register.PC (codePC code i)) := by
  have h := accepted_source_word_fetch accepted s code regions codeRegion hc hm
    placed aligned bounded hexec hlow
  have typed := (Oak.BitwiseSourceLowering.means_iff_existing source claim left right
    (Oak.BitwiseFunction.eval claim.op left right) fuel).mp
      ⟨h.1, Oak.BitwiseSource.grammar_evaluation h.1 left right⟩
  exact ⟨h.1, typed.2, h.2⟩

end OakSailFetchedFrame

