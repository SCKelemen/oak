import OakSailEntrySource
import Oak.StrictImageEntryContract

/-!
# One-way strict bundle admission to the existing entry consumer

This module belongs to the required pinned Lean 4.29 Sail build and separate
audit. The standalone Lean 4.33 diagnostic reuses this proof body against
mechanically extracted pure admission expressions only.
That test does not import or verify the actual Sail consumer or its execution.
No reverse implication, public checked capability, or execution claim is added.
-/
set_option autoImplicit false
namespace OakSailStrictImageEntry

/-- One-way admission from the original strict bundle and explicit initial SP.
The image, parsed declaration, decoded body and startup stay the same values. -/
theorem strict_source_entry_admitted
    {source wasm : List UInt8} {arm image : Oak.MinimalELF.Bytes}
    {d : Oak.BitwiseSource.Decl} {sp : Nat}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some d)
    (stack_lower : 96 ≤ sp) (stack_upper : sp ≤ 0x02000000)
    (stack_aligned : sp % 16 = 0)
    (stack_separate : 65600 ≤ sp - 96 ∨ sp ≤ 65536) :
    OakSailEntrySource.acceptsEntry source d image sp = true := by
  obtain ⟨parsed, framed, body, prefixFacts, layout⟩ :=
    Oak.StrictImageEntryContract.entry_preconditions checked stack_lower stack_upper
      stack_aligned stack_separate
  simp only [OakSailEntrySource.acceptsEntry, OakSailImageSource.accepts,
    OakSailFramedComposition.acceptsFrame, OakSailComposition.acceptsProjection,
    OakSailImageLoad.acceptsImage, OakSailImageLoad.ImageLayout,
    OakSailEntryInstructions.startupBytes, Bool.and_eq_true_iff, decide_eq_true_eq]
  exact ⟨⟨⟨parsed, framed⟩, ⟨body, by exact decide_eq_true layout⟩⟩, prefixFacts⟩

/-- Smallest actual consumer interface: retain its existing layout premise.
No new production predicate or source extraction is necessary for composition. -/
theorem strict_source_entry_admitted_of_layout
    {source wasm : List UInt8} {arm image : Oak.MinimalELF.Bytes}
    {d : Oak.BitwiseSource.Decl} {sp : Nat}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some d)
    (layout : OakSailImageLoad.ImageLayout image sp) :
    OakSailEntrySource.acceptsEntry source d image sp = true := by
  obtain ⟨_, stack_lower, stack_upper, stack_aligned, stack_separate⟩ := layout
  obtain ⟨_, _, _, _, _, hs, _⟩ :=
    Oak.StrictImageEntryContract.source_entry_binding checked
  apply strict_source_entry_admitted checked stack_lower stack_upper stack_aligned
  simpa only [hs] using stack_separate

end OakSailStrictImageEntry
