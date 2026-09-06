import Oak.RecordLayout

namespace Oak.RecordLayoutRefinement

open Oak.RecordLayout

/-! # Compiler correspondence for natural record layout

`semir.NaturalRecordLayout` computes the natural ordered layout with checked
arithmetic: every field offset and end, and the padded final size, must fit
`uint32` (intermediates use `uint64` headroom), or layout fails. This module
transliterates that checked procedure and proves that **whenever it
succeeds, it computes exactly the placement of `Oak.RecordLayout`** — so the
proven layout laws (order/identity preservation, per-field alignment,
non-overlap, aligned final size) transfer to the compiler's output verbatim,
and narrowing the results into `uint32` fields is lossless. Failure is the
only behavior on overflow: no layout value is ever truncated. Duplicate-name
and power-of-two validation are separate guards in the Go procedure; the
semantic-name laws live in `Oak.SemanticRecord`. -/

/-- Go's `^uint32(0)`, the bound the checked procedure narrows into. -/
def maxUint32 : Nat := 4294967295

/-- Transliteration of the checked placement loop of
    `semir.NaturalRecordLayout`: place each field at its aligned offset,
    failing when the offset or the field end exceeds the `uint32` range. -/
def layoutChecked : Nat → List FieldSpec → Option (List PlacedField × Nat)
  | cursor, [] => some ([], cursor)
  | cursor, field :: rest =>
    let offset := alignUp cursor field.alignment
    if offset > maxUint32 then none
    else if offset + field.size > maxUint32 then none
    else
      match layoutChecked (offset + field.size) rest with
      | none => none
      | some (placed, finalCursor) =>
        some ({ identity := field.identity
                size := field.size
                alignment := field.alignment
                offset := offset } :: placed, finalCursor)

/-- Transliteration of the final-size check: tail padding to the record
    alignment must also fit. -/
def finalSizeChecked (fields : List FieldSpec) : Option Nat :=
  match layoutChecked 0 fields with
  | none => none
  | some (_, cursor) =>
    let size := alignUp cursor (maxAlignment fields)
    if size > maxUint32 then none else some size

/-- **Success computes the abstract placement exactly**: the checked
    procedure agrees with `placeFrom`/`cursorAfter`, so every proven law of
    `Oak.RecordLayout` holds of the compiler's accepted layouts. -/
theorem layoutChecked_agrees {fields : List FieldSpec} {cursor : Nat}
    {placed : List PlacedField} {finalCursor : Nat}
    (h : layoutChecked cursor fields = some (placed, finalCursor)) :
    placed = placeFrom cursor fields ∧ finalCursor = cursorAfter cursor fields := by
  induction fields generalizing cursor placed finalCursor with
  | nil =>
    simp [layoutChecked] at h
    simp [placeFrom, cursorAfter, h.1.symm, h.2.symm]
  | cons field rest ih =>
    unfold layoutChecked at h
    by_cases hoff : alignUp cursor field.alignment > maxUint32
    · simp [hoff] at h
    · by_cases hend : alignUp cursor field.alignment + field.size > maxUint32
      · simp [hoff, hend] at h
      · simp only [hoff, hend, if_false] at h
        cases hrec : layoutChecked (alignUp cursor field.alignment + field.size) rest with
        | none => rw [hrec] at h; simp at h
        | some result =>
          obtain ⟨restPlaced, restCursor⟩ := result
          rw [hrec] at h
          simp at h
          obtain ⟨hplaced, hcursor⟩ := ih hrec
          constructor
          · rw [← h.1, placeFrom, hplaced]
          · rw [← h.2, cursorAfter, hcursor]

/-- **Every accepted offset and end fits `uint32`**: narrowing is lossless —
    the fail-closed law of the checked arithmetic. -/
theorem layoutChecked_bounded {fields : List FieldSpec} {cursor : Nat}
    {placed : List PlacedField} {finalCursor : Nat}
    (h : layoutChecked cursor fields = some (placed, finalCursor)) :
    ∀ field ∈ placed, field.offset ≤ maxUint32 ∧ field.offset + field.size ≤ maxUint32 := by
  induction fields generalizing cursor placed finalCursor with
  | nil =>
    simp [layoutChecked] at h
    intro field hmem
    rw [h.1] at hmem
    cases hmem
  | cons field rest ih =>
    unfold layoutChecked at h
    by_cases hoff : alignUp cursor field.alignment > maxUint32
    · simp [hoff] at h
    · by_cases hend : alignUp cursor field.alignment + field.size > maxUint32
      · simp [hoff, hend] at h
      · simp only [hoff, hend, if_false] at h
        cases hrec : layoutChecked (alignUp cursor field.alignment + field.size) rest with
        | none => rw [hrec] at h; simp at h
        | some result =>
          obtain ⟨restPlaced, restCursor⟩ := result
          rw [hrec] at h
          simp at h
          intro placedField hmem
          rw [← h.1] at hmem
          cases hmem with
          | head => constructor <;> simp <;> omega
          | tail _ hrest => exact ih hrec placedField hrest

/-- **The accepted final size is the abstract final size and fits `uint32`**. -/
theorem finalSizeChecked_agrees {fields : List FieldSpec} {size : Nat}
    (h : finalSizeChecked fields = some size) :
    size = finalSize fields ∧ size ≤ maxUint32 := by
  unfold finalSizeChecked at h
  cases hrec : layoutChecked 0 fields with
  | none => rw [hrec] at h; simp at h
  | some result =>
    obtain ⟨placed, cursor⟩ := result
    rw [hrec] at h
    by_cases hbig : alignUp cursor (maxAlignment fields) > maxUint32
    · simp [hbig] at h
    · simp [hbig] at h
      obtain ⟨_, hcursor⟩ := layoutChecked_agrees hrec
      constructor
      · rw [← h, hcursor]
        rfl
      · omega

end Oak.RecordLayoutRefinement
