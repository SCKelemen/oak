import Oak.RecordLayout

/-!
# Declared record layout specs: packed placement and raised alignment

`docs/spec/40-records.md`: a record declaration may carry an explicit
layout spec — `struct(packed)` places fields densely with no padding, and
`struct(align: N)` raises the record's alignment above its natural
alignment. `semir.RecordLayoutWithSpec` is maintained as the
transliteration of this module:

* packed placement (`placePacked`) puts every field at the running sum of
  the preceding sizes — dense, order- and identity-preserving,
  non-overlapping, with the pre-alignment size exactly the sum of the
  field sizes (no padding anywhere);
* raised placement is *defined* as natural placement (raising alignment
  never moves a field); only the final size changes, to the next multiple
  of the raised alignment, and never below the field cursor.
-/

namespace Oak.LayoutSpec

open Oak.RecordLayout

/-- Packed placement: each field begins exactly where the previous one
    ended. No alignment step, no padding. -/
def placePacked : Nat -> List FieldSpec -> List PlacedField
  | _, [] => []
  | cursor, field :: rest =>
      { identity := field.identity
        size := field.size
        alignment := field.alignment
        offset := cursor } ::
        placePacked (cursor + field.size) rest

/-- Cursor immediately after packed placement of every field. -/
def cursorAfterPacked : Nat -> List FieldSpec -> Nat
  | cursor, [] => cursor
  | cursor, field :: rest => cursorAfterPacked (cursor + field.size) rest

/-- The dense size of a packed record before any explicit alignment. -/
def sumSizes : List FieldSpec -> Nat
  | [] => 0
  | field :: rest => field.size + sumSizes rest

theorem placePacked_preserves_count (cursor : Nat) (fields : List FieldSpec) :
    (placePacked cursor fields).length = fields.length := by
  induction fields generalizing cursor with
  | nil => rfl
  | cons field rest ih => simp [placePacked, ih]

theorem placePacked_preserves_identity_order (cursor : Nat) (fields : List FieldSpec) :
    (placePacked cursor fields).map PlacedField.identity = fields.map FieldSpec.identity := by
  induction fields generalizing cursor with
  | nil => rfl
  | cons field rest ih => simp [placePacked, ih]

/-- Packed fields are contiguous: each field ends exactly where the next
    begins. This is stronger than `NonOverlapping` (which it implies):
    packing admits no padding at all. -/
def Dense : List PlacedField -> Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first.offset + first.size = second.offset ∧ Dense (second :: rest)

theorem placePacked_dense (cursor : Nat) (fields : List FieldSpec) :
    Dense (placePacked cursor fields) := by
  induction fields generalizing cursor with
  | nil => simp [placePacked, Dense]
  | cons field rest ih =>
      cases rest with
      | nil => simp [placePacked, Dense]
      | cons next tail =>
          exact ⟨rfl, ih (cursor + field.size)⟩

theorem dense_nonoverlapping (fields : List PlacedField) :
    Dense fields -> NonOverlapping fields := by
  induction fields with
  | nil => intro _; trivial
  | cons first rest ih =>
      cases rest with
      | nil => intro _; trivial
      | cons second tail =>
          intro h
          exact ⟨Nat.le_of_eq h.1, ih h.2⟩

/-- The cursor after packed placement advances by exactly the sum of the
    field sizes: packing wastes nothing. -/
theorem packed_cursor_exact (cursor : Nat) (fields : List FieldSpec) :
    cursorAfterPacked cursor fields = cursor + sumSizes fields := by
  induction fields generalizing cursor with
  | nil => simp [cursorAfterPacked, sumSizes]
  | cons field rest ih =>
      simp only [cursorAfterPacked, sumSizes]
      rw [ih]
      omega

/-- Raised placement is natural placement: the spec *defines* an explicit
    alignment as changing only the record's alignment and tail padding.
    The transliterated implementation computes the natural layout and then
    rewrites size and alignment alone, so "raising alignment never moves a
    field" holds by this definition — the theorem below pins the API to it. -/
def raisedPlacement (fields : List FieldSpec) (_align : Nat) : List PlacedField :=
  placeFrom 0 fields

theorem raise_keeps_offsets (fields : List FieldSpec) (align : Nat) :
    raisedPlacement fields align = placeFrom 0 fields := rfl

/-- Raised final size: the natural cursor rounded to the raised alignment
    (the raise is only legal at or above the natural alignment, which the
    checked implementation enforces). -/
def raisedSize (fields : List FieldSpec) (align : Nat) : Nat :=
  alignUp (cursorAfter 0 fields) align

theorem raisedSize_aligned (fields : List FieldSpec) (align : Nat)
    (halign : 0 < align) : raisedSize fields align % align = 0 :=
  alignUp_aligned _ _ halign

theorem raisedSize_covers_cursor (fields : List FieldSpec) (align : Nat) :
    cursorAfter 0 fields ≤ raisedSize fields align :=
  alignUp_ge _ _

/-! ## The `no_padding` claim

`struct(no_padding)` (docs/spec/40-records.md §6a) arranges nothing: the
placement is the natural one. It claims that placement is already dense
and that the final size is the sum of the field sizes — every byte of the
record is a field byte. `semir.checkNoPadding` decides exactly this
predicate over the computed layout. -/

/-- The claim `struct(no_padding)` makes about a field list. -/
def NoPadding (fields : List FieldSpec) : Prop :=
  Dense (placeFrom 0 fields) ∧ finalSize fields = sumSizes fields

theorem alignUp_zero (alignment : Nat) : alignUp 0 alignment = 0 := by
  simp [alignUp]

/-- A dense natural placement from a cursor the first field accepts is the
    packed placement: every offset is the running sum of the preceding
    sizes. `no_padding` therefore buys packed's bytes while every field
    keeps its natural alignment — the reason to prefer it over `packed`
    for a wire header. -/
theorem dense_placeFrom_eq_packed (cursor : Nat) (fields : List FieldSpec)
    (hstart : ∀ f, fields.head? = some f → alignUp cursor f.alignment = cursor)
    (hdense : Dense (placeFrom cursor fields)) :
    placeFrom cursor fields = placePacked cursor fields := by
  induction fields generalizing cursor with
  | nil => rfl
  | cons field rest ih =>
      have hoff : alignUp cursor field.alignment = cursor := hstart field rfl
      cases rest with
      | nil => simp [placeFrom, placePacked, hoff]
      | cons next tail =>
          have hnext : alignUp (cursor + field.size) next.alignment = cursor + field.size := by
            simp only [placeFrom, hoff, Dense] at hdense
            exact hdense.1.symm
          have htail : Dense (placeFrom (cursor + field.size) (next :: tail)) := by
            simp only [placeFrom, hoff, Dense] at hdense
            simp only [placeFrom]
            exact hdense.2
          have hrest := ih (cursor + field.size)
            (fun g hg => by
              simp only [List.head?_cons, Option.some.injEq] at hg
              subst hg
              exact hnext)
            htail
          simp only [placeFrom, placePacked, hoff]
          exact congrArg _ hrest

/-- The `no_padding` claim places the record exactly as `packed` would. -/
theorem noPadding_placement (fields : List FieldSpec) (h : NoPadding fields) :
    placeFrom 0 fields = placePacked 0 fields :=
  dense_placeFrom_eq_packed 0 fields (fun f _ => alignUp_zero f.alignment) h.1

end Oak.LayoutSpec
