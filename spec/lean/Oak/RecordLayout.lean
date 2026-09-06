namespace Oak.RecordLayout

structure FieldSpec where
  identity : Nat
  size : Nat
  alignment : Nat
  deriving DecidableEq, Repr

structure PlacedField where
  identity : Nat
  size : Nat
  alignment : Nat
  offset : Nat
  deriving DecidableEq, Repr

/-- Arithmetic form of natural alignment. Zero alignment is treated as invalid
    by the surrounding specification and left unchanged here. -/
def alignUp (value alignment : Nat) : Nat :=
  if alignment = 0 then value
  else
    let remainder := value % alignment
    if remainder = 0 then value
    else value + (alignment - remainder)

theorem alignUp_ge (value alignment : Nat) : value ≤ alignUp value alignment := by
  unfold alignUp
  split
  · exact Nat.le_refl value
  · split
    · exact Nat.le_refl value
    · exact Nat.le_add_right value _

theorem alignUp_aligned (value alignment : Nat) (halignment : 0 < alignment) :
    alignUp value alignment % alignment = 0 := by
  unfold alignUp
  have hne : alignment ≠ 0 := Nat.ne_of_gt halignment
  simp [hne]
  split hrem
  · exact hrem
  · have hlt : value % alignment < alignment := Nat.mod_lt value halignment
    have hpos : 0 < value % alignment := Nat.pos_of_ne_zero hrem
    have hpadlt : alignment - value % alignment < alignment := by omega
    rw [Nat.add_mod]
    rw [Nat.mod_eq_of_lt hpadlt]
    have hsum : value % alignment + (alignment - value % alignment) = alignment := by
      omega
    rw [hsum]
    exact Nat.mod_self alignment

/-- Lay out fields in authoritative semantic/source order. -/
def placeFrom : Nat -> List FieldSpec -> List PlacedField
  | _, [] => []
  | cursor, field :: rest =>
      let offset := alignUp cursor field.alignment
      { identity := field.identity
        size := field.size
        alignment := field.alignment
        offset := offset } ::
        placeFrom (offset + field.size) rest

/-- Cursor immediately after the final field, before tail padding. -/
def cursorAfter : Nat -> List FieldSpec -> Nat
  | cursor, [] => cursor
  | cursor, field :: rest =>
      let offset := alignUp cursor field.alignment
      cursorAfter (offset + field.size) rest

def maxAlignment : List FieldSpec -> Nat
  | [] => 1
  | field :: rest => Nat.max field.alignment (maxAlignment rest)

/-- Final record size includes tail padding to record alignment. -/
def finalSize (fields : List FieldSpec) : Nat :=
  alignUp (cursorAfter 0 fields) (maxAlignment fields)

/-- Adjacent ordinary fields must not overlap. -/
def NonOverlapping : List PlacedField -> Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first.offset + first.size ≤ second.offset ∧
        NonOverlapping (second :: rest)

/-- Every field has non-zero alignment. -/
def ValidAlignments (fields : List FieldSpec) : Prop :=
  ∀ field, field ∈ fields -> 0 < field.alignment

theorem placeFrom_preserves_count (cursor : Nat) (fields : List FieldSpec) :
    (placeFrom cursor fields).length = fields.length := by
  induction fields generalizing cursor with
  | nil => rfl
  | cons field rest ih =>
      simp [placeFrom, ih]

theorem placeFrom_preserves_identity_order (cursor : Nat) (fields : List FieldSpec) :
    (placeFrom cursor fields).map PlacedField.identity = fields.map FieldSpec.identity := by
  induction fields generalizing cursor with
  | nil => rfl
  | cons field rest ih =>
      simp [placeFrom, ih]

theorem placeFrom_fields_aligned (cursor : Nat) (fields : List FieldSpec)
    (hvalid : ValidAlignments fields) :
    List.Forall (fun field => field.offset % field.alignment = 0)
      (placeFrom cursor fields) := by
  induction fields generalizing cursor with
  | nil => simp [placeFrom]
  | cons field rest ih =>
      have hfield : 0 < field.alignment := hvalid field (by simp)
      have hrest : ValidAlignments rest := by
        intro candidate hmember
        exact hvalid candidate (by simp [hmember])
      constructor
      · exact alignUp_aligned cursor field.alignment hfield
      · exact ih (alignUp cursor field.alignment + field.size) hrest

theorem placeFrom_nonoverlapping (cursor : Nat) (fields : List FieldSpec) :
    NonOverlapping (placeFrom cursor fields) := by
  induction fields generalizing cursor with
  | nil => simp [placeFrom, NonOverlapping]
  | cons field rest ih =>
      cases rest with
      | nil => simp [placeFrom, NonOverlapping]
      | cons next tail =>
          let offset := alignUp cursor field.alignment
          let nextCursor := offset + field.size
          have hnext : nextCursor ≤ alignUp nextCursor next.alignment :=
            alignUp_ge nextCursor next.alignment
          constructor
          · simpa [placeFrom, NonOverlapping, offset, nextCursor] using hnext
          · simpa [placeFrom, offset, nextCursor] using
              ih nextCursor

theorem maxAlignment_positive (fields : List FieldSpec) : 0 < maxAlignment fields := by
  induction fields with
  | nil => decide
  | cons field rest ih =>
      simp [maxAlignment]
      exact Nat.lt_of_lt_of_le ih (Nat.le_max_right _ _)

theorem finalSize_aligned (fields : List FieldSpec) :
    finalSize fields % maxAlignment fields = 0 := by
  unfold finalSize
  exact alignUp_aligned _ _ (maxAlignment_positive fields)

theorem finalSize_covers_cursor (fields : List FieldSpec) :
    cursorAfter 0 fields ≤ finalSize fields := by
  unfold finalSize
  exact alignUp_ge _ _

end Oak.RecordLayout
