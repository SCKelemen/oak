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
  else if value % alignment = 0 then value
  else value + (alignment - value % alignment)

theorem alignUp_ge (value alignment : Nat) : value ≤ alignUp value alignment := by
  by_cases hzero : alignment = 0
  · simp [alignUp, hzero]
  · by_cases hrem : value % alignment = 0
    · simp [alignUp, hzero, hrem]
    · simp [alignUp, hzero, hrem]

theorem alignUp_aligned (value alignment : Nat) (halignment : 0 < alignment) :
    alignUp value alignment % alignment = 0 := by
  have hzero : alignment ≠ 0 := Nat.ne_of_gt halignment
  by_cases hrem : value % alignment = 0
  · simp [alignUp, hzero, hrem]
  · simp only [alignUp, hzero, if_false, hrem]
    have hlt : value % alignment < alignment := Nat.mod_lt value halignment
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
      { identity := field.identity
        size := field.size
        alignment := field.alignment
        offset := alignUp cursor field.alignment } ::
        placeFrom (alignUp cursor field.alignment + field.size) rest

/-- Cursor immediately after the final field, before tail padding. -/
def cursorAfter : Nat -> List FieldSpec -> Nat
  | cursor, [] => cursor
  | cursor, field :: rest =>
      cursorAfter (alignUp cursor field.alignment + field.size) rest

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

/-- Every placed field satisfies its own alignment. -/
def AllAligned : List PlacedField -> Prop
  | [] => True
  | field :: rest =>
      field.offset % field.alignment = 0 ∧ AllAligned rest

/-- Every input field has non-zero alignment. -/
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
    AllAligned (placeFrom cursor fields) := by
  induction fields generalizing cursor with
  | nil => simp [placeFrom, AllAligned]
  | cons field rest ih =>
      have hfield : 0 < field.alignment := hvalid field (by simp)
      have hrest : ValidAlignments rest := by
        intro candidate hmember
        exact hvalid candidate (by simp [hmember])
      change
        alignUp cursor field.alignment % field.alignment = 0 ∧
          AllAligned
            (placeFrom (alignUp cursor field.alignment + field.size) rest)
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
          change
            alignUp cursor field.alignment + field.size ≤
                alignUp (alignUp cursor field.alignment + field.size) next.alignment ∧
              NonOverlapping
                (placeFrom (alignUp cursor field.alignment + field.size)
                  (next :: tail))
          constructor
          · exact alignUp_ge _ _
          · exact ih (alignUp cursor field.alignment + field.size)

theorem maxAlignment_positive (fields : List FieldSpec) : 0 < maxAlignment fields := by
  induction fields with
  | nil => simp [maxAlignment]
  | cons field rest ih =>
      change 0 < Nat.max field.alignment (maxAlignment rest)
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
