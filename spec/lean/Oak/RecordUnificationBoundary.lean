/-!
Record admission before structural equations. This models only the metadata
projection consumed by `recordUnificationAdmissible`, not the whole Go checker
or field unification. Names are resolved nominal names; empty refers to field
count zero. Effects and authority are deliberately absent from this projection.
-/
namespace Oak.RecordUnificationBoundary

structure Record where
  nominal : Bool
  name : String
  empty : Bool
  openRow : Bool
  deriving DecidableEq, Repr

def admissible (left right : Record) : Bool :=
  if left.openRow != right.openRow then false
  else if left.nominal && right.nominal then left.name == right.name
  else if (left.nominal && left.empty) || (right.nominal && right.empty) then false
  else true

theorem row_boundary (left right : Record)
    (h : left.openRow ≠ right.openRow) : admissible left right = false := by
  simp [admissible, h]

theorem nominal_boundary (left right : Record)
    (hl : left.nominal = true) (hr : right.nominal = true)
    (hn : left.name ≠ right.name) : admissible left right = false := by
  simp [admissible, hl, hr, hn]

theorem empty_nominal_not_shape (left right : Record)
    (hl : left.nominal = true) (he : left.empty = true)
    (hr : right.nominal = false) : admissible left right = false := by
  simp [admissible, hl, he, hr]

theorem shape_not_empty_nominal (left right : Record)
    (hl : left.nominal = false) (he : right.empty = true)
    (hr : right.nominal = true) : admissible left right = false := by
  simp [admissible, hl, he, hr]

theorem nonempty_structural_admission (left right : Record)
    (rows : left.openRow = right.openRow)
    (hl : left.empty = false) (hr : right.empty = false)
    (shape : right.nominal = false) : admissible left right = true := by
  simp [admissible, rows, hl, hr, shape]

end Oak.RecordUnificationBoundary
