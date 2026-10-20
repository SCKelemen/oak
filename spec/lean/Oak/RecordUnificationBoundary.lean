/-!
Record admission before structural equations. This models only the metadata
projection consumed by `recordUnificationAdmissible` and the record/Unit view
used by its dispatcher, not the whole Go checker or field unification. Names
are resolved nominal names; empty refers to field count zero. Effects,
authority, substitution and persistent binders are absent from this projection.
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

/- The Unit view is used only for record-equation admission. It is not a
   normalization of stored types or substitution solutions. Metadata admission
   is necessary, not sufficient, for successful field equations. -/
inductive Operand where
  | record (metadata : Record)
  | unit
  deriving DecidableEq, Repr

def unitRecord : Record := ⟨false, "", true, false⟩

def recordView : Operand → Record
  | .record metadata => metadata
  | .unit => unitRecord

def operandAdmissible (left right : Operand) : Bool :=
  admissible (recordView left) (recordView right)

theorem open_record_not_unit (record : Record)
    (h : record.openRow = true) :
    operandAdmissible (.record record) .unit = false := by
  simp [operandAdmissible, recordView, unitRecord, admissible, h]

theorem unit_not_open_record (record : Record)
    (h : record.openRow = true) :
    operandAdmissible .unit (.record record) = false := by
  simp [operandAdmissible, recordView, unitRecord, admissible, h]

theorem closed_empty_shape_unit_admission (name : String) :
    operandAdmissible (.record ⟨false, name, true, false⟩) .unit = true ∧
    operandAdmissible .unit (.record ⟨false, name, true, false⟩) = true := by
  simp [operandAdmissible, recordView, unitRecord, admissible]

end Oak.RecordUnificationBoundary
