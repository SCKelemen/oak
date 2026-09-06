namespace Oak.RecordShape

/-- A semantic field is identified by its member name and semantic type.
    Runtime offsets and representation are deliberately absent. -/
structure Field where
  name : Nat
  ty : Nat
  deriving DecidableEq, Repr

abbrev Shape := List Field

/-- A candidate satisfies a required shape when every required semantic field is
    present in the candidate. Extra candidate fields are allowed. -/
def Satisfies (candidate required : Shape) : Prop :=
  ∀ field, field ∈ required → field ∈ candidate

/-- Every shape satisfies itself. -/
theorem reflexive (shape : Shape) : Satisfies shape shape := by
  intro field hfield
  exact hfield

/-- An empty requirement is satisfied by every candidate. -/
theorem empty_required (candidate : Shape) : Satisfies candidate [] := by
  intro field hfield
  simp at hfield

/-- Adding an extra candidate field cannot destroy shape satisfaction. -/
theorem candidate_extension (candidate required : Shape) (extra : Field)
    (h : Satisfies candidate required) :
    Satisfies (extra :: candidate) required := by
  intro field hrequired
  exact List.mem_cons_of_mem extra (h field hrequired)

/-- Shape satisfaction composes: if A provides everything B requires, and B
    provides everything C requires, then A provides everything C requires. -/
theorem transitive (a b c : Shape)
    (hab : Satisfies a b) (hbc : Satisfies b c) :
    Satisfies a c := by
  intro field hc
  exact hab field (hbc field hc)

/-- Required-field order has no semantic effect. -/
theorem required_reverse_iff (candidate required : Shape) :
    Satisfies candidate required.reverse ↔ Satisfies candidate required := by
  constructor
  · intro h field hrequired
    apply h field
    simpa using hrequired
  · intro h field hrequired
    apply h field
    simpa using hrequired

/-- Candidate-field order has no semantic effect. -/
theorem candidate_reverse_iff (candidate required : Shape) :
    Satisfies candidate.reverse required ↔ Satisfies candidate required := by
  constructor
  · intro h field hrequired
    have hmem := h field hrequired
    simpa using hmem
  · intro h field hrequired
    have hmem := h field hrequired
    simpa using hmem

/-- A specifically missing required field is enough to reject satisfaction. -/
theorem missing_required_rejected (candidate required : Shape) (field : Field)
    (hrequired : field ∈ required) (hmissing : field ∉ candidate) :
    ¬ Satisfies candidate required := by
  intro h
  exact hmissing (h field hrequired)

/-- Runtime representation is modeled as an independent axis. Its contents are
    abstract here because no representation fact participates in satisfaction. -/
structure SemanticRecord where
  fields : Shape
  representation : Nat
  deriving DecidableEq, Repr

def RecordSatisfies (candidate required : SemanticRecord) : Prop :=
  Satisfies candidate.fields required.fields

/-- Rebinding runtime representation cannot alter semantic shape satisfaction. -/
theorem representation_irrelevant
    (candidate required : SemanticRecord) (representation : Nat) :
    RecordSatisfies { candidate with representation := representation } required ↔
      RecordSatisfies candidate required := by
  rfl

/-- Required representation is likewise irrelevant to semantic shape checking. -/
theorem required_representation_irrelevant
    (candidate required : SemanticRecord) (representation : Nat) :
    RecordSatisfies candidate { required with representation := representation } ↔
      RecordSatisfies candidate required := by
  rfl

end Oak.RecordShape
