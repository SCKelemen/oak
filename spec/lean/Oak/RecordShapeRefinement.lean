import Oak.RecordShape

namespace Oak.RecordShapeRefinement

open Oak.RecordShape

/-- Concrete checker-side record fields. This mirrors the implementation's
    name -> semantic-type lookup behavior while remaining independent of runtime
    representation. Well-formed shapes have unique field names. -/
abbrev ConcreteShape := List Field

def Lookup (name : Nat) : ConcreteShape → Option Nat
  | [] => none
  | field :: rest =>
      if field.name = name then some field.ty else Lookup name rest

def UniqueNames (shape : ConcreteShape) : Prop :=
  ∀ a, a ∈ shape → ∀ b, b ∈ shape → a.name = b.name → a = b

/-- Executable relation corresponding to Go's recordSatisfiesShape loop:
    each required name must resolve in the candidate and its semantic type must
    be exactly equal. -/
def SatisfiesBool (candidate required : ConcreteShape) : Bool :=
  required.all fun requiredField =>
    match Lookup requiredField.name candidate with
    | some candidateTy => candidateTy == requiredField.ty
    | none => false

private theorem lookup_mem
    (shape : ConcreteShape) (name ty : Nat)
    (h : Lookup name shape = some ty) :
    ∃ field ∈ shape, field.name = name ∧ field.ty = ty := by
  induction shape with
  | nil => simp [Lookup] at h
  | cons field rest ih =>
      simp only [Lookup] at h
      by_cases heq : field.name = name
      · simp [heq] at h
        subst ty
        exact ⟨field, by simp, heq, rfl⟩
      · simp [heq] at h
        obtain ⟨found, hmem, hname, hty⟩ := ih h
        exact ⟨found, by simp [hmem], hname, hty⟩

private theorem lookup_of_mem_unique
    (shape : ConcreteShape) (hunique : UniqueNames shape)
    (field : Field) (hfield : field ∈ shape) :
    Lookup field.name shape = some field.ty := by
  induction shape with
  | nil => simp at hfield
  | cons head rest ih =>
      simp only [List.mem_cons] at hfield
      rcases hfield with rfl | hrest
      · simp [Lookup]
      · have hne : head.name ≠ field.name := by
          intro hname
          have heq := hunique head (by simp) field (by simp [hrest]) hname
          subst field
          simp at hrest
        have hrestUnique : UniqueNames rest := by
          intro a ha b hb hname
          exact hunique a (by simp [ha]) b (by simp [hb]) hname
        simp [Lookup, hne, ih hrestUnique hrest]

private theorem all_eq_true_iff {xs : List α} {p : α → Bool} :
    xs.all p = true ↔ ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      simp [List.all, ih, and_left_comm, and_assoc]

/-- Soundness: if the executable checker accepts two well-formed shapes, the
    abstract semantic satisfaction relation holds. -/
theorem satisfiesBool_sound
    (candidate required : ConcreteShape)
    (hcandidate : UniqueNames candidate)
    (hrequired : UniqueNames required)
    (hcheck : SatisfiesBool candidate required = true) :
    Satisfies candidate required := by
  intro field hfield
  have hall := (all_eq_true_iff.mp hcheck) field hfield
  simp only [SatisfiesBool] at hcheck
  unfold SatisfiesBool at hcheck
  have hlookupCheck := (all_eq_true_iff.mp hcheck) field hfield
  cases hlookup : Lookup field.name candidate with
  | none => simp [hlookup] at hlookupCheck
  | some ty =>
      simp [hlookup] at hlookupCheck
      have hty : ty = field.ty := by
        exact of_decide_eq_true hlookupCheck
      obtain ⟨candidateField, hmem, hname, hcandidateTy⟩ :=
        lookup_mem candidate field.name ty hlookup
      have hsame : candidateField = field := by
        apply hrequired field hfield field hfield rfl
      subst candidateField
      exact hmem

/-- Completeness: the abstract relation over unique-name records is accepted by
    the executable lookup-and-equality checker. -/
theorem satisfiesBool_complete
    (candidate required : ConcreteShape)
    (hcandidate : UniqueNames candidate)
    (hrequired : UniqueNames required)
    (hsatisfies : Satisfies candidate required) :
    SatisfiesBool candidate required = true := by
  unfold SatisfiesBool
  apply all_eq_true_iff.mpr
  intro field hfield
  have hcandidateField : field ∈ candidate := hsatisfies field hfield
  have hlookup := lookup_of_mem_unique candidate hcandidate field hcandidateField
  simp [hlookup]

/-- The concrete decision procedure and abstract semantic relation coincide on
    well-formed record shapes. This is the refinement theorem used for Oak's R
    status on record-shape satisfaction. -/
theorem satisfiesBool_iff_satisfies
    (candidate required : ConcreteShape)
    (hcandidate : UniqueNames candidate)
    (hrequired : UniqueNames required) :
    SatisfiesBool candidate required = true ↔ Satisfies candidate required := by
  constructor
  · exact satisfiesBool_sound candidate required hcandidate hrequired
  · exact satisfiesBool_complete candidate required hcandidate hrequired

end Oak.RecordShapeRefinement
