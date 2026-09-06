import Oak.RecordShape

namespace Oak.RecordShapeRefinement

open Oak.RecordShape

/-- Concrete checker-side record fields. This mirrors the implementation's
    name -> semantic-type lookup behavior while remaining independent of runtime
    representation. -/
abbrev ConcreteShape := List Field

def Lookup (name : Nat) : ConcreteShape → Option Nat
  | [] => none
  | field :: rest =>
      if field.name = name then some field.ty else Lookup name rest

/-- The implementation represents fields as a name-keyed map, so a well-formed
    concrete record cannot contain the same field name twice. -/
def UniqueNames : ConcreteShape → Prop
  | [] => True
  | field :: rest =>
      (∀ other, other ∈ rest → other.name ≠ field.name) ∧ UniqueNames rest

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
      by_cases heq : field.name = name
      · simp [Lookup, heq] at h
        subst ty
        exact ⟨field, by simp, heq, rfl⟩
      · simp [Lookup, heq] at h
        obtain ⟨found, hmem, hname, hty⟩ := ih h
        exact ⟨found, by simp [hmem], hname, hty⟩

private theorem lookup_of_mem_unique
    (shape : ConcreteShape) (hunique : UniqueNames shape)
    (field : Field) (hfield : field ∈ shape) :
    Lookup field.name shape = some field.ty := by
  induction shape with
  | nil => simp at hfield
  | cons head rest ih =>
      rcases hunique with ⟨hheadUnique, hrestUnique⟩
      simp only [List.mem_cons] at hfield
      rcases hfield with rfl | hrest
      · simp [Lookup]
      · have hne : head.name ≠ field.name := by
          intro hname
          exact hheadUnique field hrest hname.symm
        simp [Lookup, hne, ih hrestUnique hrest]

private theorem all_eq_true_iff {xs : List α} {p : α → Bool} :
    xs.all p = true ↔ ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp
  | cons head tail ih => simp [List.all, ih]

/-- Soundness: if the executable checker accepts, the abstract semantic
    satisfaction relation holds. Unique-name assumptions are carried because
    they are part of concrete record well-formedness, although soundness itself
    does not depend on them. -/
theorem satisfiesBool_sound
    (candidate required : ConcreteShape)
    (_hcandidate : UniqueNames candidate)
    (_hrequired : UniqueNames required)
    (hcheck : SatisfiesBool candidate required = true) :
    Satisfies candidate required := by
  intro field hfield
  have hlookupCheck := (all_eq_true_iff.mp hcheck) field hfield
  cases hlookup : Lookup field.name candidate with
  | none =>
      simp [hlookup] at hlookupCheck
  | some ty =>
      have hty : ty = field.ty := by
        simpa [hlookup] using hlookupCheck
      obtain ⟨candidateField, hmem, hname, hcandidateTy⟩ :=
        lookup_mem candidate field.name ty hlookup
      have hsame : candidateField = field := by
        cases candidateField
        cases field
        simp_all
      simpa [hsame] using hmem

/-- Completeness: abstract satisfaction is accepted by the executable checker
    when the concrete candidate obeys the implementation's unique-name invariant. -/
theorem satisfiesBool_complete
    (candidate required : ConcreteShape)
    (hcandidate : UniqueNames candidate)
    (_hrequired : UniqueNames required)
    (hsatisfies : Satisfies candidate required) :
    SatisfiesBool candidate required = true := by
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
