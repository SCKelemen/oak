namespace Oak.RepresentationPolymorphism

/-- A semantic record is only its named-field meaning. Runtime placement is not
    part of this object. Names/types are represented abstractly as naturals so
    the proof is independent of Oak surface syntax. -/
structure SemanticRecord where
  fields : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- One concrete runtime layout. Field offsets/order may differ between layouts
    that realize the same semantic record. -/
structure Layout where
  name : Nat
  fields : List (Nat × Nat)
  size : Nat
  alignment : Nat
  deriving DecidableEq, Repr

/-- A realization pairs one semantic record with one selected runtime layout. -/
structure Realization where
  semantic : SemanticRecord
  representation : Layout
  deriving DecidableEq, Repr

/-- Selecting representation is intentionally an operation on the representation
    axis only. -/
def select (semantic : SemanticRecord) (representation : Layout) : Realization :=
  { semantic := semantic, representation := representation }

/-- Record-shape satisfaction depends only on semantic fields. -/
def Satisfies (candidate : Realization) (required : SemanticRecord) : Prop :=
  ∀ field, field ∈ required.fields → field ∈ candidate.semantic.fields

/-- Selecting any representation preserves semantic identity exactly. -/
theorem select_preserves_semantics (semantic : SemanticRecord) (representation : Layout) :
    (select semantic representation).semantic = semantic := by
  rfl

/-- Rebinding a realization to a different representation preserves semantics. -/
def rebind (value : Realization) (representation : Layout) : Realization :=
  { semantic := value.semantic, representation := representation }

/-- Rebinding cannot change the semantic record. -/
theorem rebind_preserves_semantics (value : Realization) (representation : Layout) :
    (rebind value representation).semantic = value.semantic := by
  rfl

/-- Shape satisfaction is representation-independent by construction. -/
theorem satisfaction_representation_irrelevant (semantic required : SemanticRecord)
    (left right : Layout) :
    Satisfies (select semantic left) required ↔
      Satisfies (select semantic right) required := by
  rfl

/-- Two physically distinct layouts may realize exactly the same semantic type. -/
theorem distinct_layouts_can_share_semantics (semantic : SemanticRecord)
    (left right : Layout) (hne : left ≠ right) :
    select semantic left ≠ select semantic right ∧
      (select semantic left).semantic = (select semantic right).semantic := by
  constructor
  · intro heq
    apply hne
    exact congrArg Realization.representation heq
  · rfl

/-- Rebinding twice keeps only the final representation while semantic identity
    remains unchanged. -/
theorem rebind_last_wins (value : Realization) (first second : Layout) :
    rebind (rebind value first) second = rebind value second := by
  rfl

end Oak.RepresentationPolymorphism
