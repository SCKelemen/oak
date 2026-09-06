namespace Oak.GeneralizationSafety

/-- Generalization is a separate decision from type inference. These booleans
    abstract the authority/effect/region facts that may forbid universal
    quantification of an otherwise inferred local type. -/
structure Facts where
  mutableAuthority : Bool := false
  uniqueAuthority : Bool := false
  regionBound : Bool := false
  externalAuthority : Bool := false
  effectfulCapture : Bool := false
  unsafeAssumption : Bool := false
  unknownAuthority : Bool := false
  deriving DecidableEq, Repr

def Safe (facts : Facts) : Prop :=
  facts.mutableAuthority = false ∧
  facts.uniqueAuthority = false ∧
  facts.regionBound = false ∧
  facts.externalAuthority = false ∧
  facts.effectfulCapture = false ∧
  facts.unsafeAssumption = false ∧
  facts.unknownAuthority = false

/-- The inferred semantic type is modeled independently from the generalization
    decision. Blocking polymorphism never rewrites the inferred monotype. -/
structure Binding where
  inferredType : Nat
  generalized : Bool
  deriving DecidableEq, Repr

def decideGeneralization (inferredType : Nat) (facts : Facts) : Binding :=
  { inferredType := inferredType
    generalized :=
      !(facts.mutableAuthority || facts.uniqueAuthority || facts.regionBound ||
        facts.externalAuthority || facts.effectfulCapture || facts.unsafeAssumption ||
        facts.unknownAuthority) }

/-- Generalization policy cannot change the inferred semantic type. -/
theorem decision_preserves_inferred_type (inferredType : Nat) (facts : Facts) :
    (decideGeneralization inferredType facts).inferredType = inferredType := by
  rfl

/-- A fully safe fact set permits generalization. -/
theorem safe_generalizes (inferredType : Nat) (facts : Facts) (h : Safe facts) :
    (decideGeneralization inferredType facts).generalized = true := by
  rcases h with ⟨hm, hu, hr, he, hf, hs, hk⟩
  simp [decideGeneralization, hm, hu, hr, he, hf, hs, hk]

/-- Capturing mutable authority forbids generalization. -/
theorem mutable_authority_blocks (inferredType : Nat) (facts : Facts)
    (h : facts.mutableAuthority = true) :
    (decideGeneralization inferredType facts).generalized = false := by
  simp [decideGeneralization, h]

/-- Capturing unique authority forbids generalization. -/
theorem unique_authority_blocks (inferredType : Nat) (facts : Facts)
    (h : facts.uniqueAuthority = true) :
    (decideGeneralization inferredType facts).generalized = false := by
  simp [decideGeneralization, h]

/-- Region-bound values cannot be generalized across their region identity. -/
theorem region_bound_blocks (inferredType : Nat) (facts : Facts)
    (h : facts.regionBound = true) :
    (decideGeneralization inferredType facts).generalized = false := by
  simp [decideGeneralization, h]

/-- External/MMIO-like authority is not silently generalized. -/
theorem external_authority_blocks (inferredType : Nat) (facts : Facts)
    (h : facts.externalAuthority = true) :
    (decideGeneralization inferredType facts).generalized = false := by
  simp [decideGeneralization, h]

/-- Unresolved authority facts fail closed rather than guessing. -/
theorem unknown_authority_blocks (inferredType : Nat) (facts : Facts)
    (h : facts.unknownAuthority = true) :
    (decideGeneralization inferredType facts).generalized = false := by
  simp [decideGeneralization, h]

end Oak.GeneralizationSafety
