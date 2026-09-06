namespace Oak.Effects

inductive Family where
  | memoryAllocate
  | threadBlock
  | osSyscall
  | mmio
  | io
  | user : Nat -> Family
  deriving DecidableEq, Repr

inductive Effect where
  | broad : Family -> Effect
  | scoped : Family -> Nat -> Effect
  deriving DecidableEq, Repr

/-- `Subsumes forbidden required` means the forbidden effect covers the required one. -/
def Subsumes : Effect -> Effect -> Prop
  | .broad f, .broad g => f = g
  | .broad f, .scoped g _ => f = g
  | .scoped f s, .scoped g t => f = g ∧ s = t
  | .scoped _ _, .broad _ => False

/-- Two effects overlap when either one semantically subsumes the other. -/
def Overlaps (a b : Effect) : Prop :=
  Subsumes a b ∨ Subsumes b a

theorem broad_subsumes_scoped (f : Family) (scope : Nat) :
    Subsumes (.broad f) (.scoped f scope) := by
  rfl

theorem broad_subsumes_broad (f : Family) :
    Subsumes (.broad f) (.broad f) := by
  rfl

theorem scoped_subsumes_same (f : Family) (scope : Nat) :
    Subsumes (.scoped f scope) (.scoped f scope) := by
  exact ⟨rfl, rfl⟩

theorem scoped_does_not_subsume_broad (f : Family) (scope : Nat) :
    ¬ Subsumes (.scoped f scope) (.broad f) := by
  intro h
  exact h

theorem scoped_subsumes_scoped_iff (f g : Family) (s t : Nat) :
    Subsumes (.scoped f s) (.scoped g t) ↔ f = g ∧ s = t := by
  rfl

theorem broad_subsumes_scoped_iff (f g : Family) (scope : Nat) :
    Subsumes (.broad f) (.scoped g scope) ↔ f = g := by
  rfl

theorem overlaps_symm (a b : Effect) : Overlaps a b ↔ Overlaps b a := by
  constructor
  · intro h
    cases h with
    | inl hab => exact Or.inr hab
    | inr hba => exact Or.inl hba
  · intro h
    cases h with
    | inl hba => exact Or.inr hba
    | inr hab => exact Or.inl hab

theorem broad_overlaps_scoped (f : Family) (scope : Nat) :
    Overlaps (.broad f) (.scoped f scope) := by
  exact Or.inl (broad_subsumes_scoped f scope)

theorem distinct_scopes_do_not_overlap
    (f : Family) (s t : Nat) (hne : s ≠ t) :
    ¬ Overlaps (.scoped f s) (.scoped f t) := by
  intro h
  cases h with
  | inl hst => exact hne hst.2
  | inr hts => exact hne hts.2.symm

/-- A requirement is statically contradictory with a forbidden effect when they overlap. -/
def Contradicts (required forbidden : Effect) : Prop :=
  Overlaps required forbidden

theorem broad_forbid_rejects_scoped_requirement
    (f : Family) (scope : Nat) :
    Contradicts (.scoped f scope) (.broad f) := by
  exact (overlaps_symm (.broad f) (.scoped f scope)).mp
    (broad_overlaps_scoped f scope)

end Oak.Effects
