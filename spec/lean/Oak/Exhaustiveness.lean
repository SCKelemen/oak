namespace Oak.Exhaustiveness

/-- A finite ADT is represented abstractly by its closed constructor set. -/
def Exhaustive [DecidableEq α]
    (constructors arms : List α) (hasWildcard : Bool) : Prop :=
  hasWildcard = true ∨ ∀ ctor, ctor ∈ constructors → ctor ∈ arms

/-- A wildcard arm makes a finite match exhaustive regardless of listed arms. -/
theorem wildcard_is_exhaustive [DecidableEq α]
    (constructors arms : List α) :
    Exhaustive constructors arms true := by
  exact Or.inl rfl

/-- Listing every constructor is sufficient when there is no wildcard. -/
theorem all_constructors_are_exhaustive [DecidableEq α]
    (constructors arms : List α)
    (h : ∀ ctor, ctor ∈ constructors → ctor ∈ arms) :
    Exhaustive constructors arms false := by
  exact Or.inr h

/-- Without a wildcard, one missing constructor is enough to reject a match. -/
theorem missing_constructor_is_not_exhaustive [DecidableEq α]
    (constructors arms : List α) (missing : α)
    (hctor : missing ∈ constructors)
    (hmissing : missing ∉ arms) :
    ¬ Exhaustive constructors arms false := by
  intro hexhaustive
  cases hexhaustive with
  | inl hwildcard => simp at hwildcard
  | inr hall => exact hmissing (hall missing hctor)

/-- Adding arms cannot make an already exhaustive match non-exhaustive. -/
theorem adding_arms_preserves_exhaustiveness [DecidableEq α]
    (constructors arms extra : List α) (wildcard : Bool)
    (h : Exhaustive constructors arms wildcard) :
    Exhaustive constructors (arms ++ extra) wildcard := by
  cases h with
  | inl hwildcard => exact Or.inl hwildcard
  | inr hall =>
      exact Or.inr (by
        intro ctor hctor
        exact List.mem_append_left extra (hall ctor hctor))

/-- Constructor order is irrelevant to the coverage condition. -/
theorem constructor_membership_drives_coverage [DecidableEq α]
    (constructors arms : List α) :
    Exhaustive constructors arms false ↔
      ∀ ctor, ctor ∈ constructors → ctor ∈ arms := by
  constructor
  · intro h
    cases h with
    | inl hwildcard => simp at hwildcard
    | inr hall => exact hall
  · intro h
    exact Or.inr h

end Oak.Exhaustiveness
