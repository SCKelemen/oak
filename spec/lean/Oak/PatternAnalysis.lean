namespace Oak.PatternAnalysis

/-- A semantic case is reachable when it belongs to the closed case universe and
    survives the refinements known at the match site. For ordinary ADTs the
    reachable list is normally the full constructor/product case set; GADT
    index equalities may make it a strict subset. -/
def ReachableCase [DecidableEq α]
    (universe reachable : List α) (value : α) : Prop :=
  value ∈ universe ∧ value ∈ reachable

/-- Coverage is exhaustive exactly when every reachable semantic case is covered. -/
def Exhaustive [DecidableEq α]
    (universe reachable covered : List α) : Prop :=
  ∀ value, ReachableCase universe reachable value → value ∈ covered

/-- An arm is redundant when it contributes no case outside prior coverage. -/
def Redundant [DecidableEq α] (covered arm : List α) : Prop :=
  ∀ value, value ∈ arm → value ∈ covered

/-- An arm is useful when it contributes at least one previously uncovered case. -/
def Useful [DecidableEq α] (covered arm : List α) : Prop :=
  ∃ value, value ∈ arm ∧ value ∉ covered

/-- A counterexample is a reachable semantic case not covered by the match. -/
def Counterexample [DecidableEq α]
    (universe reachable covered : List α) (value : α) : Prop :=
  ReachableCase universe reachable value ∧ value ∉ covered

/-- A reported counterexample is sufficient to refute exhaustiveness. -/
theorem counterexample_refutes_exhaustive [DecidableEq α]
    {universe reachable covered : List α} {value : α}
    (h : Counterexample universe reachable covered value) :
    ¬ Exhaustive universe reachable covered := by
  intro hexhaustive
  exact h.2 (hexhaustive value h.1)

/-- A missing reachable case is exactly a counterexample witness. -/
theorem missing_reachable_is_counterexample [DecidableEq α]
    {universe reachable covered : List α} {value : α}
    (huniverse : value ∈ universe)
    (hreachable : value ∈ reachable)
    (hmissing : value ∉ covered) :
    Counterexample universe reachable covered value := by
  exact ⟨⟨huniverse, hreachable⟩, hmissing⟩

/-- Redundant and useful are mutually exclusive. -/
theorem redundant_not_useful [DecidableEq α]
    {covered arm : List α}
    (h : Redundant covered arm) :
    ¬ Useful covered arm := by
  intro huseful
  rcases huseful with ⟨value, harm, hmissing⟩
  exact hmissing (h value harm)

/-- Adding a redundant arm cannot change an already exhaustive match. -/
theorem adding_redundant_preserves_exhaustive [DecidableEq α]
    {universe reachable covered arm : List α}
    (hexhaustive : Exhaustive universe reachable covered)
    (_ : Redundant covered arm) :
    Exhaustive universe reachable (covered ++ arm) := by
  intro value hreachable
  exact List.mem_append_left arm (hexhaustive value hreachable)

/-- A constructor excluded by the current refinement is not a reachable case. -/
theorem refinement_excludes_other [DecidableEq α]
    {universe : List α} {selected other : α}
    (hne : other ≠ selected) :
    ¬ ReachableCase universe [selected] other := by
  intro h
  have : other = selected := by
    simpa using h.2
  exact hne this

/-- Exhaustiveness never requires a case that the current refinement excludes. -/
theorem unreachable_case_not_required [DecidableEq α]
    {universe reachable covered : List α} {value : α}
    (hunreachable : value ∉ reachable) :
    ¬ ReachableCase universe reachable value := by
  intro h
  exact hunreachable h.2

/-- The core pattern algebra used for constructor refinement. -/
inductive ArmPattern (α : Type) where
  | any
  | ctor (value : α)

/-- Pattern matching itself is a proposition; no runtime tag representation is
    assumed by this formal layer. -/
def Matches : ArmPattern α → α → Prop
  | .any, _ => True
  | .ctor ctor, value => value = ctor

/-- Entering an exact constructor arm establishes the constructor equality that
    later GADT/index reasoning may consume. -/
theorem constructor_match_introduces_refinement
    {ctor value : α}
    (h : Matches (.ctor ctor) value) :
    value = ctor := by
  exact h

/-- A constructor arm for a case excluded by the current reachable set cannot
    match any reachable value. -/
theorem excluded_constructor_arm_is_unreachable [DecidableEq α]
    {reachable : List α} {ctor : α}
    (hexcluded : ctor ∉ reachable) :
    ∀ value, value ∈ reachable → Matches (.ctor ctor) value → False := by
  intro value hreachable hmatch
  have hvalue : value = ctor := constructor_match_introduces_refinement hmatch
  subst value
  exact hexcluded hreachable

end Oak.PatternAnalysis
