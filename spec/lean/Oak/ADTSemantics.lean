namespace Oak.ADTSemantics

/-! # ADT value and dispatch semantics

Model for `docs/spec/30-adts-patterns.md`: an ADT value is a constructor tag
plus its payload, and match dispatch selects the **first** source-ordered arm
whose tag matches — deterministically, evaluating only the selected branch's
handler, with the payload delivered exactly as constructed. Coverage,
redundancy, and reachable-case laws live in `Oak.Exhaustiveness` and
`Oak.PatternAnalysis`; this module pins the value/dispatch core they assume. -/

/-- An ADT value: constructor identity plus payload. -/
structure Value (τ : Type) where
  tag : Nat
  payload : τ
  deriving Repr

/-- Constructor identity is the tag: distinct constructors yield values no
    tag test can confuse. -/
theorem constructors_disjoint {τ : Type} {p q : τ} {t u : Nat} (h : t ≠ u) :
    (Value.mk t p).tag ≠ (Value.mk u q).tag := h

/-- Source-ordered match arms: a tag guard paired with a payload handler. -/
abbrev Arm (τ β : Type) := Nat × (τ → β)

/-- First-match selection over source-ordered arms. -/
def select {τ β : Type} : List (Arm τ β) → Value τ → Option β
  | [], _ => none
  | (tag, handler) :: rest, v =>
    if v.tag == tag then some (handler v.payload) else select rest v

/-- **Selection is deterministic and source-ordered**: a matching head arm is
    taken, a non-matching head arm is skipped, and nothing else happens. The
    two equations characterize dispatch completely. -/
theorem select_head_match {τ β : Type} {tag : Nat} {handler : τ → β}
    {rest : List (Arm τ β)} {v : Value τ} (h : v.tag = tag) :
    select ((tag, handler) :: rest) v = some (handler v.payload) := by
  simp [select, h]

theorem select_head_skip {τ β : Type} {tag : Nat} {handler : τ → β}
    {rest : List (Arm τ β)} {v : Value τ} (h : v.tag ≠ tag) :
    select ((tag, handler) :: rest) v = select rest v := by
  simp [select, h]

/-- **Only the selected branch is evaluated**: the result of a successful
    dispatch is the selected handler applied to the value's payload — no
    other arm's handler contributes to the result. -/
theorem select_result_from_selected_handler {τ β : Type}
    {arms : List (Arm τ β)} {v : Value τ} {b : β}
    (h : select arms v = some b) :
    ∃ handler : τ → β, (v.tag, handler) ∈ arms ∧ b = handler v.payload := by
  induction arms with
  | nil => exact absurd h (by simp [select])
  | cons arm rest ih =>
    obtain ⟨tag, handler⟩ := arm
    by_cases htag : v.tag = tag
    · rw [select_head_match htag] at h
      subst htag
      exact ⟨handler, by simp, by injection h with h; exact h.symm⟩
    · rw [select_head_skip htag] at h
      obtain ⟨found, hmem, hb⟩ := ih h
      exact ⟨found, by simp [hmem], hb⟩

/-- **Constructor narrowing preserves the payload**: dispatching a freshly
    constructed value through an arm for its own constructor hands the arm
    exactly the constructed payload. -/
theorem construct_then_dispatch {τ β : Type} {tag : Nat} {handler : τ → β}
    {rest : List (Arm τ β)} (payload : τ) :
    select ((tag, handler) :: rest) (Value.mk tag payload) =
      some (handler payload) :=
  select_head_match rfl

/-- A value whose constructor no arm guards falls through: dispatch cannot
    invent a branch (the exhaustiveness analyses make this state an error
    before evaluation). -/
theorem select_none_of_no_arm {τ β : Type} {arms : List (Arm τ β)} {v : Value τ}
    (h : ∀ arm ∈ arms, v.tag ≠ arm.1) : select arms v = none := by
  induction arms with
  | nil => rfl
  | cons arm rest ih =>
    obtain ⟨tag, handler⟩ := arm
    rw [select_head_skip (h (tag, handler) (by simp))]
    exact ih fun a ha => h a (by simp [ha])

end Oak.ADTSemantics
