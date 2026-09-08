import PropagationState

set_option autoImplicit false
namespace OakVerification.ClauseClassifier
open PropagationState

instance (s : Scratch) (l : Literal) : Decidable (FalseUnder s l) :=
  inferInstanceAs (Decidable (s (l.index - 1) = some (!l.positive)))

def unique : Clause → Clause
  | [] => []
  | l :: rest => if l ∈ rest then unique rest else l :: unique rest

theorem mem_unique (l : Literal) (c : Clause) : l ∈ unique c ↔ l ∈ c := by
  induction c with
  | nil => simp [unique]
  | cons head rest ih =>
    by_cases h : head ∈ rest
    · simp only [unique, if_pos h, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · intro member
        rcases member with same | member
        · subst l
          exact h
        · exact member
    · simp [unique, h, ih]

def survivors (s : Scratch) (c : Clause) : Clause :=
  unique (c.filter fun l => !decide (FalseUnder s l))

theorem mem_survivors (s : Scratch) (c : Clause) (l : Literal) :
    l ∈ survivors s c ↔ l ∈ c ∧ ¬ FalseUnder s l := by
  simp [survivors, mem_unique]

inductive Result where
  | satisfied
  | conflict
  | unit (literal : Literal)
  | unresolved
  deriving DecidableEq, Repr

def classify (s : Scratch) (c : Clause) : Result :=
  if c.any (fun l => decide (s (l.index - 1) = some l.positive)) then .satisfied
  else match survivors s c with
    | [] => .conflict
    | [u] => .unit u
    | _ => .unresolved

theorem conflict_residual (s : Scratch) (c : Clause) (h : classify s c = .conflict) :
    survivors s c = [] := by
  unfold classify at h
  split at h
  · contradiction
  · cases hs : survivors s c with
    | nil => rfl
    | cons l rest => cases rest <;> simp [hs] at h

theorem unit_residual (s : Scratch) (c : Clause) (u : Literal)
    (h : classify s c = .unit u) : survivors s c = [u] := by
  unfold classify at h
  split at h
  · contradiction
  · cases hs : survivors s c with
    | nil => simp [hs] at h
    | cons l rest =>
      cases rest with
      | nil =>
        simp [hs] at h
        subst l
        rfl
      | cons next tail => simp [hs] at h

theorem conflict_premise (s : Scratch) (c : Clause) (h : classify s c = .conflict) :
    ∀ l ∈ c, FalseUnder s l := by
  intro l member
  by_cases f : FalseUnder s l
  · exact f
  · have present := (mem_survivors s c l).mpr ⟨member, f⟩
    rw [conflict_residual s c h] at present
    simp at present

theorem unit_premise (s : Scratch) (c : Clause) (u : Literal)
    (h : classify s c = .unit u) :
    u ∈ c ∧ ∀ l ∈ c, l = u ∨ FalseUnder s l := by
  have residual := unit_residual s c u h
  constructor
  · have present : u ∈ survivors s c := by rw [residual]; simp
    exact ((mem_survivors s c u).mp present).1
  · intro l member
    by_cases f : FalseUnder s l
    · exact Or.inr f
    · have present := (mem_survivors s c l).mpr ⟨member, f⟩
      rw [residual] at present
      exact Or.inl (by simpa using present)

theorem unit_unassigned (s : Scratch) (c : Clause) (u : Literal)
    (h : classify s c = .unit u) : s (u.index - 1) = none := by
  have residual := unit_residual s c u h
  have present : u ∈ survivors s c := by rw [residual]; simp
  obtain ⟨member, notFalse⟩ := (mem_survivors s c u).mp present
  have notTrue : s (u.index - 1) ≠ some u.positive := by
    intro value
    have found : c.any (fun l => decide (s (l.index - 1) = some l.positive)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨u, member, by simp [value]⟩
    simp [classify, found] at h
  unfold FalseUnder at notFalse
  cases value : s (u.index - 1) with
  | none => rfl
  | some b => cases b <;> cases u.positive <;> simp_all

theorem classified_conflict_sound (a : Assignment) (s : Scratch) (c : Clause)
    (bounds : ∀ l ∈ c, 0 < l.index) (compatible : Extends a s)
    (h : classify s c = .conflict) : ¬ SatisfiesClause a c :=
  PropagationState.conflict_sound a s c bounds compatible (conflict_premise s c h)

theorem classified_unit_write (a : Assignment) (s : Scratch) (c : Clause) (u : Literal)
    (bounds : ∀ l ∈ c, 0 < l.index) (compatible : Extends a s)
    (sat : SatisfiesClause a c) (h : classify s c = .unit u) :
    Extends a (write s (u.index - 1) u.positive) := by
  obtain ⟨member, premise⟩ := unit_premise s c u h
  exact unit_write_extends a s c u bounds (bounds u member) compatible sat premise

-- Compact wire form: 0 conflict, 1 unit, 2 satisfied, 3 unresolved.
-- The second word is meaningful only for a unit result.
def wire : Result → List Nat
  | .conflict => [0, 0]
  | .unit u => [1, Ranges.encodeLiteral u]
  | .satisfied => [2, 0]
  | .unresolved => [3, 0]

#print axioms mem_unique
#print axioms mem_survivors
#print axioms conflict_residual
#print axioms unit_residual
#print axioms conflict_premise
#print axioms unit_premise
#print axioms unit_unassigned
#print axioms classified_conflict_sound
#print axioms classified_unit_write
end OakVerification.ClauseClassifier
