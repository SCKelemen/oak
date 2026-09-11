/-!
# Oak.ProtocolConformance — a checker's verdict on two machines

`docs/spec/112-protocols.md` section 4a compares a hand-written TLA+ module
with a protocol projection in the projection's normal form: a machine is a
finite set of lines, each `(action, from, guard, to, effect)`, plus an
initial condition. The checker reports the symmetric difference of the two
line sets (and of the initial conditions). This module proves what that
verdict means:

* `steps_of_lines`: two machines with the same lines have the same step
  relation, whatever the guards and effects denote.
* `conform_reachable_equal`: with the same initial states as well, they
  reach the same states — the checker's "agrees" is trace equivalence, not
  a textual coincidence.
* `report_complete`: a difference in the line sets is a line the report
  names; an empty report means equal sets.
-/

namespace Oak.ProtocolConformance

variable {S A G E : Type} [DecidableEq S] [DecidableEq A] [DecidableEq G] [DecidableEq E]

/-- One disjunct of an action in normal form. Guards and effects are
compared by identity (their canonical spelling); their meaning is given by
the interpretation below. -/
structure Line (S A G E : Type) where
  action : A
  from_ : S
  guard : G
  to : S
  effect : E
  deriving DecidableEq

/-- A machine: its lines and its initial states. -/
structure Machine (S A G E : Type) where
  lines : List (Line S A G E)
  initial : S → Prop

/-- An interpretation of guards and effects over data `D`. -/
structure Interp (G E D : Type) where
  holds : G → D → Prop
  apply : E → D → D

/-- The step relation a machine denotes under an interpretation. -/
def Step (I : Interp G E D) (M : Machine S A G E) : (S × D) → A → (S × D) → Prop :=
  fun ⟨s, d⟩ a ⟨s', d'⟩ =>
    ∃ l ∈ M.lines, l.action = a ∧ l.from_ = s ∧ I.holds l.guard d ∧ l.to = s' ∧ I.apply l.effect d = d'

/-- Same lines, same steps: the step relation is a function of the line set. -/
theorem steps_of_lines {D : Type} (I : Interp G E D) (M N : Machine S A G E)
    (h : ∀ l, l ∈ M.lines ↔ l ∈ N.lines) : ∀ x a y, Step I M x a y ↔ Step I N x a y := by
  intro ⟨s, d⟩ a ⟨s', d'⟩
  simp only [Step]
  constructor
  · rintro ⟨l, hl, rest⟩
    exact ⟨l, (h l).mp hl, rest⟩
  · rintro ⟨l, hl, rest⟩
    exact ⟨l, (h l).mpr hl, rest⟩

/-- Reachability under a step relation. -/
inductive Reach {D : Type} (I : Interp G E D) (M : Machine S A G E) : (S × D) → Prop where
  | init (s : S) (d : D) (h : M.initial s) : Reach I M (s, d)
  | step (x y : S × D) (a : A) (hx : Reach I M x) (hs : Step I M x a y) : Reach I M y

theorem conform_reachable_equal {D : Type} (I : Interp G E D) (M N : Machine S A G E)
    (hl : ∀ l, l ∈ M.lines ↔ l ∈ N.lines) (hi : ∀ s, M.initial s ↔ N.initial s) :
    ∀ x, Reach I M x ↔ Reach I N x := by
  intro x
  constructor
  · intro h
    induction h with
    | init s d h0 => exact Reach.init s d ((hi s).mp h0)
    | step x y a _ hs ih => exact Reach.step x y a ih ((steps_of_lines I M N hl x a y).mp hs)
  · intro h
    induction h with
    | init s d h0 => exact Reach.init s d ((hi s).mpr h0)
    | step x y a _ hs ih => exact Reach.step x y a ih ((steps_of_lines I M N hl x a y).mpr hs)

/-- The checker's report: lines on one side and not the other. -/
def report (M N : Machine S A G E) : List (Line S A G E) :=
  M.lines.filter (fun l => !(N.lines.contains l)) ++ N.lines.filter (fun l => !(M.lines.contains l))

/-- Completeness: a line set difference is a reported line, and an empty
report means the line sets agree. -/
theorem report_complete (M N : Machine S A G E) (l : Line S A G E)
    (h : ¬ (l ∈ M.lines ↔ l ∈ N.lines)) : l ∈ report M N := by
  unfold report
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  by_cases hm : l ∈ M.lines
  · by_cases hn : l ∈ N.lines
    · exact absurd ⟨fun _ => hn, fun _ => hm⟩ h
    · exact Or.inl ⟨hm, hn⟩
  · by_cases hn : l ∈ N.lines
    · exact Or.inr ⟨hn, hm⟩
    · exact absurd ⟨fun hm' => absurd hm' hm, fun hn' => absurd hn' hn⟩ h

theorem empty_report_agrees (M N : Machine S A G E) (h : report M N = []) :
    ∀ l, l ∈ M.lines ↔ l ∈ N.lines := by
  intro l
  by_cases hm : l ∈ M.lines
  · by_cases hn : l ∈ N.lines
    · exact ⟨fun _ => hn, fun _ => hm⟩
    · have := report_complete M N l (fun hiff => hn (hiff.mp hm))
      rw [h] at this
      exact absurd this List.not_mem_nil
  · by_cases hn : l ∈ N.lines
    · have := report_complete M N l (fun hiff => hm (hiff.mpr hn))
      rw [h] at this
      exact absurd this List.not_mem_nil
    · exact ⟨fun hm' => absurd hm' hm, fun hn' => absurd hn' hn⟩

end Oak.ProtocolConformance
