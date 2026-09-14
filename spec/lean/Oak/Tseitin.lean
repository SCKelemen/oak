/-!
# The clause engine's laws

`asm/cnf.go` lowers a bit-level obligation to clauses the way `asm/bdd.go`
lowers it to a decision diagram: the same gates from the same lowering,
each distinct gate a fresh variable `g` constrained by Tseitin's clauses,
the same folds on constant and identical operands, and one obligation
clause "some trap fires or the claim is false" (`docs/spec/125-verification.md`
§3 "By certificate"). This module states what that construction relies
on, over Booleans:

- `and_clauses`, `or_clauses`, `xor_clauses`, `ite_clauses`: a gate's
  clauses hold under an assignment exactly when the gate variable equals
  the operation's value, so a model of the clauses is a consistent
  evaluation of the circuit and every consistent evaluation is a model.
- The fold laws: the engine returns an operand or a constant instead of a
  gate in the cases below; each is an identity.
- `determined`: with every gate determined by the inputs, the formula
  "definitions and obligation" is satisfiable exactly when some input
  assignment makes the obligation true, which is what lets a solver's
  `UNSATISFIABLE` stand for the theorem and its model stand for a
  counterexample after `asm.CNF.Evaluate` recomputes the gates from the
  inputs alone.

The encoder's code is cross-checked against the diagram engine over the
corpus (`prove/lrat_test.go`), not proved; these are the laws the check
rests on.
-/

namespace Oak.Tseitin

/-- The three clauses of `g ↔ (x ∧ y)`: (¬g ∨ x), (¬g ∨ y), (g ∨ ¬x ∨ ¬y). -/
def andClauses (g x y : Bool) : Bool :=
  (!g || x) && (!g || y) && (g || !x || !y)

/-- The three clauses of `g ↔ (x ∨ y)`: (g ∨ ¬x), (g ∨ ¬y), (¬g ∨ x ∨ y). -/
def orClauses (g x y : Bool) : Bool :=
  (g || !x) && (g || !y) && (!g || x || y)

/-- The four clauses of `g ↔ (x ⊕ y)`. -/
def xorClauses (g x y : Bool) : Bool :=
  (!g || x || y) && (!g || !x || !y) && (g || !x || y) && (g || x || !y)

/-- The six clauses of `g ↔ (if c then t else e)`, the last two redundant
but propagation-strengthening: when both arms agree the gate agrees. -/
def iteClauses (g c t e : Bool) : Bool :=
  (!g || !c || t) && (!g || c || e) && (g || !c || !t) && (g || c || !e)
    && (!g || t || e) && (g || !t || !e)

theorem and_clauses (g x y : Bool) : andClauses g x y = true ↔ g = (x && y) := by
  cases g <;> cases x <;> cases y <;> simp [andClauses]

theorem or_clauses (g x y : Bool) : orClauses g x y = true ↔ g = (x || y) := by
  cases g <;> cases x <;> cases y <;> simp [orClauses]

theorem xor_clauses (g x y : Bool) : xorClauses g x y = true ↔ g = xor x y := by
  cases g <;> cases x <;> cases y <;> simp [xorClauses]

theorem ite_clauses (g c t e : Bool) : iteClauses g c t e = true ↔ g = (if c then t else e) := by
  cases g <;> cases c <;> cases t <;> cases e <;> simp [iteClauses]

/-! The folds `cnfBuilder.apply` and `cnfBuilder.ite` perform instead of
emitting a gate. -/

theorem and_self (x : Bool) : (x && x) = x := by cases x <;> rfl
theorem or_self (x : Bool) : (x || x) = x := by cases x <;> rfl
theorem xor_self (x : Bool) : xor x x = false := by cases x <;> rfl
theorem and_not_self (x : Bool) : (x && !x) = false := by cases x <;> rfl
theorem or_not_self (x : Bool) : (x || !x) = true := by cases x <;> rfl
theorem xor_not_self (x : Bool) : xor x (!x) = true := by cases x <;> rfl
theorem and_false_left (y : Bool) : (false && y) = false := rfl
theorem and_true_left (y : Bool) : (true && y) = y := rfl
theorem or_false_left (y : Bool) : (false || y) = y := rfl
theorem or_true_left (y : Bool) : (true || y) = true := rfl
theorem xor_false_left (y : Bool) : xor false y = y := by cases y <;> rfl
theorem xor_true_left (y : Bool) : xor true y = !y := by cases y <;> rfl
theorem ite_true (t e : Bool) : (if true then t else e) = t := rfl
theorem ite_false (t e : Bool) : (if false then t else e) = e := rfl
theorem ite_same (c t : Bool) : (if c then t else t) = t := by cases c <;> rfl
theorem ite_select (c : Bool) : (if c then true else false) = c := by cases c <;> rfl
theorem ite_select_not (c : Bool) : (if c then false else true) = !c := by cases c <;> rfl
theorem ite_true_arm (c e : Bool) : (if c then true else e) = (c || e) := by cases c <;> cases e <;> rfl
theorem ite_false_arm (c e : Bool) : (if c then false else e) = (!c && e) := by cases c <;> cases e <;> rfl
theorem ite_true_else (c t : Bool) : (if c then t else true) = (!c || t) := by cases c <;> cases t <;> rfl
theorem ite_false_else (c t : Bool) : (if c then t else false) = (c && t) := by cases c <;> cases t <;> rfl

/-! Determination. A circuit is a function from input assignments to gate
values; the definitions hold exactly under the assignment that extends the
inputs by that function (`defs`), so the whole formula is satisfiable
exactly when the obligation is true for some input. -/

section Determined

variable {ι : Type} {γ : Type}

/-- The definitions: every gate carries the value the circuit computes
from the inputs. -/
def Defs (circuit : (ι → Bool) → γ → Bool) (inputs : ι → Bool) (gates : γ → Bool) : Prop :=
  ∀ g, gates g = circuit inputs g

/-- The obligation reads the inputs and the gates. -/
def Satisfiable (circuit : (ι → Bool) → γ → Bool) (obligation : (ι → Bool) → (γ → Bool) → Bool) : Prop :=
  ∃ inputs gates, Defs circuit inputs gates ∧ obligation inputs gates = true

theorem determined (circuit : (ι → Bool) → γ → Bool)
    (obligation : (ι → Bool) → (γ → Bool) → Bool) :
    Satisfiable circuit obligation ↔ ∃ inputs, obligation inputs (circuit inputs) = true := by
  constructor
  · rintro ⟨inputs, gates, defs, holds⟩
    refine ⟨inputs, ?_⟩
    have : gates = circuit inputs := funext defs
    simpa [this] using holds
  · rintro ⟨inputs, holds⟩
    exact ⟨inputs, circuit inputs, fun _ => rfl, holds⟩

end Determined

end Oak.Tseitin
