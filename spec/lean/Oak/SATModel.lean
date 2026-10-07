import Oak.SATModelExtracted
import Oak.RupCheck

/-!
# SAT-model evidence

`SATModelExtracted` is the complete production Oak model checker, including
its fuel-bounded loops. A drift test regenerates it, and formal CI compares
its kernel-reduced decisions with compiled Oak on raw formula/model words.

The scalar theorems below prove the extracted assignment/literal predicates.
The clause-list model then composes checked literals into a model of the
decoded database. `Oak.SATModelSoundness` derives exact decoding and a model
from successful execution of the generated framing/scan loops, for UInt32
view lengths. Extraction, compilation, and source-to-CNF lowering remain
separate obligations. Bounded replay is additional implementation evidence.
The new loop proof awaits its first successful mandatory formal-CI kernel
build; its refinement obligation is not yet recorded as closed.
-/

set_option autoImplicit false

namespace Oak.SATModel

theorem value_accepted (value : UInt32) (fuel : Nat) :
    sat_model_value value fuel = some true ↔ value = 1 ∨ value = 2 := by
  simp [sat_model_value]

/-- A true result from the extracted literal predicate has exactly the
polarity of the raw literal under the complete assignment's Boolean value. -/
theorem literal_value_sound (lit value : UInt32) (fuel : Nat)
    (accepted : sat_model_literal lit value fuel = some true) :
    (value == 2) = (lit % 2 == 1) := by
  by_cases positive : lit % 2 = 1
  · have valueTrue : value = 2 := by
      simpa [sat_model_literal, positive] using accepted
    simp [valueTrue, positive]
  · have valueFalse : value = 1 := by
      simpa [sat_model_literal, positive] using accepted
    simp [valueFalse, positive]

def literal (word : UInt32) : Oak.RupCheck.Literal :=
  ⟨(word / 2).toNat, word % 2 == 1⟩

def assignment (values : List UInt32) : Oak.RupCheck.Assignment :=
  fun index => values[index]?.getD 0 == 2

def acceptsLiteral (values : List UInt32) (word : UInt32) : Bool :=
  match values[(word / 2).toNat]? with
  | none => false
  | some value => (sat_model_literal word value 0).getD false

theorem accepted_literal {values : List UInt32} {word : UInt32}
    (accepted : acceptsLiteral values word = true) :
    Oak.RupCheck.Holds (assignment values) (literal word) := by
  unfold acceptsLiteral at accepted
  -- Match the Nat index produced by the UInt32 division simp rules.
  cases found : values[word.toNat / 2]? with
  | none => simp [found] at accepted
  | some value =>
      have checked : sat_model_literal word value 0 = some true := by
        simpa [found, sat_model_literal] using accepted
      have sound := literal_value_sound word value 0 checked
      simpa [Oak.RupCheck.Holds, assignment, literal, found] using sound

def acceptsClauses (values : List UInt32) (clauses : List (List UInt32)) : Bool :=
  clauses.all (fun clause => clause.any (acceptsLiteral values))

/-- The raw clauses use the same zero-based variable index and polarity as
the extracted literal checker. Clause identifiers start at one. -/
def database (clauses : List (List UInt32)) : Oak.RupCheck.Database :=
  fun id => if id = 0 then none
    else (clauses[id - 1]?).map (List.map literal)

theorem accepted_clauses {values : List UInt32} {clauses : List (List UInt32)}
    (accepted : acceptsClauses values clauses = true) :
    Oak.RupCheck.Models (assignment values) (database clauses) := by
  intro id clause found
  unfold database at found
  split at found
  · contradiction
  · cases lookup : clauses[id - 1]? with
    | none => simp [lookup] at found
    | some words =>
        have clauseEq : words.map literal = clause := by simpa [lookup] using found
        have member : words ∈ clauses := List.mem_of_getElem? lookup
        have holds : words.any (acceptsLiteral values) = true :=
          List.all_eq_true.mp accepted words member
        obtain ⟨word, inClause, checked⟩ := List.any_eq_true.mp holds
        refine ⟨literal word, ?_, accepted_literal checked⟩
        rw [← clauseEq]
        exact List.mem_map.mpr ⟨word, inClause, rfl⟩

/-- Checked SAT evidence and accepted RUP evidence cannot describe the same
decoded clause database. This does not assume the solver's status is sound. -/
theorem checked_sat_not_rup {values : List UInt32} {clauses : List (List UInt32)}
    (accepted : acceptsClauses values clauses = true) :
    ¬ Oak.RupCheck.Accepted (database clauses) := by
  intro refutation
  exact Oak.RupCheck.accepted_unsatisfiable refutation
    (assignment values) (accepted_clauses accepted)

end Oak.SATModel
