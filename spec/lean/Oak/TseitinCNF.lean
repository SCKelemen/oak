import Oak.RupCheck
import Oak.Tseitin

/-!
# Concrete Tseitin clauses at the RUP boundary

`Oak.Tseitin` states the Boolean laws of each gate.  `Oak.RupCheck`, however,
checks lists of signed literals.  This module connects those two
representations for the raw fresh-gate branches of `asm/cnf.go`: the exact
three, four, or six clauses emitted for AND, OR, XOR, and ITE.

This is deliberately not a refinement of the complete clause builder.  It
composes a supplied sequence of raw gates with a supplied final obligation
clause on the non-settled path and connects that clause list to the RUP
database representation.  It
does not prove that the Go builder produced that sequence or obligation, nor
does it model constant folding, gate memoization, fresh allocation, dependency
acyclicity, sequential assignment extension, the clause budget, DIMACS
serialization/parsing, or term bit-blasting.  Those remain separate
obligations before the native equality certificate's concrete `cnf_complete`
premise can be discharged.
-/

set_option autoImplicit false

namespace Oak.TseitinCNF

open Oak.RupCheck

/-- The positive literal naming a freshly allocated gate output. -/
def output (index : Nat) : Literal := ⟨index, true⟩

/-- The Boolean denoted by a signed RUP literal under an assignment. -/
def evalLiteral (assignment : Assignment) (literal : Literal) : Bool :=
  if literal.positive then assignment literal.index else !assignment literal.index

@[simp] theorem evalLiteral_output (assignment : Assignment) (index : Nat) :
    evalLiteral assignment (output index) = assignment index := by
  rfl

@[simp] theorem evalLiteral_negate (assignment : Assignment) (literal : Literal) :
    evalLiteral assignment (negate literal) = !evalLiteral assignment literal := by
  cases literal with
  | mk index positive =>
      cases positive <;> cases assignment index <;> simp [evalLiteral, negate]

theorem evalLiteral_eq_true_iff (assignment : Assignment) (literal : Literal) :
    evalLiteral assignment literal = true ↔ Holds assignment literal := by
  cases literal with
  | mk index positive =>
      cases positive <;> cases assignment index <;> simp [evalLiteral, Holds]

/-- Boolean evaluation of one concrete RUP clause. -/
def clauseValue (assignment : Assignment) (clause : Clause) : Bool :=
  clause.any (evalLiteral assignment)

/-- Boolean evaluation of a concrete list of RUP clauses. -/
def clausesValue (assignment : Assignment) (clauses : List Clause) : Bool :=
  clauses.all (clauseValue assignment)

/-- The propositional reading of a concrete list of clauses. -/
def SatisfiesClauses (assignment : Assignment) (clauses : List Clause) : Prop :=
  ∀ clause ∈ clauses, SatisfiesClause assignment clause

theorem clauseValue_eq_true_iff (assignment : Assignment) (clause : Clause) :
    clauseValue assignment clause = true ↔ SatisfiesClause assignment clause := by
  simp [clauseValue, SatisfiesClause, evalLiteral_eq_true_iff]

theorem clausesValue_eq_true_iff (assignment : Assignment) (clauses : List Clause) :
    clausesValue assignment clauses = true ↔ SatisfiesClauses assignment clauses := by
  simp [clausesValue, SatisfiesClauses, clauseValue_eq_true_iff]

/-! The lists below preserve the clause and literal order in `cnfBuilder`.
For binary gates, `left` and `right` are the canonical order after the Go
builder's `x > y` swap.  The order is irrelevant to their semantics but
keeping it explicit gives the Go-side correspondence test one canonical
representation to pin. -/

def andGateClauses (gate : Nat) (left right : Literal) : List Clause :=
  [[negate (output gate), left],
   [negate (output gate), right],
   [output gate, negate left, negate right]]

def orGateClauses (gate : Nat) (left right : Literal) : List Clause :=
  [[output gate, negate left],
   [output gate, negate right],
   [negate (output gate), left, right]]

def xorGateClauses (gate : Nat) (left right : Literal) : List Clause :=
  [[negate (output gate), left, right],
   [negate (output gate), negate left, negate right],
   [output gate, negate left, right],
   [output gate, left, negate right]]

def iteGateClauses (gate : Nat) (condition thenValue elseValue : Literal) : List Clause :=
  [[negate (output gate), negate condition, thenValue],
   [negate (output gate), condition, elseValue],
   [output gate, negate condition, negate thenValue],
   [output gate, condition, negate elseValue],
   [negate (output gate), thenValue, elseValue],
   [output gate, negate thenValue, negate elseValue]]

theorem andGate_value (assignment : Assignment) (gate : Nat) (left right : Literal) :
    clausesValue assignment (andGateClauses gate left right) =
      Oak.Tseitin.andClauses (assignment gate) (evalLiteral assignment left)
        (evalLiteral assignment right) := by
  simp [clausesValue, clauseValue, andGateClauses, Oak.Tseitin.andClauses,
    Bool.and_assoc, Bool.or_assoc]

theorem orGate_value (assignment : Assignment) (gate : Nat) (left right : Literal) :
    clausesValue assignment (orGateClauses gate left right) =
      Oak.Tseitin.orClauses (assignment gate) (evalLiteral assignment left)
        (evalLiteral assignment right) := by
  simp [clausesValue, clauseValue, orGateClauses, Oak.Tseitin.orClauses,
    Bool.and_assoc, Bool.or_assoc]

theorem xorGate_value (assignment : Assignment) (gate : Nat) (left right : Literal) :
    clausesValue assignment (xorGateClauses gate left right) =
      Oak.Tseitin.xorClauses (assignment gate) (evalLiteral assignment left)
        (evalLiteral assignment right) := by
  simp [clausesValue, clauseValue, xorGateClauses, Oak.Tseitin.xorClauses,
    Bool.and_assoc, Bool.or_assoc]

theorem iteGate_value (assignment : Assignment) (gate : Nat)
    (condition thenValue elseValue : Literal) :
    clausesValue assignment (iteGateClauses gate condition thenValue elseValue) =
      Oak.Tseitin.iteClauses (assignment gate) (evalLiteral assignment condition)
        (evalLiteral assignment thenValue) (evalLiteral assignment elseValue) := by
  simp [clausesValue, clauseValue, iteGateClauses, Oak.Tseitin.iteClauses,
    Bool.and_assoc, Bool.or_assoc]

/-- The exact three RUP clauses for a raw AND gate characterize its output. -/
theorem satisfies_andGate_iff (assignment : Assignment) (gate : Nat)
    (left right : Literal) :
    SatisfiesClauses assignment (andGateClauses gate left right) ↔
      assignment gate = (evalLiteral assignment left && evalLiteral assignment right) := by
  rw [← clausesValue_eq_true_iff, andGate_value]
  exact Oak.Tseitin.and_clauses _ _ _

/-- The exact three RUP clauses for a raw OR gate characterize its output. -/
theorem satisfies_orGate_iff (assignment : Assignment) (gate : Nat)
    (left right : Literal) :
    SatisfiesClauses assignment (orGateClauses gate left right) ↔
      assignment gate = (evalLiteral assignment left || evalLiteral assignment right) := by
  rw [← clausesValue_eq_true_iff, orGate_value]
  exact Oak.Tseitin.or_clauses _ _ _

/-- The exact four RUP clauses for a raw XOR gate characterize its output. -/
theorem satisfies_xorGate_iff (assignment : Assignment) (gate : Nat)
    (left right : Literal) :
    SatisfiesClauses assignment (xorGateClauses gate left right) ↔
      assignment gate = xor (evalLiteral assignment left) (evalLiteral assignment right) := by
  rw [← clausesValue_eq_true_iff, xorGate_value]
  exact Oak.Tseitin.xor_clauses _ _ _

/-- The exact six RUP clauses for a raw ITE gate characterize its output. -/
theorem satisfies_iteGate_iff (assignment : Assignment) (gate : Nat)
    (condition thenValue elseValue : Literal) :
    SatisfiesClauses assignment (iteGateClauses gate condition thenValue elseValue) ↔
      assignment gate =
        (if evalLiteral assignment condition then evalLiteral assignment thenValue
         else evalLiteral assignment elseValue) := by
  rw [← clausesValue_eq_true_iff, iteGate_value]
  exact Oak.Tseitin.ite_clauses _ _ _ _

/-! ## A supplied sequence of raw gates

`RawGate` is the decoded immutable logical counterpart of one raw-edge entry
in `cnfBuilder.gates`.  It intentionally starts after all folds, memo hits and
allocation decisions: proving that those mutable Go operations produce this
record is a later implementation-refinement obligation. -/

inductive RawGate where
  | andGate (gate : Nat) (left right : Literal)
  | orGate (gate : Nat) (left right : Literal)
  | xorGate (gate : Nat) (left right : Literal)
  | iteGate (gate : Nat) (condition thenValue elseValue : Literal)
  deriving Repr

def RawGate.clauses : RawGate → List Clause
  | .andGate gate left right => andGateClauses gate left right
  | .orGate gate left right => orGateClauses gate left right
  | .xorGate gate left right => xorGateClauses gate left right
  | .iteGate gate condition thenValue elseValue =>
      iteGateClauses gate condition thenValue elseValue

/-- The Boolean equation characterized by one raw gate's concrete clauses. -/
def RawGate.Holds (assignment : Assignment) : RawGate → Prop
  | .andGate gate left right =>
      assignment gate = (evalLiteral assignment left && evalLiteral assignment right)
  | .orGate gate left right =>
      assignment gate = (evalLiteral assignment left || evalLiteral assignment right)
  | .xorGate gate left right =>
      assignment gate = xor (evalLiteral assignment left) (evalLiteral assignment right)
  | .iteGate gate condition thenValue elseValue =>
      assignment gate =
        (if evalLiteral assignment condition then evalLiteral assignment thenValue
         else evalLiteral assignment elseValue)

def gateClauses (gates : List RawGate) : List Clause :=
  gates.flatMap RawGate.clauses

def builderClauses (gates : List RawGate) (obligation : Clause) : List Clause :=
  gateClauses gates ++ [obligation]

def GateConsistent (assignment : Assignment) (gates : List RawGate) : Prop :=
  ∀ gate ∈ gates, gate.Holds assignment

theorem satisfiesClauses_append (assignment : Assignment) (left right : List Clause) :
    SatisfiesClauses assignment (left ++ right) ↔
      SatisfiesClauses assignment left ∧ SatisfiesClauses assignment right := by
  constructor
  · intro satisfies
    constructor
    · intro clause member
      exact satisfies clause (by simp [member])
    · intro clause member
      exact satisfies clause (by simp [member])
  · rintro ⟨leftSatisfies, rightSatisfies⟩ clause member
    rcases List.mem_append.mp member with member | member
    · exact leftSatisfies clause member
    · exact rightSatisfies clause member

/-- Each raw-gate variant delegates to its exact concrete clause theorem. -/
theorem satisfies_rawGate_iff (assignment : Assignment) (gate : RawGate) :
    SatisfiesClauses assignment gate.clauses ↔ gate.Holds assignment := by
  cases gate with
  | andGate gate left right => exact satisfies_andGate_iff assignment gate left right
  | orGate gate left right => exact satisfies_orGate_iff assignment gate left right
  | xorGate gate left right => exact satisfies_xorGate_iff assignment gate left right
  | iteGate gate condition thenValue elseValue =>
      exact satisfies_iteGate_iff assignment gate condition thenValue elseValue

/-- Concatenating raw-gate clause blocks means satisfying every gate equation.
No freshness or dependency order is needed for this propositional statement. -/
theorem satisfies_gateClauses_iff (assignment : Assignment) (gates : List RawGate) :
    SatisfiesClauses assignment (gateClauses gates) ↔ GateConsistent assignment gates := by
  induction gates with
  | nil => simp [gateClauses, GateConsistent, SatisfiesClauses]
  | cons gate rest ih =>
      rw [show gateClauses (gate :: rest) = gate.clauses ++ gateClauses rest by rfl]
      rw [satisfiesClauses_append, satisfies_rawGate_iff, ih]
      simp [GateConsistent]

/-- The supplied builder formula is exactly all gate equations conjoined with
the supplied final obligation clause. -/
theorem satisfies_builderClauses_iff (assignment : Assignment) (gates : List RawGate)
    (obligation : Clause) :
    SatisfiesClauses assignment (builderClauses gates obligation) ↔
      GateConsistent assignment gates ∧ SatisfiesClause assignment obligation := by
  rw [builderClauses, satisfiesClauses_append, satisfies_gateClauses_iff]
  simp [SatisfiesClauses]

/-! ## The one-based RUP database

DIMACS clause 1 is the list head and database id 0 is absent.  This closes the
representation gap between the concrete clause lists above and
`Oak.RupCheck.Models`; it is not a parser or serializer refinement. -/

def databaseOfClauses : List Clause → Database
  | [] => fun _ => none
  | clause :: rest => fun
      | 0 => none
      | 1 => some clause
      | Nat.succ (Nat.succ id) => databaseOfClauses rest (Nat.succ id)

@[simp] theorem databaseOfClauses_zero (clauses : List Clause) :
    databaseOfClauses clauses 0 = none := by
  cases clauses <;> rfl

@[simp] theorem databaseOfClauses_cons_one (clause : Clause) (rest : List Clause) :
    databaseOfClauses (clause :: rest) 1 = some clause := by
  rfl

@[simp] theorem databaseOfClauses_cons_succ_succ (clause : Clause)
    (rest : List Clause) (id : Nat) :
    databaseOfClauses (clause :: rest) (Nat.succ (Nat.succ id)) =
      databaseOfClauses rest (Nat.succ id) := by
  rfl

example (clause : Clause) : databaseOfClauses [clause] 2 = none := rfl

example (clause : Clause) :
    databaseOfClauses [clause, clause] 1 = some clause ∧
      databaseOfClauses [clause, clause] 2 = some clause := by
  constructor <;> rfl

example : databaseOfClauses ([[]] : List Clause) 1 = some [] := rfl

theorem models_databaseOfClauses_iff (assignment : Assignment) (clauses : List Clause) :
    Models assignment (databaseOfClauses clauses) ↔
      SatisfiesClauses assignment clauses := by
  induction clauses with
  | nil =>
      constructor
      · intro _ clause member
        simp at member
      · intro _ id clause lookup
        simp [databaseOfClauses] at lookup
  | cons head tail ih =>
      constructor
      · intro models
        have headModel : SatisfiesClause assignment head :=
          models 1 head (by simp [databaseOfClauses])
        have tailModels : Models assignment (databaseOfClauses tail) := by
          intro id clause lookup
          cases id with
          | zero => simp at lookup
          | succ id =>
              exact models (Nat.succ (Nat.succ id)) clause
                (by simpa [databaseOfClauses] using lookup)
        intro clause member
        rcases List.mem_cons.mp member with rfl | member
        · exact headModel
        · exact ih.mp tailModels clause member
      · intro satisfies
        have headModel : SatisfiesClause assignment head :=
          satisfies head (by simp)
        have tailModels : Models assignment (databaseOfClauses tail) :=
          ih.mpr (by
            intro clause member
            exact satisfies clause (by simp [member]))
        intro id clause lookup
        cases id with
        | zero => simp [databaseOfClauses] at lookup
        | succ id =>
            cases id with
            | zero =>
                have eq : head = clause := by
                  simpa [databaseOfClauses] using lookup
                simpa [eq] using headModel
            | succ id =>
                exact tailModels (Nat.succ id) clause
                  (by simpa [databaseOfClauses] using lookup)

/-- The exact model characterization at the abstract RUP database boundary. -/
theorem models_builderDatabase_iff (assignment : Assignment) (gates : List RawGate)
    (obligation : Clause) :
    Models assignment (databaseOfClauses (builderClauses gates obligation)) ↔
      GateConsistent assignment gates ∧ SatisfiesClause assignment obligation := by
  rw [models_databaseOfClauses_iff, satisfies_builderClauses_iff]

/-! A two-gate example pins concatenation and dependency representation.  Its
second gate reads the first gate's output.  This does not prove that arbitrary
sequences are fresh or acyclic. -/

namespace SequenceExample

def gates : List RawGate :=
  [.andGate 3 (output 1) (output 2),
   .xorGate 4 (negate (output 1)) (output 3)]

def obligation : Clause := [output 4]

example : builderClauses gates obligation =
    [[⟨3, false⟩, ⟨1, true⟩],
     [⟨3, false⟩, ⟨2, true⟩],
     [⟨3, true⟩, ⟨1, false⟩, ⟨2, false⟩],
     [⟨4, false⟩, ⟨1, false⟩, ⟨3, true⟩],
     [⟨4, false⟩, ⟨1, true⟩, ⟨3, false⟩],
     [⟨4, true⟩, ⟨1, true⟩, ⟨3, true⟩],
     [⟨4, true⟩, ⟨1, false⟩, ⟨3, false⟩],
     [⟨4, true⟩]] := by
  rfl

example (assignment : Assignment) :
    Models assignment (databaseOfClauses (builderClauses gates obligation)) ↔
      GateConsistent assignment gates ∧ SatisfiesClause assignment obligation :=
  models_builderDatabase_iff assignment gates obligation

end SequenceExample

end Oak.TseitinCNF
