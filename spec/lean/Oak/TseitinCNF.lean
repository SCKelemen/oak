import Oak.RupCheck
import Oak.Tseitin

/-!
# Concrete Tseitin clauses at the RUP boundary

`Oak.Tseitin` states the Boolean laws of each gate.  `Oak.RupCheck`, however,
checks lists of signed literals.  This module connects those two
representations for the raw fresh-gate branches of `asm/cnf.go`: the exact
three, four, or six clauses emitted for AND, OR, XOR, and ITE.

This is deliberately not a refinement of the complete clause builder.  It
does not model constant folding, gate memoization or allocation, a sequence of
dependent gates, the final obligation clause, DIMACS parsing, or term
bit-blasting.  Those remain separate obligations before the native equality
certificate's concrete `cnf_complete` premise can be discharged.
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

end Oak.TseitinCNF
