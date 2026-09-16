import Oak.CNFBuilderTrace
import Oak.CNFFinalObligation

/-!
# A bounded Boolean-term to CNF-root semantics bridge

This module closes one deliberately small formal part of term-to-root
semantics.  A normalized one-bit Boolean term can contain constants,
designated positive input indices, complement, and gate-emitting AND, OR, XOR,
and ITE nodes.  `Encodes gates term root` is supplied evidence that each
connective is represented by the corresponding recorded raw gate.  Under a
gate-consistent assignment, the decoded root then has exactly the term's
Boolean value.  The result composes with `Oak.CNFFinalObligation` and the exact
builder database model.

This is not a refinement proof of Go's `term` or bit blaster.  In particular,
it does not prove that an actual Go term satisfies `Encodes`, that input names
or source traps map to these designated indices, that those indices occur in a
supplied allocation trace, or that the Go builder records every required gate.
General constant/identity folds, Go gate-memo-hit semantics, widths and adaptation,
arithmetic, comparisons and flags,
selects, floating point, quantifiers, term/source provenance, clause budgets,
DIMACS serialization/parsing, and `cnf_complete` remain open.  The normalized
`complement` node states the semantic rung used by Boolean negation; it does
not prove Go's xor-with-true fold.  Raw-gate uniqueness and allocation order
also remain the separate supplied-trace obligation checked by
`Oak.CNFBuilderTrace`; connecting the term inputs to that trace remains open.
-/

set_option autoImplicit false

namespace Oak.CNFTermRoot

open Oak.RupCheck
open Oak.TseitinCNF
open Oak.CNFFinalObligation

/-- A normalized, one-bit Boolean shell over designated positive CNF inputs. -/
inductive BoolTerm where
  | constant (value : Bool)
  | input (index : Nat)
  | complement (term : BoolTerm)
  | andTerm (left right : BoolTerm)
  | orTerm (left right : BoolTerm)
  | xorTerm (left right : BoolTerm)
  | iteTerm (condition thenValue elseValue : BoolTerm)
  deriving Repr

def BoolTerm.eval (assignment : Assignment) : BoolTerm → Bool
  | .constant value => value
  | .input index => assignment index
  | .complement term => !(term.eval assignment)
  | .andTerm left right => left.eval assignment && right.eval assignment
  | .orTerm left right => left.eval assignment || right.eval assignment
  | .xorTerm left right => xor (left.eval assignment) (right.eval assignment)
  | .iteTerm condition thenValue elseValue =>
      if condition.eval assignment then thenValue.eval assignment
      else elseValue.eval assignment

/-- Complement a decoded root using the same polarity convention as a CNF
edge's low bit. -/
def complementRoot : Root → Root
  | .constant value => .constant (!value)
  | .literal literal => .literal (negate literal)

@[simp] theorem eval_complementRoot (assignment : Assignment) (root : Root) :
    (complementRoot root).eval assignment = !(root.eval assignment) := by
  cases root with
  | constant value => rfl
  | literal literal => simp [complementRoot, Root.eval]

/-- A supplied semantic correspondence between one normalized Boolean term
and one decoded root.  Binary raw gates may record either child orientation:
their operations are commutative, while the concrete builder orders encoded
edges before recording them. -/
inductive Encodes (gates : List RawGate) : BoolTerm → Root → Prop where
  | constant (value : Bool) :
      Encodes gates (.constant value) (.constant value)
  | input (index : Nat) (positive : 0 < index) :
      Encodes gates (.input index) (.literal (output index))
  | complement {term : BoolTerm} {root : Root}
      (encoded : Encodes gates term root) :
      Encodes gates (.complement term) (complementRoot root)
  | andGate {leftTerm rightTerm : BoolTerm} {left right : Literal} {gate : Nat}
      (leftEncoded : Encodes gates leftTerm (.literal left))
      (rightEncoded : Encodes gates rightTerm (.literal right))
      (recorded : RawGate.andGate gate left right ∈ gates ∨
        RawGate.andGate gate right left ∈ gates) :
      Encodes gates (.andTerm leftTerm rightTerm) (.literal (output gate))
  | orGate {leftTerm rightTerm : BoolTerm} {left right : Literal} {gate : Nat}
      (leftEncoded : Encodes gates leftTerm (.literal left))
      (rightEncoded : Encodes gates rightTerm (.literal right))
      (recorded : RawGate.orGate gate left right ∈ gates ∨
        RawGate.orGate gate right left ∈ gates) :
      Encodes gates (.orTerm leftTerm rightTerm) (.literal (output gate))
  | xorGate {leftTerm rightTerm : BoolTerm} {left right : Literal} {gate : Nat}
      (leftEncoded : Encodes gates leftTerm (.literal left))
      (rightEncoded : Encodes gates rightTerm (.literal right))
      (recorded : RawGate.xorGate gate left right ∈ gates ∨
        RawGate.xorGate gate right left ∈ gates) :
      Encodes gates (.xorTerm leftTerm rightTerm) (.literal (output gate))
  | iteGate {conditionTerm thenTerm elseTerm : BoolTerm}
      {condition thenValue elseValue : Literal} {gate : Nat}
      (conditionEncoded : Encodes gates conditionTerm (.literal condition))
      (thenEncoded : Encodes gates thenTerm (.literal thenValue))
      (elseEncoded : Encodes gates elseTerm (.literal elseValue))
      (recorded : RawGate.iteGate gate condition thenValue elseValue ∈ gates) :
      Encodes gates (.iteTerm conditionTerm thenTerm elseTerm)
        (.literal (output gate))

/-- The supplied term/root relation is semantically sound under every model
of the recorded gate equations. -/
theorem Encodes.eval_eq {gates : List RawGate} {term : BoolTerm} {root : Root}
    (encoded : Encodes gates term root) (assignment : Assignment)
    (consistent : GateConsistent assignment gates) :
    root.eval assignment = term.eval assignment := by
  induction encoded with
  | constant value => rfl
  | input index positive => rfl
  | complement encoded ih =>
      simp [BoolTerm.eval, ih]
  | @andGate leftTerm rightTerm left right gate leftEncoded rightEncoded recorded
      leftIH rightIH =>
      have leftMeaning : evalLiteral assignment left = leftTerm.eval assignment := by
        simpa [Root.eval] using leftIH
      have rightMeaning : evalLiteral assignment right = rightTerm.eval assignment := by
        simpa [Root.eval] using rightIH
      rcases recorded with recorded | recorded
      · have holds := consistent (.andGate gate left right) recorded
        simpa [Root.eval, BoolTerm.eval, RawGate.Holds, RawGate.value,
          RawGate.outputIndex, leftMeaning, rightMeaning] using holds
      · have holds := consistent (.andGate gate right left) recorded
        simpa [Root.eval, BoolTerm.eval, RawGate.Holds, RawGate.value,
          RawGate.outputIndex, leftMeaning, rightMeaning,
          Bool.and_comm] using holds
  | @orGate leftTerm rightTerm left right gate leftEncoded rightEncoded recorded
      leftIH rightIH =>
      have leftMeaning : evalLiteral assignment left = leftTerm.eval assignment := by
        simpa [Root.eval] using leftIH
      have rightMeaning : evalLiteral assignment right = rightTerm.eval assignment := by
        simpa [Root.eval] using rightIH
      rcases recorded with recorded | recorded
      · have holds := consistent (.orGate gate left right) recorded
        simpa [Root.eval, BoolTerm.eval, RawGate.Holds, RawGate.value,
          RawGate.outputIndex, leftMeaning, rightMeaning] using holds
      · have holds := consistent (.orGate gate right left) recorded
        simpa [Root.eval, BoolTerm.eval, RawGate.Holds, RawGate.value,
          RawGate.outputIndex, leftMeaning, rightMeaning,
          Bool.or_comm] using holds
  | @xorGate leftTerm rightTerm left right gate leftEncoded rightEncoded recorded
      leftIH rightIH =>
      have leftMeaning : evalLiteral assignment left = leftTerm.eval assignment := by
        simpa [Root.eval] using leftIH
      have rightMeaning : evalLiteral assignment right = rightTerm.eval assignment := by
        simpa [Root.eval] using rightIH
      rcases recorded with recorded | recorded
      · have holds := consistent (.xorGate gate left right) recorded
        simpa [Root.eval, BoolTerm.eval, RawGate.Holds, RawGate.value,
          RawGate.outputIndex, leftMeaning, rightMeaning] using holds
      · have holds := consistent (.xorGate gate right left) recorded
        simpa [Root.eval, BoolTerm.eval, RawGate.Holds, RawGate.value,
          RawGate.outputIndex, leftMeaning, rightMeaning,
          Bool.xor_comm] using holds
  | @iteGate conditionTerm thenTerm elseTerm condition thenValue elseValue gate
      conditionEncoded thenEncoded elseEncoded recorded conditionIH thenIH elseIH =>
      have conditionMeaning :
          evalLiteral assignment condition = conditionTerm.eval assignment := by
        simpa [Root.eval] using conditionIH
      have thenMeaning :
          evalLiteral assignment thenValue = thenTerm.eval assignment := by
        simpa [Root.eval] using thenIH
      have elseMeaning :
          evalLiteral assignment elseValue = elseTerm.eval assignment := by
        simpa [Root.eval] using elseIH
      have holds := consistent (.iteGate gate condition thenValue elseValue) recorded
      simpa [Root.eval, BoolTerm.eval, RawGate.Holds, RawGate.value,
        RawGate.outputIndex, conditionMeaning, thenMeaning, elseMeaning] using holds

/-- A counterexample stated over the bounded Boolean-term model. -/
def TermCounterexample (assignment : Assignment) (traps : List BoolTerm)
    (claim : BoolTerm) : Prop :=
  (∃ trap ∈ traps, trap.eval assignment = true) ∨ claim.eval assignment = false

/-- Pointwise correspondence between two lists.  It is local here because the
Lean core list library used by the specification does not supply this
two-list relation. -/
inductive Forall₂ {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ relation [] []
  | cons {left : α} {right : β} {lefts : List α} {rights : List β}
      (head : relation left right) (tail : Forall₂ relation lefts rights) :
      Forall₂ relation (left :: lefts) (right :: rights)

theorem forall₂_traps_fire_iff {gates : List RawGate} {terms : List BoolTerm}
    {roots : List Root} (encoded : Forall₂ (Encodes gates) terms roots)
    (assignment : Assignment) (consistent : GateConsistent assignment gates) :
    (∃ root ∈ roots, root.eval assignment = true) ↔
      ∃ term ∈ terms, term.eval assignment = true := by
  induction encoded with
  | nil => simp
  | @cons term root terms roots head tail ih =>
      have meaning := head.eval_eq assignment consistent
      simp only [List.mem_cons]
      constructor
      · rintro ⟨candidate, rfl | member, fires⟩
        · exact ⟨term, Or.inl rfl, by simpa [meaning] using fires⟩
        · rcases ih.mp ⟨candidate, member, fires⟩ with ⟨rest, restMember, restFires⟩
          exact ⟨rest, Or.inr restMember, restFires⟩
      · rintro ⟨candidate, rfl | member, fires⟩
        · exact ⟨root, Or.inl rfl, by simpa [meaning] using fires⟩
        · rcases ih.mpr ⟨candidate, member, fires⟩ with ⟨rest, restMember, restFires⟩
          exact ⟨rest, Or.inr restMember, restFires⟩

/-- Supplied encodings transport the decoded-root counterexample condition to
the bounded term semantics. -/
theorem counterexample_iff {gates : List RawGate} {termTraps : List BoolTerm}
    {rootTraps : List Root} {termClaim : BoolTerm} {rootClaim : Root}
    (trapsEncoded : Forall₂ (Encodes gates) termTraps rootTraps)
    (claimEncoded : Encodes gates termClaim rootClaim)
    (assignment : Assignment) (consistent : GateConsistent assignment gates) :
    Counterexample assignment rootTraps rootClaim ↔
      TermCounterexample assignment termTraps termClaim := by
  unfold Counterexample TermCounterexample
  rw [forall₂_traps_fire_iff trapsEncoded assignment consistent,
    claimEncoded.eval_eq assignment consistent]

/-- A model of the exact pending builder database is precisely a consistent
gate assignment that is a counterexample in the bounded term language. -/
theorem pending_builderDatabase_terms_iff (assignment : Assignment)
    (gates : List RawGate) {termTraps : List BoolTerm} {rootTraps : List Root}
    {termClaim : BoolTerm} {rootClaim : Root} {clause : Clause}
    (trapsEncoded : Forall₂ (Encodes gates) termTraps rootTraps)
    (claimEncoded : Encodes gates termClaim rootClaim)
    (pending : build rootTraps rootClaim = .pending clause) :
    Models assignment (databaseOfClauses (builderClauses gates clause)) ↔
      GateConsistent assignment gates ∧
        TermCounterexample assignment termTraps termClaim := by
  rw [pending_builderDatabase_iff assignment gates pending]
  constructor
  · rintro ⟨consistent, counterexample⟩
    exact ⟨consistent,
      (counterexample_iff trapsEncoded claimEncoded assignment consistent).mp counterexample⟩
  · rintro ⟨consistent, counterexample⟩
    exact ⟨consistent,
      (counterexample_iff trapsEncoded claimEncoded assignment consistent).mpr counterexample⟩

/-- An accepted supplied allocation trace constructs the gate-consistent
assignment needed by the bounded term/database theorem. -/
theorem checkedTrace_models_pending_iff {trace : List CNFBuilderTrace.AllocationEvent}
    {gates : List RawGate} (accepted : CNFBuilderTrace.check trace = some gates)
    (assignment : Assignment) {termTraps : List BoolTerm} {rootTraps : List Root}
    {termClaim : BoolTerm} {rootClaim : Root} {clause : Clause}
    (trapsEncoded : Forall₂ (Encodes gates) termTraps rootTraps)
    (claimEncoded : Encodes gates termClaim rootClaim)
    (pending : build rootTraps rootClaim = .pending clause) :
    Models (evalSequence gates assignment)
        (databaseOfClauses (builderClauses gates clause)) ↔
      TermCounterexample (evalSequence gates assignment) termTraps termClaim := by
  rw [pending_builderDatabase_terms_iff (evalSequence gates assignment) gates
    trapsEncoded claimEncoded pending]
  have consistent : GateConsistent (evalSequence gates assignment) gates :=
    evalSequence_gateConsistent (CNFBuilderTrace.check_wellFormed accepted) assignment
  constructor
  · exact fun modeled => modeled.2
  · exact fun counterexample => ⟨consistent, counterexample⟩

namespace ProductionExample

open Oak.TseitinCNF.SequenceExample

def term : BoolTerm :=
  .xorTerm (.complement (.input 1)) (.andTerm (.input 1) (.input 2))

def root : Root := .literal (output 4)

theorem term_encoded : Encodes gates term root := by
  have notEncoded : Encodes gates (.complement (.input 1))
      (.literal (negate (output 1))) := by
    exact Encodes.complement (Encodes.input 1 (by decide))
  have andEncoded : Encodes gates (.andTerm (.input 1) (.input 2))
      (.literal (output 3)) := by
    apply Encodes.andGate (Encodes.input 1 (by decide))
      (Encodes.input 2 (by decide))
    exact Or.inl (by simp [gates])
  unfold term root
  apply Encodes.xorGate notEncoded andEncoded
  exact Or.inl (by simp [gates, output, negate])

example (assignment : Assignment) (consistent : GateConsistent assignment gates) :
    root.eval assignment = term.eval assignment :=
  term_encoded.eval_eq assignment consistent

def trace : List CNFBuilderTrace.AllocationEvent :=
  [.input 0 1,
   .input 1 2,
   .gate ⟨0, 2, 4, 0, 3⟩,
   .gate ⟨2, 3, 6, 0, 4⟩]

theorem trace_accepted : CNFBuilderTrace.check trace = some gates := by
  rfl

example : build [] root = .pending [negate (output 4)] := by
  rfl

example (assignment : Assignment) :
    Models (evalSequence gates assignment)
        (databaseOfClauses
          (builderClauses gates [negate (output 4)])) ↔
      TermCounterexample (evalSequence gates assignment) [] term := by
  exact checkedTrace_models_pending_iff trace_accepted assignment
    Forall₂.nil term_encoded (by rfl)

end ProductionExample

end Oak.CNFTermRoot
