import Oak.CNFDenseAllocation
import Oak.CNFReplayApply

/-!
# Input stability and bounded Boolean replay

Inputs in an accepted shared allocation cannot be overwritten by gate
evaluation, including when input allocation is interleaved with gates.
The executable Boolean-expression replay admits constants, designated input
slots and pointwise AND/OR/XOR, including constant/identity/complement folds
and memo hits. It preserves expression evaluation at the original inputs.

This is a supplied-snapshot model, not a refinement of Go source bindings,
word-width adaptation, term-pointer memoization or complete reachable-term
coverage. The result-pair list explicitly supplies the corresponding bit
expressions. Its empty difference is the mathematical false identity; unlike
the native audit, this model does not impose a nonempty 1..64-bit profile.
-/

set_option autoImplicit false

namespace Oak.CNFReplayTerm

open Oak.RupCheck Oak.TseitinCNF Oak.CNFBuilderTrace
open Oak.CNFDenseAllocation
open Oak.CNFReplayApply

theorem gate_output_recorded {variables previous : Nat} {memo : List MemoEntry}
    {records : List EncodedGate} {gates : List RawGate}
    (walk : GatesAcceptedFrom variables memo previous records gates)
    {gate : RawGate} (member : gate ∈ gates) :
    gate.outputIndex ∈ records.map EncodedGate.out := by
  induction walk with
  | nil => contradiction
  | cons decoded range ordered backward keyed found tail induction =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [decodeGate_output decoded]
      · exact List.mem_cons_of_mem _ (induction member)

theorem evalSequence_at_unwritten (gates : List RawGate) (assignment : Assignment)
    (index : Nat) (unwritten : ∀ gate ∈ gates, index ≠ gate.outputIndex) :
    evalSequence gates assignment index = assignment index := by
  induction gates generalizing assignment with
  | nil => rfl
  | cons gate rest induction =>
      rw [evalSequence, induction (assignOutput assignment gate)
        (fun next member => unwritten next (List.mem_cons_of_mem _ member))]
      exact assignOutput_at_other assignment gate index (unwritten gate (by simp))

theorem check_input_stable {snapshot : Snapshot} {gates : List RawGate}
    (accepted : check snapshot = some gates) (assignment : Assignment)
    {index : Nat} (input : index ∈ inputOutputs snapshot) :
    evalSequence gates assignment index = assignment index := by
  apply evalSequence_at_unwritten
  intro gate member equal
  have gateMember := gate_output_recorded (check_accepted accepted).gateWalk member
  have unique := (check_accepted accepted).shape.outputUnique
  have disjoint := (List.pairwise_append.mp unique).2.2
  exact disjoint index input gate.outputIndex gateMember equal

/-! ## Executable Boolean-expression replay over designated inputs -/

inductive Term where
  | constant (value : Bool)
  | input (index : Nat)
  | binary (op : Nat) (left right : Term)
  deriving Repr

def Term.eval (assignment : Assignment) : Term → Bool
  | .constant value => value
  | .input index => assignment index
  | .binary op left right => binaryValue op (left.eval assignment) (right.eval assignment)

/-- Inputs must designate actual allocated input slots, never gate outputs.
The max-int guard models the separate nonnegative edge-construction bound.
Binary replay includes all of the checked fold and exact-memo cases. -/
def replayTerm (snapshot : Snapshot) (maxInt : Nat) : Term → Option Nat
  | .constant value => some (if value then 1 else 0)
  | .input index =>
      if 0 < index ∧ index ∈ inputOutputs snapshot ∧ index ≤ maxInt / 2 then
        some (2 * index)
      else none
  | .binary op left right =>
      match replayTerm snapshot maxInt left, replayTerm snapshot maxInt right with
      | some x, some y => replayApply snapshot.variables maxInt snapshot.memo op x y
      | _, _ => none

/-- Replay reads designated source bits from the initial assignment. Gate
evaluation may change internal outputs but must preserve these input slots.
`MemoSound` is a local premise, discharged from accepted allocation and gate
consistency by the composition module. -/
theorem replayTerm_sound {snapshot : Snapshot} {maxInt : Nat}
    {assignment initial : Assignment} (sound : MemoSound assignment snapshot.memo)
    (stable : ∀ index ∈ inputOutputs snapshot, assignment index = initial index)
    {term : Term} {edge : Nat}
    (replayed : replayTerm snapshot maxInt term = some edge) :
    evalEdge assignment edge = term.eval initial := by
  induction term generalizing edge with
  | constant value =>
      cases value <;> simp only [replayTerm] at replayed <;>
        cases Option.some.inj replayed <;> rfl
  | input index =>
      unfold replayTerm at replayed
      split at replayed
      · rename_i conditions
        cases Option.some.inj replayed
        rw [evalEdge_positive assignment index conditions.1]
        exact stable index conditions.2.1
      · contradiction
  | binary op left right leftIH rightIH =>
      simp only [replayTerm] at replayed
      cases leftRoot : replayTerm snapshot maxInt left with
      | none => simp [leftRoot] at replayed
      | some x =>
          cases rightRoot : replayTerm snapshot maxInt right with
          | none => simp [leftRoot, rightRoot] at replayed
          | some y =>
              simp only [leftRoot, rightRoot] at replayed
              rw [replayApply_sound sound replayed, leftIH leftRoot, rightIH rightRoot]
              rfl

/-- Build the same low-to-high OR-of-XOR shape as the native word audit.
The pairs explicitly supply corresponding result bits; no source-to-bit
projection is inferred here. -/
def differenceFrom (prior : Term) : List (Term × Term) → Term
  | [] => prior
  | (left, right) :: rest =>
      differenceFrom (.binary 1 prior (.binary 2 left right)) rest

def differenceTerm (pairs : List (Term × Term)) : Term :=
  differenceFrom (.constant false) pairs

private theorem or_xor_eq_false_iff (prior left right : Bool) :
    (prior || xor left right) = false ↔ prior = false ∧ left = right := by
  cases prior <;> cases left <;> cases right <;> decide

theorem differenceFrom_false_iff (assignment : Assignment) (pairs : List (Term × Term))
    (prior : Term) :
    (differenceFrom prior pairs).eval assignment = false ↔
      prior.eval assignment = false ∧
        ∀ pair ∈ pairs, pair.1.eval assignment = pair.2.eval assignment := by
  induction pairs generalizing prior with
  | nil => simp [differenceFrom]
  | cons pair rest induction =>
      rw [differenceFrom, induction]
      simp only [Term.eval, binaryValue, or_xor_eq_false_iff]
      simp [List.mem_cons, and_assoc]

theorem differenceTerm_false_iff (assignment : Assignment) (pairs : List (Term × Term)) :
    (differenceTerm pairs).eval assignment = false ↔
      ∀ pair ∈ pairs, pair.1.eval assignment = pair.2.eval assignment := by
  simp [differenceTerm, differenceFrom_false_iff, Term.eval]

end Oak.CNFReplayTerm
