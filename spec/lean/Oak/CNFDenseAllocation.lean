import Oak.CNFBuilderTrace

/-!
# Dense CNF allocation snapshot checking

This module models the nonnegative snapshot consumed by
`asm.validateCNFAllocation`: inputs and gates share one dense DIMACS variable
namespace, gates are output-ordered and backward-referencing, and every gate
has the exact entry in the builder's unique table.  Go maps are projected as
lists with explicit key-uniqueness requirements.

The Go correspondence test renders production snapshots into `check`
examples and asks Lean's kernel to evaluate them.  This is a bounded
implementation-correspondence slice, not a proof that arbitrary Go memory is
projected faithfully, that signed integers were converted to naturals
correctly, or that clause emission, the final obligation, DIMACS, solving, or
LRAT checking is correct.
-/

set_option autoImplicit false

namespace Oak.CNFDenseAllocation

open Oak.CNFBuilderTrace
open Oak.RupCheck
open Oak.TseitinCNF

structure InputAllocation where
  source : Nat
  output : Nat
  deriving Repr, DecidableEq

/-- The Go memo key after its signed `z = -1` binary sentinel has been decoded
into a constructor distinct from the three-edge ITE key. -/
inductive MemoKey where
  | binary (op x y : Nat)
  | ite (condition thenValue elseValue : Nat)
  deriving Repr, DecidableEq

structure MemoEntry where
  key : MemoKey
  output : Nat
  deriving Repr, DecidableEq

structure Snapshot where
  variables : Nat
  exceeded : Bool
  inputs : List InputAllocation
  gates : List EncodedGate
  memo : List MemoEntry
  deriving Repr

def lookupMemo? : List MemoEntry → MemoKey → Option Nat
  | [], _ => none
  | entry :: rest, key =>
      if entry.key = key then some entry.output else lookupMemo? rest key

def inputSources (snapshot : Snapshot) : List Nat :=
  snapshot.inputs.map InputAllocation.source

def inputOutputs (snapshot : Snapshot) : List Nat :=
  snapshot.inputs.map InputAllocation.output

def gateOutputs (snapshot : Snapshot) : List Nat :=
  snapshot.gates.map EncodedGate.out

def outputs (snapshot : Snapshot) : List Nat :=
  inputOutputs snapshot ++ gateOutputs snapshot

def memoKeys (snapshot : Snapshot) : List MemoKey :=
  snapshot.memo.map MemoEntry.key

/-- Complement edges name one variable with opposite polarities. -/
def complementaryEdges (left right : Nat) : Bool :=
  left / 2 == right / 2 && left % 2 != right % 2

/-- The exact non-folded unique-table key shape.  Raw operation tags,
constant operands, operand ordering and decoding are checked separately by
`EncodedGate.decode?`; this function rejects the remaining production folds.
-/
def memoKey? (record : EncodedGate) : Option MemoKey :=
  match record.op with
  | 0 | 1 | 2 =>
      if record.x = record.y ∨ complementaryEdges record.x record.y = true then
        none
      else
        some (.binary record.op record.x record.y)
  | 3 =>
      if record.y = record.z then none
      else some (.ite record.x record.y record.z)
  | _ => none

/-- Relational reading of the stable gate/memo walk. -/
inductive GatesAcceptedFrom (variables : Nat) (memo : List MemoEntry) :
    Nat → List EncodedGate → List RawGate → Prop where
  | nil (previous : Nat) : GatesAcceptedFrom variables memo previous [] []
  | cons {previous : Nat} {record : EncodedGate} {rest : List EncodedGate}
      {gate : RawGate} {gates : List RawGate} {key : MemoKey}
      (decoded : record.decode? = some gate)
      (range : 0 < record.out ∧ record.out ≤ variables)
      (ordered : previous < record.out)
      (backward : OperandsBefore record.out gate)
      (keyed : memoKey? record = some key)
      (found : lookupMemo? memo key = some record.out)
      (tail : GatesAcceptedFrom variables memo record.out rest gates) :
      GatesAcceptedFrom variables memo previous (record :: rest) (gate :: gates)

/-- Replay exactly the gate-order, backward-edge and memo-lookup decisions. -/
def checkGatesFrom (variables : Nat) (memo : List MemoEntry) :
    Nat → List EncodedGate → Option (List RawGate)
  | _, [] => some []
  | previous, record :: rest =>
      match record.decode?, memoKey? record with
      | some gate, some key =>
          if decide (0 < record.out ∧ record.out ≤ variables) &&
              decide (previous < record.out) && operandsBefore record.out gate &&
              decide (lookupMemo? memo key = some record.out) then
            match checkGatesFrom variables memo record.out rest with
            | some gates => some (gate :: gates)
            | none => none
          else none
      | _, _ => none

theorem checkGatesFrom_accepted {variables previous : Nat}
    {memo : List MemoEntry} {records : List EncodedGate} {gates : List RawGate}
    (accepted : checkGatesFrom variables memo previous records = some gates) :
    GatesAcceptedFrom variables memo previous records gates := by
  induction records generalizing previous gates with
  | nil =>
      simp [checkGatesFrom] at accepted
      subst gates
      exact .nil previous
  | cons record rest induction =>
      simp only [checkGatesFrom] at accepted
      cases decoded : record.decode? with
      | none => simp [decoded] at accepted
      | some gate =>
          cases keyed : memoKey? record with
          | none => simp [decoded, keyed] at accepted
          | some key =>
              simp only [decoded, keyed] at accepted
              cases condition :
                  (decide (0 < record.out ∧ record.out ≤ variables) &&
                    decide (previous < record.out) &&
                    operandsBefore record.out gate &&
                    decide (lookupMemo? memo key = some record.out)) with
              | false => simp_all [Bool.and_eq_true]
              | true =>
                  simp only [condition, if_true] at accepted
                  cases tailResult : checkGatesFrom variables memo record.out rest with
                  | none => simp [tailResult] at accepted
                  | some tailGates =>
                      simp [tailResult] at accepted
                      subst gates
                      have conditions :
                          ((decide (0 < record.out ∧ record.out ≤ variables) = true ∧
                          decide (previous < record.out) = true) ∧
                          operandsBefore record.out gate = true) ∧
                          decide (lookupMemo? memo key = some record.out) = true := by
                        simpa only [Bool.and_eq_true] using condition
                      exact .cons decoded
                        (of_decide_eq_true conditions.1.1.1)
                        (of_decide_eq_true conditions.1.1.2)
                        ((operandsBefore_eq_true_iff record.out gate).mp conditions.1.2)
                        keyed (of_decide_eq_true conditions.2)
                        (induction tailResult)

def inputsInRange (snapshot : Snapshot) : Bool :=
  snapshot.inputs.all fun input =>
    decide (0 < input.output ∧ input.output ≤ snapshot.variables)

def denseCoverage (snapshot : Snapshot) : Bool :=
  (List.range snapshot.variables).all fun index =>
    decide (index + 1 ∈ outputs snapshot)

/-- Header/count/range/allocation conditions outside the stable gate walk. -/
structure Shape (snapshot : Snapshot) : Prop where
  notExceeded : snapshot.exceeded = false
  sourceKeysUnique : (inputSources snapshot).Nodup
  memoKeysUnique : (memoKeys snapshot).Nodup
  memoCount : snapshot.memo.length = snapshot.gates.length
  inputCount : snapshot.inputs.length ≤ snapshot.variables
  allocationCount :
    snapshot.gates.length = snapshot.variables - snapshot.inputs.length
  inputRange : inputsInRange snapshot = true
  outputUnique : (outputs snapshot).Nodup
  dense : denseCoverage snapshot = true

def shapeCheck (snapshot : Snapshot) : Bool :=
  decide (snapshot.exceeded = false) &&
  decide (inputSources snapshot).Nodup &&
  decide (memoKeys snapshot).Nodup &&
  decide (snapshot.memo.length = snapshot.gates.length) &&
  decide (snapshot.inputs.length ≤ snapshot.variables) &&
  decide (snapshot.gates.length = snapshot.variables - snapshot.inputs.length) &&
  inputsInRange snapshot &&
  decide (outputs snapshot).Nodup &&
  denseCoverage snapshot

theorem shapeCheck_sound {snapshot : Snapshot}
    (accepted : shapeCheck snapshot = true) : Shape snapshot := by
  simp only [shapeCheck, Bool.and_eq_true] at accepted
  rcases accepted with
    ⟨⟨⟨⟨⟨⟨⟨⟨notExceeded, sourceUnique⟩, memoUnique⟩, memoCount⟩,
      inputCount⟩, allocationCount⟩, inputRange⟩, outputUnique⟩, dense⟩
  exact ⟨of_decide_eq_true notExceeded,
    of_decide_eq_true sourceUnique,
    of_decide_eq_true memoUnique,
    of_decide_eq_true memoCount,
    of_decide_eq_true inputCount,
    of_decide_eq_true allocationCount,
    inputRange,
    of_decide_eq_true outputUnique,
    dense⟩

/-- The complete executable snapshot checker. -/
def check (snapshot : Snapshot) : Option (List RawGate) :=
  if shapeCheck snapshot then
    checkGatesFrom snapshot.variables snapshot.memo 0 snapshot.gates
  else
    none

structure Accepted (snapshot : Snapshot) (gates : List RawGate) : Prop where
  shape : Shape snapshot
  gateWalk : GatesAcceptedFrom snapshot.variables snapshot.memo 0 snapshot.gates gates

theorem check_accepted {snapshot : Snapshot} {gates : List RawGate}
    (accepted : check snapshot = some gates) : Accepted snapshot gates := by
  unfold check at accepted
  split at accepted
  · exact ⟨shapeCheck_sound (by assumption), checkGatesFrom_accepted accepted⟩
  · contradiction

theorem GatesAcceptedFrom.wellFormed {variables previous : Nat}
    {memo : List MemoEntry} {records : List EncodedGate} {gates : List RawGate}
    (accepted : GatesAcceptedFrom variables memo previous records gates) :
    WellFormedFrom previous gates := by
  induction accepted with
  | nil => exact .nil _
  | @cons previous record rest gate gates key decoded range ordered backward keyed found tail induction =>
      refine .cons ?_ ?_ ?_
      · simpa [decodeGate_output decoded] using ordered
      · intro operand member
        simpa [decodeGate_output decoded] using (backward operand member).2
      · simpa [decodeGate_output decoded] using induction

/-- Accepted concrete allocation snapshots provide the acyclic gate sequence
consumed by the existing Tseitin evaluation theorems. -/
theorem check_wellFormed {snapshot : Snapshot} {gates : List RawGate}
    (accepted : check snapshot = some gates) : WellFormedSequence gates :=
  (check_accepted accepted).gateWalk.wellFormed

/-- The existing Tseitin theorem can consume the decoded sequence directly. -/
theorem check_models_gateDatabase {snapshot : Snapshot} {gates : List RawGate}
    (accepted : check snapshot = some gates) (assignment : Assignment) :
    Models (evalSequence gates assignment)
      (databaseOfClauses (gateClauses gates)) :=
  evalSequence_models_gateDatabase (check_wellFormed accepted) assignment

theorem GatesAcceptedFrom.gate_output_range {variables previous : Nat}
    {memo : List MemoEntry} {records : List EncodedGate} {gates : List RawGate}
    (accepted : GatesAcceptedFrom variables memo previous records gates)
    {record : EncodedGate} (member : record ∈ records) :
    0 < record.out ∧ record.out ≤ variables := by
  induction accepted with
  | nil => contradiction
  | cons decoded range ordered backward keyed found tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact range
      · exact induction member

theorem check_output_range {snapshot : Snapshot} {gates : List RawGate}
    (accepted : check snapshot = some gates) {output : Nat}
    (member : output ∈ outputs snapshot) :
    0 < output ∧ output ≤ snapshot.variables := by
  have checked := check_accepted accepted
  rcases List.mem_append.mp member with inputMember | gateMember
  · rcases List.mem_map.mp inputMember with ⟨input, inputIn, rfl⟩
    have ranges : snapshot.inputs.all (fun input =>
        decide (0 < input.output ∧ input.output ≤ snapshot.variables)) = true :=
      checked.shape.inputRange
    exact of_decide_eq_true ((List.all_eq_true.mp ranges) input inputIn)
  · rcases List.mem_map.mp gateMember with ⟨record, recordIn, rfl⟩
    exact checked.gateWalk.gate_output_range recordIn

/-- Every in-range DIMACS variable has exactly one input-or-gate owner. -/
theorem check_exactly_one_owner {snapshot : Snapshot} {gates : List RawGate}
    (accepted : check snapshot = some gates) (output : Nat)
    (positive : 0 < output) (bounded : output ≤ snapshot.variables) :
    (outputs snapshot).count output = 1 := by
  have checked := check_accepted accepted
  have member : output ∈ outputs snapshot := by
    have indexMember : output - 1 ∈ List.range snapshot.variables :=
      List.mem_range.mpr (by omega)
    have covered := (List.all_eq_true.mp checked.shape.dense)
      (output - 1) indexMember
    have decoded := of_decide_eq_true covered
    simpa [Nat.sub_add_cancel positive] using decoded
  simpa [member] using
    (checked.shape.outputUnique.count (a := output))

theorem GatesAcceptedFrom.gate_has_exact_memo {variables previous : Nat}
    {memo : List MemoEntry} {records : List EncodedGate} {gates : List RawGate}
    (accepted : GatesAcceptedFrom variables memo previous records gates)
    {record : EncodedGate} (member : record ∈ records) :
    ∃ gate key, record.decode? = some gate ∧
      OperandsBefore record.out gate ∧ memoKey? record = some key ∧
      lookupMemo? memo key = some record.out := by
  induction accepted with
  | nil => contradiction
  | cons decoded range ordered backward keyed found tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, _, decoded, backward, keyed, found⟩
      · exact induction member

/-- Every accepted gate carries its decoded backward operands and exact memo
witness; unique memo keys and equal gate/memo counts come from the shape. -/
theorem check_gate_has_exact_memo {snapshot : Snapshot} {gates : List RawGate}
    (accepted : check snapshot = some gates) {record : EncodedGate}
    (member : record ∈ snapshot.gates) :
    ∃ gate key, record.decode? = some gate ∧
      OperandsBefore record.out gate ∧ memoKey? record = some key ∧
      lookupMemo? snapshot.memo key = some record.out := by
  exact (check_accepted accepted).gateWalk.gate_has_exact_memo member

theorem check_memo_keys_unique {snapshot : Snapshot} {gates : List RawGate}
    (accepted : check snapshot = some gates) :
    (memoKeys snapshot).Nodup ∧ snapshot.memo.length = snapshot.gates.length :=
  ⟨(check_accepted accepted).shape.memoKeysUnique,
   (check_accepted accepted).shape.memoCount⟩

namespace Examples

def valid : Snapshot :=
  ⟨4, false,
   [⟨0, 1⟩, ⟨1, 2⟩],
   [⟨0, 2, 4, 0, 3⟩, ⟨2, 3, 6, 0, 4⟩],
   [⟨.binary 0 2 4, 3⟩, ⟨.binary 2 3 6, 4⟩]⟩

example : (check valid).isSome = true := by decide

example : (check { valid with inputs := [⟨0, 1⟩, ⟨1, 1⟩] }).isSome = false := by decide

example : (check { valid with variables := 5 }).isSome = false := by decide

example : (check { valid with gates := [⟨0, 2, 6, 0, 3⟩, ⟨2, 3, 6, 0, 4⟩]}).isSome = false := by decide

end Examples

end Oak.CNFDenseAllocation
