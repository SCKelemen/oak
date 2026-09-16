import Oak.TseitinCNF

/-!
# Checked CNF builder allocation traces

This module checks a supplied, production-shaped projection of
`asm/cnf.go`'s shared input/gate allocation stream.  It decodes the Go edge
convention (`2*v` positive and `2*v+1` negative), pins the raw operation tags,
requires contiguous one-based allocation, and checks that raw-gate operands
refer strictly backwards.  An accepted trace therefore yields the
`Oak.TseitinCNF.WellFormedSequence` needed by the existing clause/database
model theorems.

This is not a refinement proof of `cnfBuilder`.  In particular, it does not
prove that Go emits the supplied trace, that the trace contains every call to
`fresh`, or that the Go input map, memo table, folds, and memo hits implement
this model.  It does not prove memo-key uniqueness, compare the actual
`cnfBuilder.clauses` slice with `gateClauses`, establish `exceeded = false` or
the clause-budget behavior, decode the final obligation edges, relate an
obligation to the lowered claim and traps, verify DIMACS serialization or
parsing, or discharge `cnf_complete`.  The final-database theorem below keeps
the obligation's satisfaction as an explicit premise.  Connecting a concrete
Go snapshot or event log to an accepted trace remains a separate
implementation-refinement obligation.
-/

set_option autoImplicit false

namespace Oak.CNFBuilderTrace

open Oak.RupCheck
open Oak.TseitinCNF

/-- The production fields of one entry in `cnfBuilder.gates`, represented as
natural numbers after a boundary check has rejected negative Go integers. -/
structure EncodedGate where
  op : Nat
  x : Nat
  y : Nat
  z : Nat
  out : Nat
  deriving Repr

/-- An allocation event in the shared DIMACS variable namespace.  Input
events carry the blaster variable key and its allocated DIMACS variable;
gate events carry the exact fields recorded by `cnfGate`. -/
inductive AllocationEvent where
  | input (source out : Nat)
  | gate (record : EncodedGate)
  deriving Repr

def AllocationEvent.output : AllocationEvent → Nat
  | .input _ out => out
  | .gate record => record.out

def inputSources : List AllocationEvent → List Nat
  | [] => []
  | .input source _ :: rest => source :: inputSources rest
  | .gate _ :: rest => inputSources rest

/-- Decode a nonconstant complement edge.  Edges zero and one are Boolean
constants and must have been folded before a raw gate is recorded. -/
def literalOfEdge? (edge : Nat) : Option Literal :=
  if edge < 2 then none
  else some ⟨edge / 2, edge % 2 == 0⟩

private structure DecodedGate (record : EncodedGate) where
  gate : RawGate
  output : gate.outputIndex = record.out

/-- Decode exactly the `cnfGate` operation tags while retaining the immediate
fact that every resulting raw gate uses the recorded output. -/
private def EncodedGate.decodeWithProof? (record : EncodedGate) :
    Option (DecodedGate record) :=
  match record.op with
  | 0 =>
      if record.z = 0 ∧ record.x ≤ record.y then
        match literalOfEdge? record.x, literalOfEdge? record.y with
        | some left, some right => some ⟨.andGate record.out left right, rfl⟩
        | _, _ => none
      else none
  | 1 =>
      if record.z = 0 ∧ record.x ≤ record.y then
        match literalOfEdge? record.x, literalOfEdge? record.y with
        | some left, some right => some ⟨.orGate record.out left right, rfl⟩
        | _, _ => none
      else none
  | 2 =>
      if record.z = 0 ∧ record.x ≤ record.y then
        match literalOfEdge? record.x, literalOfEdge? record.y with
        | some left, some right => some ⟨.xorGate record.out left right, rfl⟩
        | _, _ => none
      else none
  | 3 =>
      match literalOfEdge? record.x, literalOfEdge? record.y,
          literalOfEdge? record.z with
      | some condition, some thenValue, some elseValue =>
          some ⟨.iteGate record.out condition thenValue elseValue, rfl⟩
      | _, _, _ => none
  | _ => none

/-- Decode a production gate record to the existing logical gate type. -/
def EncodedGate.decode? (record : EncodedGate) : Option RawGate :=
  record.decodeWithProof?.map DecodedGate.gate

theorem decodeGate_output {record : EncodedGate} {gate : RawGate}
    (decoded : record.decode? = some gate) :
    gate.outputIndex = record.out := by
  unfold EncodedGate.decode? at decoded
  cases decodedWithProof : record.decodeWithProof? with
  | none => simp [decodedWithProof] at decoded
  | some result =>
      simp [decodedWithProof] at decoded
      subst gate
      exact result.output

/-- Public binary decoding characterization.  Clients can recover both
operand decodings and the exact raw constructor without depending on the
private proof-carrying decoder representation. -/
theorem decodeGate_binary {record : EncodedGate} {gate : RawGate}
    (admitted : record.op < 3) (decoded : record.decode? = some gate) :
    ∃ left right, literalOfEdge? record.x = some left ∧
      literalOfEdge? record.y = some right ∧
      gate = match record.op with
        | 0 => .andGate record.out left right
        | 1 => .orGate record.out left right
        | _ => .xorGate record.out left right := by
  have operations : record.op = 0 ∨ record.op = 1 ∨ record.op = 2 := by omega
  rcases operations with operation | operation | operation
  all_goals
    unfold EncodedGate.decode? at decoded
    simp only [EncodedGate.decodeWithProof?, operation] at decoded
    split at decoded
    · cases leftDecoded : literalOfEdge? record.x with
      | none => simp [leftDecoded] at decoded
      | some left =>
          cases rightDecoded : literalOfEdge? record.y with
          | none => simp [leftDecoded, rightDecoded] at decoded
          | some right =>
              refine ⟨left, right, rfl, rfl, ?_⟩
              simpa [leftDecoded, rightDecoded, operation] using decoded.symm
    · simp at decoded

/-- Every raw operand has a nonzero DIMACS index below the next allocation ID. -/
def OperandsBefore (next : Nat) (gate : RawGate) : Prop :=
  ∀ operand ∈ gate.operands, 0 < operand.index ∧ operand.index < next

def operandsBefore (next : Nat) (gate : RawGate) : Bool :=
  gate.operands.all fun operand =>
    decide (0 < operand.index ∧ operand.index < next)

theorem operandsBefore_eq_true_iff (next : Nat) (gate : RawGate) :
    operandsBefore next gate = true ↔ OperandsBefore next gate := by
  simp [operandsBefore, OperandsBefore]

/-- The relational reading of the executable checker. -/
inductive AcceptedFrom : Nat → List AllocationEvent → List RawGate → Prop where
  | nil (next : Nat) : AcceptedFrom next [] []
  | input {next source out : Nat} {rest : List AllocationEvent}
      {gates : List RawGate}
      (output : out = next)
      (tail : AcceptedFrom (next + 1) rest gates) :
      AcceptedFrom next (.input source out :: rest) gates
  | gate {next : Nat} {record : EncodedGate} {rest : List AllocationEvent}
      {gate : RawGate} {gates : List RawGate}
      (decoded : record.decode? = some gate)
      (output : gate.outputIndex = next)
      (operands : OperandsBefore next gate)
      (tail : AcceptedFrom (next + 1) rest gates) :
      AcceptedFrom next (.gate record :: rest) (gate :: gates)

/-- Replay the supplied allocation projection. -/
def checkFrom : Nat → List AllocationEvent → Option (List RawGate)
  | _, [] => some []
  | next, .input _ out :: rest =>
      if out = next then checkFrom (next + 1) rest else none
  | next, .gate record :: rest =>
      match record.decode? with
      | none => none
      | some gate =>
          if gate.outputIndex = next then
            if operandsBefore next gate then
              match checkFrom (next + 1) rest with
              | none => none
              | some gates => some (gate :: gates)
            else none
          else none

/-- Public checking also rejects allocating the same blaster input key twice. -/
def check (trace : List AllocationEvent) : Option (List RawGate) :=
  if (inputSources trace).Nodup then checkFrom 1 trace else none

theorem checkFrom_accepted {next : Nat} {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : checkFrom next trace = some gates) :
    AcceptedFrom next trace gates := by
  induction trace generalizing next gates with
  | nil =>
      simp [checkFrom] at accepted
      subst gates
      exact .nil next
  | cons event rest ih =>
      cases event with
      | input source out =>
          simp only [checkFrom] at accepted
          split at accepted
          · exact .input (by assumption) (ih accepted)
          · contradiction
      | gate record =>
          simp only [checkFrom] at accepted
          cases decoded : record.decode? with
          | none => simp [decoded] at accepted
          | some gate =>
              simp only [decoded] at accepted
              split at accepted
              · split at accepted
                · cases tailResult : checkFrom (next + 1) rest with
                  | none => simp [tailResult] at accepted
                  | some tailGates =>
                      simp [tailResult] at accepted
                      subst gates
                      exact .gate decoded (by assumption)
                        (operandsBefore_eq_true_iff next gate |>.mp (by assumption))
                        (ih tailResult)
                · contradiction
              · contradiction

theorem AcceptedFrom.outputs {next : Nat} {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : AcceptedFrom next trace gates) :
    trace.map AllocationEvent.output = List.range' next trace.length := by
  induction accepted with
  | nil => rfl
  | @input next source out rest gates output tail ih =>
      simp [AllocationEvent.output, output, List.range'_succ, ih]
  | @gate next record rest gate gates decoded output operands tail ih =>
      have encodedOutput : record.out = next := by
        rw [← decodeGate_output decoded, output]
      simp [AllocationEvent.output, encodedOutput, List.range'_succ, ih]

theorem checkFrom_outputs {next : Nat} {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : checkFrom next trace = some gates) :
    trace.map AllocationEvent.output = List.range' next trace.length :=
  (checkFrom_accepted accepted).outputs

theorem AcceptedFrom.wellFormed {next : Nat} {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : AcceptedFrom next trace gates)
    {bound : Nat} (before : bound < next) :
    WellFormedFrom bound gates := by
  induction accepted generalizing bound with
  | nil => exact .nil bound
  | @input next source out rest gates output tail ih =>
      exact ih (Nat.lt_trans before (Nat.lt_succ_self next))
  | @gate next record rest gate gates decoded output operands tail ih =>
      refine .cons ?_ ?_ ?_
      · simpa [output] using before
      · intro operand member
        have earlier := (operands operand member).2
        simpa [output] using earlier
      · apply ih
        rw [output]
        exact Nat.lt_succ_self next

theorem checkFrom_wellFormed {next : Nat} {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : checkFrom next trace = some gates)
    {bound : Nat} (before : bound < next) :
    WellFormedFrom bound gates :=
  (checkFrom_accepted accepted).wellFormed before

theorem check_inputSources_nodup {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : check trace = some gates) :
    (inputSources trace).Nodup := by
  unfold check at accepted
  split at accepted
  · assumption
  · contradiction

theorem check_from {trace : List AllocationEvent} {gates : List RawGate}
    (accepted : check trace = some gates) :
    checkFrom 1 trace = some gates := by
  unfold check at accepted
  split at accepted
  · exact accepted
  · contradiction

theorem check_outputs_nodup {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : check trace = some gates) :
    (trace.map AllocationEvent.output).Nodup := by
  rw [checkFrom_outputs (check_from accepted)]
  exact List.nodup_range'

theorem check_wellFormed {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : check trace = some gates) :
    WellFormedSequence gates := by
  unfold WellFormedSequence
  exact checkFrom_wellFormed (check_from accepted) (by decide)

theorem check_models_gateDatabase {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : check trace = some gates)
    (assignment : Assignment) :
    Models (evalSequence gates assignment)
      (databaseOfClauses (gateClauses gates)) :=
  evalSequence_models_gateDatabase (check_wellFormed accepted) assignment

theorem check_models_builderDatabase_of_obligation {trace : List AllocationEvent}
    {gates : List RawGate} (accepted : check trace = some gates)
    (assignment : Assignment) (obligation : Clause)
    (finalClause : SatisfiesClause (evalSequence gates assignment) obligation) :
    Models (evalSequence gates assignment)
      (databaseOfClauses (builderClauses gates obligation)) :=
  evalSequence_models_builderDatabase_of_obligation
    (check_wellFormed accepted) assignment obligation finalClause

namespace ProductionExample

example : literalOfEdge? 2 = some ⟨1, true⟩ := by
  rfl

example : literalOfEdge? 3 = some ⟨1, false⟩ := by
  rfl

def trace : List AllocationEvent :=
  [.input 0 1,
   .input 1 2,
   .gate ⟨0, 2, 4, 0, 3⟩,
   .gate ⟨2, 3, 6, 0, 4⟩]

example : check trace = some Oak.TseitinCNF.SequenceExample.gates := by
  rfl

/-- Pin the remaining production operation tags and ITE operand order. -/
example : EncodedGate.decode? ⟨1, 2, 4, 0, 3⟩ =
    some (.orGate 3 ⟨1, true⟩ ⟨2, true⟩) := by
  rfl

example : EncodedGate.decode? ⟨3, 2, 4, 7, 4⟩ =
    some (.iteGate 4 ⟨1, true⟩ ⟨2, true⟩ ⟨3, false⟩) := by
  rfl

example : check
    [.input 0 1, .input 1 2, .gate ⟨0, 2, 4, 0, 4⟩] = none := by
  rfl

example : check [.input 0 1, .input 1 1] = none := by
  rfl

example : check
    [.input 0 1, .input 1 2, .gate ⟨0, 2, 6, 0, 3⟩] = none := by
  rfl

example : check
    [.input 0 1, .input 1 2, .gate ⟨0, 0, 4, 0, 3⟩] = none := by
  rfl

example : check
    [.input 0 1, .input 1 2, .gate ⟨0, 4, 2, 0, 3⟩] = none := by
  rfl

example : check [.input 0 1, .input 0 2] = none := by
  rfl

example : check
    [.input 0 1, .input 1 2, .gate ⟨4, 2, 4, 0, 3⟩] = none := by
  rfl

example : check
    [.input 0 1, .input 1 2, .gate ⟨0, 2, 4, 7, 3⟩] = none := by
  rfl

end ProductionExample

end Oak.CNFBuilderTrace
