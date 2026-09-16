import Oak.CNFDenseAllocation

/-!
# Checked signed CNF clause snapshots

This module checks the concrete signed builder and emitted clause lists after
`Oak.CNFDenseAllocation` accepts their shared allocation snapshot. It preserves
the exact gate, clause, and literal order, including repeated or complementary
final-obligation edges, and applies the production 50,000,000 builder-clause
limit. Signed zero is not a literal. The signed representation is proved to
decode to the existing Tseitin clauses and hence the abstract RUP database.

This is a theorem about the supplied snapshot checker, with bounded production
correspondence tests. It does not prove the Go implementation or projection,
the provenance of the final obligation from source terms, DIMACS serialization,
LRAT checking, or authority to issue a native equivalence verdict. A model of
the complete emitted database still explicitly requires satisfaction of the
supplied final obligation.
-/

set_option autoImplicit false

namespace Oak.CNFClauseTrace

open Oak.RupCheck
open Oak.TseitinCNF
open Oak.CNFBuilderTrace

structure Snapshot where
  allocation : Oak.CNFDenseAllocation.Snapshot
  clauses : List (List Int)
  obligation : List Nat
  emitted : List (List Int)
  deriving Repr

structure Checked where
  gates : List RawGate
  obligation : Clause
  deriving Repr

/-- The nonzero signed DIMACS representation, before serialization to text. -/
def encodeLiteral (literal : Literal) : Int :=
  if literal.positive then (literal.index : Int) else -(literal.index : Int)

/-- Zero cannot be decoded as a literal of either polarity. -/
def decodeLiteral (signed : Int) : Option Literal :=
  if signed = 0 then none
  else some ⟨signed.natAbs, decide (0 < signed)⟩

def encodeClause (clause : Clause) : List Int := clause.map encodeLiteral

def encodeClauses (clauses : List Clause) : List (List Int) :=
  clauses.map encodeClause

def decodeClause : List Int → Option Clause
  | [] => some []
  | signed :: rest =>
      match decodeLiteral signed, decodeClause rest with
      | some literal, some literals => some (literal :: literals)
      | _, _ => none

def decodeClauses : List (List Int) → Option (List Clause)
  | [] => some []
  | clause :: rest =>
      match decodeClause clause, decodeClauses rest with
      | some literals, some clauses => some (literals :: clauses)
      | _, _ => none

def PositiveClause (clause : Clause) : Prop :=
  ∀ literal ∈ clause, 0 < literal.index

def PositiveClauses (clauses : List Clause) : Prop :=
  ∀ clause ∈ clauses, PositiveClause clause

theorem decode_encode_literal (literal : Literal)
    (positive : 0 < literal.index) :
    decodeLiteral (encodeLiteral literal) = some literal := by
  cases literal with
  | mk index polarity =>
      have nonzero : index ≠ 0 := Nat.ne_of_gt positive
      cases polarity <;>
        simp [decodeLiteral, encodeLiteral, nonzero, positive]

/-- The sign and variable index can both be recovered, so distinct valid
literals cannot collapse to the same signed integer. -/
theorem encodeLiteral_injective {left right : Literal}
    (leftPositive : 0 < left.index) (rightPositive : 0 < right.index)
    (same : encodeLiteral left = encodeLiteral right) : left = right := by
  have decoded := congrArg decodeLiteral same
  rw [decode_encode_literal left leftPositive,
    decode_encode_literal right rightPositive] at decoded
  exact Option.some.inj decoded

theorem decode_encode_clause {clause : Clause} (positive : PositiveClause clause) :
    decodeClause (encodeClause clause) = some clause := by
  induction clause with
  | nil => rfl
  | cons literal rest induction =>
      have headPositive := positive literal (by simp)
      have tailPositive : PositiveClause rest :=
        fun next member => positive next (by simp [member])
      have tailDecoded := induction tailPositive
      simp only [encodeClause] at tailDecoded
      simp [encodeClause, decodeClause, decode_encode_literal literal headPositive,
        tailDecoded]

theorem decode_encode_clauses {clauses : List Clause}
    (positive : PositiveClauses clauses) :
    decodeClauses (encodeClauses clauses) = some clauses := by
  induction clauses with
  | nil => rfl
  | cons clause rest induction =>
      have headPositive := positive clause (by simp)
      have tailPositive : PositiveClauses rest :=
        fun next member => positive next (by simp [member])
      have tailDecoded := induction tailPositive
      simp only [encodeClauses] at tailDecoded
      simp [encodeClauses, decodeClauses, decode_encode_clause headPositive,
        tailDecoded]

/-- A final edge must name an allocated variable; constants 0 and 1 reject.
Dense allocation acceptance establishes that each in-range variable is owned.
-/
def obligationLiteral? (variables edge : Nat) : Option Literal :=
  if 2 ≤ edge ∧ edge / 2 ≤ variables then
    some ⟨edge / 2, edge % 2 == 0⟩
  else none

def decodeObligation (variables : Nat) : List Nat → Option Clause
  | [] => some []
  | edge :: rest =>
      match obligationLiteral? variables edge, decodeObligation variables rest with
      | some literal, some literals => some (literal :: literals)
      | _, _ => none

def check (snapshot : Snapshot) : Option Checked :=
  match Oak.CNFDenseAllocation.check snapshot.allocation with
  | none => none
  | some gates =>
      if snapshot.clauses.length ≤ 50000000 ∧ snapshot.obligation ≠ [] then
        match decodeObligation snapshot.allocation.variables snapshot.obligation with
        | none => none
        | some obligation =>
            if snapshot.clauses = encodeClauses (gateClauses gates) ∧
                snapshot.emitted = encodeClauses (builderClauses gates obligation) then
              some ⟨gates, obligation⟩
            else none
      else none

structure Accepted (snapshot : Snapshot) (checked : Checked) : Prop where
  allocation : Oak.CNFDenseAllocation.check snapshot.allocation = some checked.gates
  budget : snapshot.clauses.length ≤ 50000000
  nonempty : snapshot.obligation ≠ []
  obligation : decodeObligation snapshot.allocation.variables snapshot.obligation =
    some checked.obligation
  builder : snapshot.clauses = encodeClauses (gateClauses checked.gates)
  emitted : snapshot.emitted =
    encodeClauses (builderClauses checked.gates checked.obligation)

theorem check_accepted {snapshot : Snapshot} {checked : Checked}
    (accepted : check snapshot = some checked) : Accepted snapshot checked := by
  unfold check at accepted
  cases allocation : Oak.CNFDenseAllocation.check snapshot.allocation with
  | none => simp [allocation] at accepted
  | some gates =>
      simp only [allocation] at accepted
      split at accepted
      · rename_i header
        cases obligation : decodeObligation snapshot.allocation.variables snapshot.obligation with
        | none => simp [obligation] at accepted
        | some literals =>
            simp only [obligation] at accepted
            split at accepted
            · rename_i exactClauses
              cases Option.some.inj accepted
              exact ⟨allocation, header.1, header.2, obligation,
                exactClauses.1, exactClauses.2⟩
            · contradiction
      · contradiction

theorem obligationLiteral_range {variables edge : Nat} {literal : Literal}
    (accepted : obligationLiteral? variables edge = some literal) :
    2 ≤ edge ∧ literal.index = edge / 2 ∧
      0 < literal.index ∧ literal.index ≤ variables := by
  unfold obligationLiteral? at accepted
  split at accepted
  · rename_i range
    cases Option.some.inj accepted
    exact ⟨range.1, rfl, by change 0 < edge / 2; omega, range.2⟩
  · contradiction

/-- The decoder retains exactly one literal per input edge in the original
order. Neither repeated literals nor opposite polarities are removed. -/
theorem decodeObligation_exact {variables : Nat} {edges : List Nat}
    {clause : Clause} (accepted : decodeObligation variables edges = some clause) :
    clause = edges.map (fun edge => (⟨edge / 2, edge % 2 == 0⟩ : Literal)) ∧
      ∀ edge ∈ edges, 2 ≤ edge ∧ edge / 2 ≤ variables := by
  induction edges generalizing clause with
  | nil =>
      simp [decodeObligation] at accepted
      subst clause
      simp
  | cons edge rest induction =>
      simp only [decodeObligation] at accepted
      cases headResult : obligationLiteral? variables edge with
      | none => simp [headResult] at accepted
      | some literal =>
          cases tailResult : decodeObligation variables rest with
          | none => simp [headResult, tailResult] at accepted
          | some literals =>
              simp [headResult, tailResult] at accepted
              subst clause
              have tailExact := induction tailResult
              unfold obligationLiteral? at headResult
              split at headResult
              · rename_i headRange
                cases Option.some.inj headResult
                constructor
                · simp [tailExact.1]
                · intro next member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact headRange
                  · exact tailExact.2 next member
              · contradiction

theorem check_obligation_exact {snapshot : Snapshot} {checked : Checked}
    (accepted : check snapshot = some checked) :
    checked.obligation = snapshot.obligation.map
      (fun edge => (⟨edge / 2, edge % 2 == 0⟩ : Literal)) ∧
      ∀ edge ∈ snapshot.obligation,
        2 ≤ edge ∧ edge / 2 ≤ snapshot.allocation.variables :=
  decodeObligation_exact (check_accepted accepted).obligation

theorem check_obligation_nonempty {snapshot : Snapshot} {checked : Checked}
    (accepted : check snapshot = some checked) : checked.obligation ≠ [] := by
  rw [(check_obligation_exact accepted).1]
  simpa using (check_accepted accepted).nonempty

theorem check_obligation_length {snapshot : Snapshot} {checked : Checked}
    (accepted : check snapshot = some checked) :
    checked.obligation.length = snapshot.obligation.length := by
  rw [(check_obligation_exact accepted).1, List.length_map]

theorem decodeObligation_positive {variables : Nat} {edges : List Nat}
    {clause : Clause} (accepted : decodeObligation variables edges = some clause) :
    PositiveClause clause := by
  induction edges generalizing clause with
  | nil =>
      simp [decodeObligation] at accepted
      subst clause
      simp [PositiveClause]
  | cons edge rest induction =>
      simp only [decodeObligation] at accepted
      cases headResult : obligationLiteral? variables edge with
      | none => simp [headResult] at accepted
      | some literal =>
          cases tailResult : decodeObligation variables rest with
          | none => simp [headResult, tailResult] at accepted
          | some literals =>
              simp [headResult, tailResult] at accepted
              subst clause
              intro next member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact (obligationLiteral_range headResult).2.2.1
              · exact induction tailResult next member

/-- All clauses of a valid raw gate use nonzero variables, including the
negated output literals and operands in the redundant ITE clauses. -/
theorem rawGate_positive {gate : RawGate}
    (outputPositive : 0 < gate.outputIndex)
    (operandPositive : ∀ literal ∈ gate.operands, 0 < literal.index) :
    PositiveClauses gate.clauses := by
  cases gate <;>
    simp_all [RawGate.outputIndex, RawGate.operands, RawGate.clauses,
      PositiveClauses, PositiveClause, andGateClauses, orGateClauses,
      xorGateClauses, iteGateClauses, negate, output]

theorem acceptedGates_positive {variables previous : Nat}
    {memo : List Oak.CNFDenseAllocation.MemoEntry}
    {records : List EncodedGate} {gates : List RawGate}
    (accepted : Oak.CNFDenseAllocation.GatesAcceptedFrom variables memo previous records gates) :
    PositiveClauses (gateClauses gates) := by
  induction accepted with
  | nil => simp [PositiveClauses, gateClauses]
  | cons decoded range ordered backward keyed found tail induction =>
      have outputPositive : 0 < _ := range.1
      have headPositive := rawGate_positive
        (by simpa [decodeGate_output decoded] using outputPositive)
        (fun literal member => (backward literal member).1)
      intro clause member
      simp only [gateClauses, List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · exact headPositive clause member
      · exact induction clause member

theorem check_builder_positive {snapshot : Snapshot} {checked : Checked}
    (accepted : check snapshot = some checked) :
    PositiveClauses (builderClauses checked.gates checked.obligation) := by
  have evidence := check_accepted accepted
  have gatesPositive := acceptedGates_positive
    (Oak.CNFDenseAllocation.check_accepted evidence.allocation).gateWalk
  have obligationPositive := decodeObligation_positive evidence.obligation
  intro clause member
  simp only [builderClauses, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact gatesPositive clause member
  · exact obligationPositive

/-- Decoding the actual signed emitted list recovers precisely the formal
gate clauses followed by the supplied obligation, not merely an equisatisfiable
set. This also rules out every occurrence of signed zero. -/
theorem check_decodes_emitted {snapshot : Snapshot} {checked : Checked}
    (accepted : check snapshot = some checked) :
    decodeClauses snapshot.emitted =
      some (builderClauses checked.gates checked.obligation) := by
  rw [(check_accepted accepted).emitted]
  exact decode_encode_clauses (check_builder_positive accepted)

theorem check_decodes_builder {snapshot : Snapshot} {checked : Checked}
    (accepted : check snapshot = some checked) :
    decodeClauses snapshot.clauses = some (gateClauses checked.gates) := by
  rw [(check_accepted accepted).builder]
  exact decode_encode_clauses (acceptedGates_positive
    (Oak.CNFDenseAllocation.check_accepted (check_accepted accepted).allocation).gateWalk)

/-- The partial database reader rejects any signed zero instead of giving it
an interpretation as a variable or a clause terminator. -/
def emittedDatabase? (snapshot : Snapshot) : Option Database :=
  (decodeClauses snapshot.emitted).map databaseOfClauses

theorem check_exact_database {snapshot : Snapshot} {checked : Checked}
    (accepted : check snapshot = some checked) :
    emittedDatabase? snapshot =
      some (databaseOfClauses (builderClauses checked.gates checked.obligation)) := by
  simp [emittedDatabase?, check_decodes_emitted accepted]

theorem check_models_iff {snapshot : Snapshot} {checked : Checked}
    {database : Database} (accepted : check snapshot = some checked)
    (decoded : emittedDatabase? snapshot = some database) (assignment : Assignment) :
    Models assignment database ↔
      GateConsistent assignment checked.gates ∧
      SatisfiesClause assignment checked.obligation := by
  rw [check_exact_database accepted] at decoded
  cases Option.some.inj decoded
  exact models_builderDatabase_iff assignment checked.gates checked.obligation

theorem check_wellFormed {snapshot : Snapshot} {checked : Checked}
    (accepted : check snapshot = some checked) : WellFormedSequence checked.gates :=
  Oak.CNFDenseAllocation.check_wellFormed (check_accepted accepted).allocation

/-- Allocation and the exact signed clauses compose with the existing
left-to-right gate evaluation. The final obligation remains an explicit
semantic premise; acceptance alone cannot make an arbitrary obligation true.
-/
theorem check_evalSequence_models_of_obligation {snapshot : Snapshot}
    {checked : Checked} {database : Database}
    (accepted : check snapshot = some checked)
    (decoded : emittedDatabase? snapshot = some database)
    (assignment : Assignment)
    (finalClause : SatisfiesClause (evalSequence checked.gates assignment) checked.obligation) :
    Models (evalSequence checked.gates assignment) database := by
  rw [check_exact_database accepted] at decoded
  cases Option.some.inj decoded
  exact evalSequence_models_builderDatabase_of_obligation
    (check_wellFormed accepted) assignment checked.obligation finalClause

end Oak.CNFClauseTrace
