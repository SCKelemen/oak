import Oak.CNFClauseTrace
import Init.Data.List.Sort.Lemmas

/-!
# Compositional witnesses for the existing CNF snapshot checkers

These lemmas construct the existing allocation and clause-trace acceptance
relations and recover the exact existing executable checker equalities.
They permit bounded local witnesses to be joined without evaluating a whole
snapshot. They neither change a checker nor assume a supplied snapshot passes.
-/

set_option autoImplicit false

universe u v

namespace Oak.CNFCheckComposition

open Oak.CNFBuilderTrace
open Oak.CNFDenseAllocation
open Oak.RupCheck
open Oak.TseitinCNF

theorem shapeCheck_complete
    {snapshot : Oak.CNFDenseAllocation.Snapshot}
    (accepted : Shape snapshot) :
    shapeCheck snapshot = true := by
  simp [shapeCheck, accepted.notExceeded, accepted.sourceKeysUnique,
    accepted.memoKeysUnique, accepted.memoCount, accepted.inputCount,
    accepted.allocationCount, accepted.inputRange, accepted.outputUnique,
    accepted.dense]

theorem gateWalk_complete
    {variables previous : Nat} {memo : List MemoEntry}
    {records : List EncodedGate} {gates : List RawGate}
    (accepted : GatesAcceptedFrom variables memo previous records gates) :
    checkGatesFrom variables memo previous records = some gates := by
  induction accepted with
  | nil => rfl
  | @cons previous record rest gate gates key decoded range ordered backward keyed found tail induction =>
      have backwardChecked : operandsBefore record.out gate = true :=
        (operandsBefore_eq_true_iff record.out gate).mpr backward
      simp [checkGatesFrom, decoded, keyed, range, ordered, backwardChecked,
        found, induction]

theorem allocation_check_complete
    {snapshot : Oak.CNFDenseAllocation.Snapshot} {gates : List RawGate}
    (accepted : Oak.CNFDenseAllocation.Accepted snapshot gates) :
    Oak.CNFDenseAllocation.check snapshot = some gates := by
  simp [Oak.CNFDenseAllocation.check, shapeCheck_complete accepted.shape,
    gateWalk_complete accepted.gateWalk]

theorem clause_check_complete
    {snapshot : Oak.CNFClauseTrace.Snapshot}
    {checked : Oak.CNFClauseTrace.Checked}
    (accepted : Oak.CNFClauseTrace.Accepted snapshot checked) :
    Oak.CNFClauseTrace.check snapshot = some checked := by
  simp only [Oak.CNFClauseTrace.check, accepted.allocation]
  rw [if_pos ⟨accepted.budget, accepted.nonempty⟩, accepted.obligation]
  exact if_pos ⟨accepted.builder, accepted.emitted⟩

def strictNatFrom (previous : Nat) : List Nat → Bool
  | [] => true
  | next :: rest => decide (previous < next) && strictNatFrom next rest

def strictNatIncreasing : List Nat → Bool
  | [] => true
  | first :: rest => strictNatFrom first rest

private theorem strictNatFrom_spec {values : List Nat} {previous : Nat}
    (accepted : strictNatFrom previous values = true) :
    values.Nodup ∧ ∀ value ∈ values, previous < value := by
  induction values generalizing previous with
  | nil => simp
  | cons next rest induction =>
      have conditions : decide (previous < next) = true ∧
          strictNatFrom next rest = true :=
        Bool.and_eq_true_iff.mp accepted
      have bound : previous < next := of_decide_eq_true conditions.1
      obtain ⟨tailUnique, tailBounds⟩ := induction conditions.2
      constructor
      · apply List.nodup_cons.mpr
        constructor
        · intro member
          exact Nat.lt_irrefl next (tailBounds next member)
        · exact tailUnique
      · intro value member
        rcases List.mem_cons.mp member with same | member
        · subst value
          exact bound
        · exact Nat.lt_trans bound (tailBounds value member)

theorem strictNatIncreasing_nodup {values : List Nat}
    (accepted : strictNatIncreasing values = true) : values.Nodup := by
  cases values with
  | nil => exact List.nodup_nil
  | cons first rest =>
      obtain ⟨tailUnique, tailBounds⟩ := strictNatFrom_spec accepted
      apply List.nodup_cons.mpr
      constructor
      · intro member
        exact Nat.lt_irrefl first (tailBounds first member)
      · exact tailUnique

theorem nodup_of_map_nodup {α : Type u} {β : Type v}
    (f : α → β) {values : List α}
    (distinct : (values.map f).Nodup) : values.Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons first rest induction =>
      have parts : f first ∉ rest.map f ∧ (rest.map f).Nodup :=
        List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      constructor
      · intro member
        exact parts.1 (List.mem_map.mpr ⟨first, member, rfl⟩)
      · exact induction parts.2

def memoCode : MemoKey → Nat
  | .binary op x y => ((op * 8192 + x) * 8192 + y) * 8192
  | .ite condition thenValue elseValue =>
      ((3 * 8192 + condition) * 8192 + thenValue) * 8192 + elseValue

theorem outputs_shape_of_sorted
    {snapshot : Oak.CNFDenseAllocation.Snapshot}
    (sorted : (outputs snapshot).mergeSort
        (fun left right : Nat => decide (left ≤ right)) =
      List.range' 1 snapshot.variables) :
    (outputs snapshot).Nodup ∧ denseCoverage snapshot = true := by
  have permutation : (List.range' 1 snapshot.variables).Perm (outputs snapshot) := by
    simpa only [sorted] using
      (List.mergeSort_perm (outputs snapshot)
        (fun left right : Nat => decide (left ≤ right)))
  constructor
  · exact permutation.nodup (List.nodup_range' 1)
  · unfold denseCoverage
    apply List.all_eq_true.mpr
    intro index member
    apply decide_eq_true
    apply permutation.mem_iff.mp
    apply List.mem_range'.mpr
    exact ⟨index, List.mem_range.mp member, by omega⟩

theorem lookupMemo_of_mem {memo : List MemoEntry} {entry : MemoEntry}
    (unique : (memo.map MemoEntry.key).Nodup)
    (member : entry ∈ memo) :
    lookupMemo? memo entry.key = some entry.output := by
  induction memo with
  | nil => simp at member
  | cons first rest induction =>
      have parts : first.key ∉ rest.map MemoEntry.key ∧
          (rest.map MemoEntry.key).Nodup :=
        List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | member
      · subst entry
        simp [lookupMemo?]
      · have different : first.key ≠ entry.key := by
          intro same
          exact parts.1 (List.mem_map.mpr ⟨entry, member, same.symm⟩)
        simp only [lookupMemo?, different, if_false]
        exact induction parts.2 member

def GateChunk (variables : Nat) (memo : List MemoEntry)
    (previous last : Nat) (records : List EncodedGate)
    (gates : List RawGate) : Prop :=
  ∀ (tailRecords : List EncodedGate) (tailGates : List RawGate),
    GatesAcceptedFrom variables memo last tailRecords tailGates →
    GatesAcceptedFrom variables memo previous
      (records ++ tailRecords) (gates ++ tailGates)

theorem GateChunk.nil (variables : Nat) (memo : List MemoEntry)
    (previous : Nat) :
    GateChunk variables memo previous previous [] [] := by
  intro tailRecords tailGates tail
  exact tail

theorem GateChunk.cons
    {variables previous last : Nat} {memo : List MemoEntry}
    {record : EncodedGate} {records : List EncodedGate}
    {gate : RawGate} {gates : List RawGate} {key : MemoKey}
    (decoded : record.decode? = some gate)
    (range : 0 < record.out ∧ record.out ≤ variables)
    (ordered : previous < record.out)
    (backward : OperandsBefore record.out gate)
    (keyed : memoKey? record = some key)
    (found : lookupMemo? memo key = some record.out)
    (tail : GateChunk variables memo record.out last records gates) :
    GateChunk variables memo previous last (record :: records) (gate :: gates) := by
  intro tailRecords tailGates accepted
  exact .cons decoded range ordered backward keyed found
    (tail tailRecords tailGates accepted)

theorem GateChunk.append
    {variables previous middle last : Nat} {memo : List MemoEntry}
    {leftRecords rightRecords : List EncodedGate}
    {leftGates rightGates : List RawGate}
    (left : GateChunk variables memo previous middle leftRecords leftGates)
    (right : GateChunk variables memo middle last rightRecords rightGates) :
    GateChunk variables memo previous last
      (leftRecords ++ rightRecords) (leftGates ++ rightGates) := by
  intro tailRecords tailGates accepted
  simpa only [List.append_assoc] using
    (left (rightRecords ++ tailRecords) (rightGates ++ tailGates)
      (right tailRecords tailGates accepted))

theorem GateChunk.close
    {variables previous last : Nat} {memo : List MemoEntry}
    {records : List EncodedGate} {gates : List RawGate}
    (chunk : GateChunk variables memo previous last records gates) :
    GatesAcceptedFrom variables memo previous records gates := by
  simpa only [List.append_nil] using
    (chunk [] [] (GatesAcceptedFrom.nil last))

theorem decodeClauses_append
    {left right : List (List Int)} {leftDecoded rightDecoded : List Clause}
    (leftAccepted : Oak.CNFClauseTrace.decodeClauses left = some leftDecoded)
    (rightAccepted : Oak.CNFClauseTrace.decodeClauses right = some rightDecoded) :
    Oak.CNFClauseTrace.decodeClauses (left ++ right) =
      some (leftDecoded ++ rightDecoded) := by
  induction left generalizing leftDecoded with
  | nil =>
      have same : [] = leftDecoded := Option.some.inj leftAccepted
      subst leftDecoded
      exact rightAccepted
  | cons clause rest induction =>
      cases headResult : Oak.CNFClauseTrace.decodeClause clause with
      | none =>
          simp [Oak.CNFClauseTrace.decodeClauses, headResult] at leftAccepted
      | some decodedClause =>
          cases tailResult : Oak.CNFClauseTrace.decodeClauses rest with
          | none =>
              simp [Oak.CNFClauseTrace.decodeClauses, headResult, tailResult]
                at leftAccepted
          | some decodedRest =>
              have same : decodedClause :: decodedRest = leftDecoded := by
                simpa only [Oak.CNFClauseTrace.decodeClauses, headResult,
                  tailResult, Option.some.injEq] using leftAccepted
              subst leftDecoded
              have tailAccepted := induction tailResult
              simp only [List.cons_append, Oak.CNFClauseTrace.decodeClauses,
                headResult, tailAccepted]

theorem encodeClauses_append (left right : List Clause) :
    Oak.CNFClauseTrace.encodeClauses (left ++ right) =
      Oak.CNFClauseTrace.encodeClauses left ++
        Oak.CNFClauseTrace.encodeClauses right := by
  simp only [Oak.CNFClauseTrace.encodeClauses, List.map_append]

theorem gateClauses_append (left right : List RawGate) :
    gateClauses (left ++ right) = gateClauses left ++ gateClauses right := by
  simp only [gateClauses, List.flatMap_append]

theorem encodeBuilderClauses (gates : List RawGate) (obligation : Clause) :
    Oak.CNFClauseTrace.encodeClauses (builderClauses gates obligation) =
      Oak.CNFClauseTrace.encodeClauses (gateClauses gates) ++
        [Oak.CNFClauseTrace.encodeClause obligation] := by
  rw [builderClauses, encodeClauses_append]
  rfl

end Oak.CNFCheckComposition
