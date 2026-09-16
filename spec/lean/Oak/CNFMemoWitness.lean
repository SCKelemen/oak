import Oak.CNFDenseAllocation

/-!
# Exact memo witnesses for accepted CNF snapshots

The dense-allocation checker checks every gate against the memo table.  Its
unique allocated outputs and equal gate/memo cardinalities also establish the
converse: every memo hit names a gate in the decoded sequence, with the exact
requested key.  Thus extra memo entries cannot authorize an unrecorded gate.

This is a theorem about accepted snapshots, not a proof of Go map projection
or of the builder's execution.  No compiler verdict authority is changed.
-/

set_option autoImplicit false

namespace Oak.CNFMemoWitness

open Oak.CNFBuilderTrace Oak.CNFDenseAllocation Oak.TseitinCNF

theorem lookupMemo?_mem {memo : List MemoEntry} {key : MemoKey} {out : Nat}
    (found : lookupMemo? memo key = some out) :
    (⟨key, out⟩ : MemoEntry) ∈ memo := by
  induction memo with
  | nil => simp [lookupMemo?] at found
  | cons entry rest induction =>
      simp only [lookupMemo?] at found
      split at found
      · have keyEq : entry.key = key := by assumption
        have outEq : entry.output = out := Option.some.inj found
        have entryEq : entry = ⟨key, out⟩ := by
          cases entry
          simp_all
        exact List.mem_cons.mpr (Or.inl entryEq.symm)
      · exact List.mem_cons_of_mem _ (induction found)

/-- A duplicate-free subset with equal length has no missing members, even
when uniqueness of the larger list has not separately been assumed. -/
private theorem reverse_subset_of_length {α : Type} {left right : List α}
    (unique : left.Nodup) (subset : left ⊆ right)
    (sameLength : left.length = right.length) : right ⊆ left := by
  classical
  intro value member
  by_cases missing : value ∈ left
  · exact missing
  have enlargedUnique : (value :: left).Nodup := List.nodup_cons.mpr ⟨missing, unique⟩
  have enlargedSubset : value :: left ⊆ right := by
    intro item itemMember
    rcases List.mem_cons.mp itemMember with rfl | itemMember
    · exact member
    · exact subset itemMember
  have tooLong := enlargedUnique.length_le_of_subset enlargedSubset
  simp only [List.length_cons] at tooLong
  omega

/-- The default key is unreachable for records in an accepted gate walk. -/
private def recordEntry (record : EncodedGate) : MemoEntry :=
  ⟨(memoKey? record).getD (.binary 0 0 0), record.out⟩

theorem GatesAcceptedFrom.decoded_member {variables previous : Nat}
    {memo : List MemoEntry} {records : List EncodedGate} {gates : List RawGate}
    (accepted : GatesAcceptedFrom variables memo previous records gates)
    {record : EncodedGate} (member : record ∈ records) :
    ∃ gate, record.decode? = some gate ∧ gate ∈ gates := by
  induction accepted with
  | nil => contradiction
  | cons decoded range ordered backward keyed found tail induction =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, decoded, List.mem_cons_self⟩
      · obtain ⟨gate, decoded, gateMember⟩ := induction member
        exact ⟨gate, decoded, List.mem_cons_of_mem _ gateMember⟩

/-- Every successful memo lookup in an accepted snapshot has both an encoded
record and its decoded gate in the checked sequence.  Exact key and output
equalities are recovered without an additional memo-soundness premise. -/
theorem check_memo_has_gate {snapshot : Snapshot} {gates : List RawGate}
    {key : MemoKey} {out : Nat}
    (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    (found : lookupMemo? snapshot.memo key = some out) :
    ∃ record gate, record ∈ snapshot.gates ∧ record.decode? = some gate ∧
      gate ∈ gates ∧ memoKey? record = some key ∧ record.out = out := by
  have checked := check_accepted accepted
  have entriesSubset : snapshot.gates.map recordEntry ⊆ snapshot.memo := by
    intro entry member
    obtain ⟨record, recordMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨gate, recordKey, decoded, backward, keyed, hit⟩ :=
      checked.gateWalk.gate_has_exact_memo recordMember
    simpa [recordEntry, keyed] using lookupMemo?_mem hit
  have outputUnique : (snapshot.gates.map EncodedGate.out).Nodup :=
    (List.nodup_append.mp checked.shape.outputUnique).2.1
  have entriesUnique : (snapshot.gates.map recordEntry).Nodup := by
    apply List.Pairwise.of_map (S := fun left right : Nat => left ≠ right) MemoEntry.output
      (fun _ _ different equal => different (congrArg MemoEntry.output equal))
    simpa [List.Nodup, List.map_map, Function.comp_def, recordEntry] using outputUnique
  have sameLength : (snapshot.gates.map recordEntry).length = snapshot.memo.length := by
    simpa using checked.shape.memoCount.symm
  have reverseSubset := reverse_subset_of_length entriesUnique entriesSubset sameLength
  obtain ⟨record, recordMember, entryEq⟩ :=
    List.mem_map.mp (reverseSubset (lookupMemo?_mem found))
  obtain ⟨gate, decoded, gateMember⟩ := GatesAcceptedFrom.decoded_member checked.gateWalk recordMember
  obtain ⟨_, recordKey, _, _, keyed, _⟩ :=
    checked.gateWalk.gate_has_exact_memo recordMember
  have keyEq : recordKey = key := by
    simpa [recordEntry, keyed] using congrArg MemoEntry.key entryEq
  have outEq : record.out = out := congrArg MemoEntry.output entryEq
  exact ⟨record, gate, recordMember, decoded, gateMember, keyed.trans (congrArg some keyEq), outEq⟩

end Oak.CNFMemoWitness
