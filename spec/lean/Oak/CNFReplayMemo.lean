import Oak.CNFReplayApply
import Oak.CNFMemoWitness

/-!
# Checked gate snapshots discharge native replay memo soundness

A decoded, gate-consistent dense snapshot gives every binary memo lookup the
Boolean meaning of its exact key.  The reverse memo witness excludes extra
entries, and the edge decoder ties both operand polarities to the existing
Tseitin semantics.  Thus the replay operation's `MemoSound` condition follows
from checked allocation and gate consistency, not an additional assumption
about an arbitrary unique table.
-/

set_option autoImplicit false

namespace Oak.CNFReplayMemo

open Oak.RupCheck Oak.TseitinCNF Oak.CNFBuilderTrace
open Oak.CNFDenseAllocation Oak.CNFReplayApply Oak.CNFMemoWitness

theorem evalLiteral_of_decoded_edge {edge : Nat} {literal : Literal}
    (decoded : literalOfEdge? edge = some literal) (assignment : Assignment) :
    evalLiteral assignment literal = evalEdge assignment edge := by
  unfold literalOfEdge? at decoded
  split at decoded
  · contradiction
  · rename_i nonconstant
    have literalEq := Option.some.inj decoded
    subst literal
    exact (evalEdge_literal assignment edge (by omega)).symm

private theorem binary_key_fields {record : EncodedGate} {op x y : Nat}
    (keyed : memoKey? record = some (.binary op x y)) :
    record.op = op ∧ record.x = x ∧ record.y = y := by
  unfold memoKey? at keyed
  split at keyed <;> (try split at keyed) <;> simp_all

theorem decoded_binary_value {record : EncodedGate} {gate : RawGate}
    {op x y : Nat} (admitted : op < 3)
    (decoded : record.decode? = some gate)
    (keyed : memoKey? record = some (.binary op x y)) (assignment : Assignment) :
    gate.value assignment =
      binaryValue op (evalEdge assignment x) (evalEdge assignment y) := by
  obtain ⟨operation, left, right⟩ := binary_key_fields keyed
  obtain ⟨leftLiteral, rightLiteral, leftDecoded, rightDecoded, gateEq⟩ :=
    decodeGate_binary (by omega) decoded
  subst gate
  rw [← operation]
  rw [← left, ← right]
  have leftValue := evalLiteral_of_decoded_edge leftDecoded assignment
  have rightValue := evalLiteral_of_decoded_edge rightDecoded assignment
  have casesOp : op = 0 ∨ op = 1 ∨ op = 2 := by omega
  rcases casesOp with rfl | rfl | rfl
  all_goals simp [operation, RawGate.value, binaryValue, leftValue, rightValue]

/-- Accepted allocation plus gate consistency gives the replay's entire
memo-soundness condition, including every lookup rather than only the
gate-to-memo direction checked by the production walk. -/
theorem check_memo_sound {snapshot : Snapshot} {gates : List RawGate}
    (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    (assignment : Assignment) (consistent : GateConsistent assignment gates) :
    MemoSound assignment snapshot.memo := by
  intro op x y output admitted found
  obtain ⟨record, gate, _, decoded, member, keyed, outputEq⟩ :=
    check_memo_has_gate accepted found
  have holds := consistent gate member
  unfold RawGate.Holds at holds
  rw [decodeGate_output decoded, outputEq] at holds
  exact holds.trans (decoded_binary_value admitted decoded keyed assignment)

end Oak.CNFReplayMemo
