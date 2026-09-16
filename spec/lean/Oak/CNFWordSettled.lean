import Oak.CNFWordCertificate

/-!
# Constant-false word disequality, without a refutation certificate

The native bitwise audit can settle equality when its checked direct
disequality root is false. This model checks allocation even on that path,
projects both complete named words, and replays the root rather than taking
an unbound supplied zero as evidence. No clause, DIMACS or RUP is needed.

Acceptance proves equality for every typed model input. A true or nonconstant
root refuses this equality-only checker; refusal does not imply inequality.
Arbitrary Go graph/table projection, pointer-memo/intermediate-root coverage,
complete native admission, source/ISA correspondence, and compiler verdict
authority remain outside this theorem. This is not a new compiler consumer.
-/

set_option autoImplicit false

namespace Oak.CNFWordSettled

open Oak.RupCheck Oak.TseitinCNF Oak.CNFReplayTerm
open Oak.CNFWordInput Oak.CNFWordProjection Oak.CNFWordCertificate

/-- Both allocation and complete word pairing must pass before constant-false
replay can settle equality. In particular, a malformed snapshot cannot be
hidden behind constant folds, and unequal widths cannot be silently zipped.
-/
def checkEqual (snapshot : Oak.CNFDenseAllocation.Snapshot)
    (parameters : List Parameter) (maxInt : Nat) (left right : WordTerm) : Bool :=
  match Oak.CNFDenseAllocation.check snapshot,
      projectPair snapshot parameters maxInt left right with
  | some _, some pairs =>
      decide (replayTerm snapshot maxInt (differenceTerm pairs) = some 0)
  | _, _ => false

theorem settled_bits_equal {snapshot : Oak.CNFDenseAllocation.Snapshot}
    {gates : List RawGate} {parameters : List Parameter} {maxInt : Nat}
    {left right : WordTerm} {pairs : List (Term × Term)}
    (allocation : Oak.CNFDenseAllocation.check snapshot = some gates)
    (projected : projectPair snapshot parameters maxInt left right = some pairs)
    (replayed : replayTerm snapshot maxInt (differenceTerm pairs) = some 0)
    (inputs : Inputs) :
    left.width = right.width ∧ ∀ bit, left.bitValue inputs bit = right.bitValue inputs bit := by
  let initial := initialAssignment snapshot parameters inputs
  have meaning := Oak.CNFReplayCertificate.checked_replay_sound allocation replayed initial
  have rootFalse : (differenceTerm pairs).eval initial = false := by
    simpa only [Oak.CNFReplayApply.evalEdge_zero] using meaning.symm
  exact projected_bits_equal_of_pairs allocation projected inputs
    ((differenceTerm_false_iff initial pairs).mp rootFalse)

/-- An accepted settled equality is valid for every typed input, not only
for sampled values. No root/word equality, memo semantics or CNF-completeness
premise is assumed, and no external refutation certificate is required. -/
theorem checkEqual_sound {snapshot : Oak.CNFDenseAllocation.Snapshot}
    {parameters : List Parameter} {maxInt : Nat} {left right : WordTerm}
    (accepted : checkEqual snapshot parameters maxInt left right = true) (inputs : Inputs) :
    left.width = right.width ∧ (left.eval inputs).toNat = (right.eval inputs).toNat := by
  unfold checkEqual at accepted
  cases allocation : Oak.CNFDenseAllocation.check snapshot with
  | none => simp [allocation] at accepted
  | some gates =>
      cases projected : projectPair snapshot parameters maxInt left right with
      | none => simp [allocation, projected] at accepted
      | some pairs =>
          simp only [allocation, projected] at accepted
          have replayed := of_decide_eq_true accepted
          obtain ⟨sameWidth, equalBits⟩ :=
            settled_bits_equal allocation projected replayed inputs
          exact ⟨sameWidth, words_equal_of_bits inputs sameWidth equalBits⟩

end Oak.CNFWordSettled
