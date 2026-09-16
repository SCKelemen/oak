import Oak.CNFReplayCertificate
import Oak.CNFWordProjection

/-!
# Checked word projection in the native certificate chain

Result pairing must retain both complete, nonempty bit lists. In particular,
list zip alone is not a width check: unmatched result bits must reject rather
than silently disappear from the asserted disequality.

Successful projection supplies named-input binding and word-bit meaning to
the existing checked replay/clause/RUP chain. The independent model words
then agree at every typed input. This is the nonconstant singleton-obligation
path, not a theorem about settled roots or the complete Go admission policy.
Faithful projection of actual Go graphs/tables, source lowering, symbolic
execution, DIMACS bytes, LRAT implementation, and verdict authority remain
separate obligations.
-/

set_option autoImplicit false

namespace Oak.CNFWordCertificate

open Oak.RupCheck Oak.CNFReplayTerm
open Oak.CNFWordInput Oak.CNFWordProjection

def pairBits (left right : List Term) : Option (List (Term × Term)) :=
  if left.length = right.length ∧ left ≠ [] then some (left.zip right)
  else none

theorem pairBits_accepted {left right : List Term} {pairs : List (Term × Term)}
    (accepted : pairBits left right = some pairs) :
    left.length = right.length ∧ left ≠ [] ∧ pairs = left.zip right := by
  unfold pairBits at accepted
  split at accepted
  · rename_i conditions
    exact ⟨conditions.1, conditions.2, (Option.some.inj accepted).symm⟩
  · contradiction

theorem paired_evaluations_equal (initial : Assignment) {left right : List Term}
    (sameLength : left.length = right.length)
    (equalPairs : ∀ pair ∈ left.zip right, pair.1.eval initial = pair.2.eval initial) :
    left.map (Term.eval initial) = right.map (Term.eval initial) := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all
  | cons head tail induction =>
      cases right with
      | nil => simp at sameLength
      | cons other rest =>
          have heads := equalPairs (head, other) (by simp)
          have tails : tail.map (Term.eval initial) = rest.map (Term.eval initial) :=
            induction (by simpa using sameLength)
              (fun pair member => equalPairs pair (by simp [member]))
          simp [heads, tails]

/-- Project both complete word expressions before admitting their paired
result bits. Width agreement is checked through the proved projection lengths.
-/
def projectPair (snapshot : Oak.CNFDenseAllocation.Snapshot)
    (parameters : List Parameter) (maxInt : Nat) (left right : WordTerm) :
    Option (List (Term × Term)) :=
  match projectWord snapshot parameters maxInt left,
      projectWord snapshot parameters maxInt right with
  | some leftBits, some rightBits => pairBits leftBits rightBits
  | _, _ => none

theorem projectPair_spec {snapshot : Oak.CNFDenseAllocation.Snapshot}
    {parameters : List Parameter} {maxInt : Nat} {left right : WordTerm}
    {pairs : List (Term × Term)}
    (projected : projectPair snapshot parameters maxInt left right = some pairs) :
    ∃ leftBits rightBits,
      projectWord snapshot parameters maxInt left = some leftBits ∧
      projectWord snapshot parameters maxInt right = some rightBits ∧
      leftBits.length = rightBits.length ∧ pairs = leftBits.zip rightBits := by
  unfold projectPair at projected
  cases leftProjection : projectWord snapshot parameters maxInt left with
  | none => simp [leftProjection] at projected
  | some leftBits =>
      cases rightProjection : projectWord snapshot parameters maxInt right with
      | none => simp [leftProjection, rightProjection] at projected
      | some rightBits =>
          simp only [leftProjection, rightProjection] at projected
          have paired := pairBits_accepted projected
          exact ⟨leftBits, rightBits, rfl, rfl, paired.1, paired.2.2⟩

private theorem eval_getD (initial : Assignment) (bits : List Term) (bit : Nat) :
    (bits.getD bit (.constant false)).eval initial =
      (bits.map (Term.eval initial)).getD bit false := by
  induction bits generalizing bit with
  | nil => simp [Term.eval]
  | cons head tail induction =>
      cases bit <;> simp_all

/-- Accepted word projection constructs the input binding and result-bit
meaning used by the certificate theorem. Both widths and every bit agree;
no semantic model-word-to-bit or named-input-to-slot equality is supplied as a premise.
-/
theorem projected_bits_equal {snapshot : Oak.CNFClauseTrace.Snapshot}
    {checked : Oak.CNFClauseTrace.Checked} {database : Database}
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    {parameters : List Parameter} {maxInt edge : Nat} {left right : WordTerm}
    {pairs : List (Term × Term)}
    (projected : projectPair snapshot.allocation parameters maxInt left right = some pairs)
    (replayed : replayTerm snapshot.allocation maxInt (differenceTerm pairs) = some edge)
    (singleton : snapshot.obligation = [edge])
    (certificateAccepted : Oak.RupCheck.Accepted database) (inputs : Inputs) :
    left.width = right.width ∧ ∀ bit, left.bitValue inputs bit = right.bitValue inputs bit := by
  obtain ⟨leftBits, rightBits, leftProjection, rightProjection, sameLength, pairsEq⟩ :=
    projectPair_spec projected
  have allocation := (Oak.CNFClauseTrace.check_accepted traceAccepted).allocation
  let initial := initialAssignment snapshot.allocation parameters inputs
  have equalPairs := Oak.CNFReplayCertificate.replayed_pairs_equal
    traceAccepted decoded replayed singleton certificateAccepted initial
  rw [pairsEq] at equalPairs
  have equalValues := paired_evaluations_equal initial sameLength equalPairs
  refine ⟨(projectWord_length leftProjection).symm.trans
    (sameLength.trans (projectWord_length rightProjection)), ?_⟩
  intro bit
  have leftMeaning := projectWord_sound_all allocation leftProjection inputs bit
  have rightMeaning := projectWord_sound_all allocation rightProjection inputs bit
  rw [← leftMeaning, ← rightMeaning]
  change (leftBits.getD bit (.constant false)).eval initial =
    (rightBits.getD bit (.constant false)).eval initial
  rw [eval_getD, eval_getD, equalValues]

/-- Equality of the independently interpreted model words, with matching
widths derived from admission. The remaining boundary is faithful projection
of actual Go/source terms and tables, not an assumed equality between these
model words and their checked Boolean roots. -/
theorem projected_words_equal {snapshot : Oak.CNFClauseTrace.Snapshot}
    {checked : Oak.CNFClauseTrace.Checked} {database : Database}
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    {parameters : List Parameter} {maxInt edge : Nat} {left right : WordTerm}
    {pairs : List (Term × Term)}
    (projected : projectPair snapshot.allocation parameters maxInt left right = some pairs)
    (replayed : replayTerm snapshot.allocation maxInt (differenceTerm pairs) = some edge)
    (singleton : snapshot.obligation = [edge])
    (certificateAccepted : Oak.RupCheck.Accepted database) (inputs : Inputs) :
    left.width = right.width ∧ (left.eval inputs).toNat = (right.eval inputs).toNat := by
  obtain ⟨sameWidth, equalBits⟩ := projected_bits_equal
    traceAccepted decoded projected replayed singleton certificateAccepted inputs
  refine ⟨sameWidth, ?_⟩
  have equalLists : (List.range left.width).map (left.bitValue inputs) =
      (List.range right.width).map (right.bitValue inputs) := by
    rw [sameWidth]
    exact List.map_congr_left (fun bit _ => equalBits bit)
  change (BitVec.ofBoolListLE ((List.range left.width).map (left.bitValue inputs))).toNat =
    (BitVec.ofBoolListLE ((List.range right.width).map (right.bitValue inputs))).toNat
  rw [equalLists]

example : pairBits [] [] = none := by decide
example : pairBits [.constant false] [] = none := by decide
example : (pairBits [.constant false] [.constant true]).isSome = true := by decide

end Oak.CNFWordCertificate
