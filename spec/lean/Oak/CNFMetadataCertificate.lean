import Oak.CNFReplayHeader
import Oak.CNFWordCertificate

/-!
# Metadata-checked word certificates

The header check precedes word projection, so even constant-only words must
have a valid complete parameter/index/width table. The returned ordered
parameters are exactly those used to bind named bits in the existing word
certificate theorem; callers do not supply a separate validity premise.

This composes checks on supplied metadata and model words. It does not prove
that arbitrary Go pointer graphs or tables are faithfully projected, that
every intermediate producer root was visited, or that replay bookkeeping is
immutable. `CNFReplayCoverage` separately proves the count-completion law for
admitted recordings against a fixed producer. The equality theorem here is
the nonconstant singleton/RUP path, not settled-outcome or verdict authority.
-/

set_option autoImplicit false

namespace Oak.CNFMetadataCertificate

open Oak.RupCheck Oak.CNFReplayTerm
open Oak.CNFWordInput Oak.CNFWordProjection

structure CheckedWords where
  parameters : List Parameter
  pairs : List (Term × Term)

def projectWords (header : Oak.CNFReplayHeader.Snapshot)
    (allocation : Oak.CNFDenseAllocation.Snapshot) (maxInt : Nat)
    (left right : WordTerm) : Option CheckedWords :=
  match Oak.CNFReplayHeader.check header with
  | none => none
  | some parameters =>
      match Oak.CNFWordCertificate.projectPair allocation parameters maxInt left right with
      | none => none
      | some pairs => some ⟨parameters, pairs⟩

theorem projectWords_spec {header : Oak.CNFReplayHeader.Snapshot}
    {allocation : Oak.CNFDenseAllocation.Snapshot} {maxInt : Nat}
    {left right : WordTerm} {words : CheckedWords}
    (projected : projectWords header allocation maxInt left right = some words) :
    Oak.CNFReplayHeader.check header = some words.parameters ∧
      parametersValid words.parameters = true ∧
      Oak.CNFWordCertificate.projectPair allocation words.parameters maxInt left right =
        some words.pairs := by
  unfold projectWords at projected
  cases headerChecked : Oak.CNFReplayHeader.check header with
  | none => simp [headerChecked] at projected
  | some parameters =>
      cases pairChecked : Oak.CNFWordCertificate.projectPair allocation parameters maxInt
          left right with
      | none => simp [headerChecked, pairChecked] at projected
      | some pairs =>
          simp only [headerChecked, pairChecked, Option.some.injEq] at projected
          subst words
          exact ⟨rfl, Oak.CNFReplayHeader.check_parameters_valid headerChecked,
            pairChecked⟩

/-- The complete checked metadata is valid, and the independently interpreted
model words have equal widths and values. All named input bindings use the
same parameters produced by the header check. No root-meaning equality is
assumed, and no numeric coverage check is mistaken for a semantic premise. -/
theorem metadata_words_equal {header : Oak.CNFReplayHeader.Snapshot}
    {snapshot : Oak.CNFClauseTrace.Snapshot} {checked : Oak.CNFClauseTrace.Checked}
    {database : Database}
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    {maxInt edge : Nat} {left right : WordTerm} {words : CheckedWords}
    (projected : projectWords header snapshot.allocation maxInt left right = some words)
    (replayed : replayTerm snapshot.allocation maxInt (differenceTerm words.pairs) = some edge)
    (singleton : snapshot.obligation = [edge])
    (certificateAccepted : Oak.RupCheck.Accepted database) (inputs : Inputs) :
    parametersValid words.parameters = true ∧ left.width = right.width ∧
      (left.eval inputs).toNat = (right.eval inputs).toNat := by
  obtain ⟨_, valid, pairsProjected⟩ := projectWords_spec projected
  exact ⟨valid, Oak.CNFWordCertificate.projected_words_equal traceAccepted decoded
    pairsProjected replayed singleton certificateAccepted inputs⟩

private def validHeader : Oak.CNFReplayHeader.Snapshot :=
  ⟨["a", "b"], [("a", 0), ("b", 1)], [("a", 8), ("b", 8)], false, false, 0⟩

private def missingFirstIndex : Oak.CNFReplayHeader.Snapshot :=
  { validHeader with index := [("ghost", 0), ("b", 1)] }

private def emptyAllocation : Oak.CNFDenseAllocation.Snapshot := ⟨0, false, [], [], []⟩

-- Constant words do not excuse malformed unused parameter metadata.
example : (projectWords validHeader emptyAllocation 1024
    (.constant 8 42) (.constant 8 42)).isSome = true := by decide

example : (projectWords missingFirstIndex emptyAllocation 1024
    (.constant 8 42) (.constant 8 42)).isSome = false := by decide

end Oak.CNFMetadataCertificate
