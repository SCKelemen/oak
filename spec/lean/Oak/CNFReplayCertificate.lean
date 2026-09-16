import Oak.CNFReplayTerm
import Oak.CNFReplayMemo
import Oak.CNFClauseCertificate

/-!
# Certificate composition for replayed Boolean expressions

The supplied expression uses designated allocated input slots. Replaying its
exact folds and memo hits connects its initial-input semantics to the checked
final clause. A refutation of that database then refutes the expression.

This is a model theorem, with bounded production replay correspondence. It
does not establish the provenance of arbitrary Go word terms, bit widths or
adaptation, source lowering, symbolic execution, DIMACS bytes, or LRAT parser
behavior. Native compiler verdict authority remains unchanged.
-/

set_option autoImplicit false

namespace Oak.CNFReplayCertificate

open Oak.RupCheck Oak.TseitinCNF Oak.CNFBuilderTrace
open Oak.CNFReplayApply Oak.CNFReplayTerm

/-- Checked allocation discharges both memo meaning and input stability for
any replayed edge, including the constant roots that need no clause or RUP. -/
theorem checked_replay_sound {snapshot : Oak.CNFDenseAllocation.Snapshot}
    {gates : List RawGate} {maxInt edge : Nat} {term : Term}
    (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    (replayed : replayTerm snapshot maxInt term = some edge) (initial : Assignment) :
    evalEdge (evalSequence gates initial) edge = term.eval initial := by
  have consistent := evalSequence_gateConsistent
    (Oak.CNFDenseAllocation.check_wellFormed accepted) initial
  exact replayTerm_sound (Oak.CNFReplayMemo.check_memo_sound accepted _ consistent)
    (fun index member => check_input_stable accepted initial member) replayed

/-- The singleton final clause reads exactly the supplied nonconstant root,
with its original polarity. Its equality to the root is obtained from the
accepted clause trace, not supplied as a semantic premise. -/
theorem singleton_obligation_value {snapshot : Oak.CNFClauseTrace.Snapshot}
    {checked : Oak.CNFClauseTrace.Checked} {edge : Nat}
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (singleton : snapshot.obligation = [edge]) (assignment : Assignment) :
    clauseValue assignment checked.obligation = evalEdge assignment edge := by
  have exactObligation := Oak.CNFClauseTrace.check_obligation_exact traceAccepted
  have nonconstant : 2 ≤ edge := (exactObligation.2 edge (by simp [singleton])).1
  rw [exactObligation.1, singleton]
  simp only [List.map_cons, List.map_nil, clauseValue, List.any_cons, List.any_nil,
    Bool.or_false]
  exact (evalEdge_literal assignment edge nonconstant).symm

/-- Once the memo denotes the accepted gates, replay makes the term/root
connection constructive, including source-input stability. The allocation
composition discharges the local memo condition in the public wrapper below.
-/
theorem replayed_term_false_of_memo {snapshot : Oak.CNFClauseTrace.Snapshot}
    {checked : Oak.CNFClauseTrace.Checked} {database : Database}
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    {maxInt edge : Nat} {term : Term}
    (replayed : replayTerm snapshot.allocation maxInt term = some edge)
    (singleton : snapshot.obligation = [edge])
    (certificateAccepted : Oak.RupCheck.Accepted database) (initial : Assignment)
    (memoSound : MemoSound (evalSequence checked.gates initial) snapshot.allocation.memo) :
    term.eval initial = false := by
  have allocation := (Oak.CNFClauseTrace.check_accepted traceAccepted).allocation
  have stable := fun index member => check_input_stable allocation initial (index := index) member
  have rootMeaning := replayTerm_sound memoSound stable replayed
  have rootFalse := Oak.CNFClauseCertificate.accepted_refutes_obligation
    traceAccepted decoded certificateAccepted initial
  rw [singleton_obligation_value traceAccepted singleton, rootMeaning] at rootFalse
  exact rootFalse

/-- Checked allocation supplies memo soundness and input stability. No
term/root semantic equality or CNF-completeness premise is required. -/
theorem replayed_term_false {snapshot : Oak.CNFClauseTrace.Snapshot}
    {checked : Oak.CNFClauseTrace.Checked} {database : Database}
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    {maxInt edge : Nat} {term : Term}
    (replayed : replayTerm snapshot.allocation maxInt term = some edge)
    (singleton : snapshot.obligation = [edge])
    (certificateAccepted : Oak.RupCheck.Accepted database) (initial : Assignment) :
    term.eval initial = false := by
  have allocation := (Oak.CNFClauseTrace.check_accepted traceAccepted).allocation
  have consistent := evalSequence_gateConsistent
    (Oak.CNFDenseAllocation.check_wellFormed allocation) initial
  exact replayed_term_false_of_memo traceAccepted decoded replayed singleton
    certificateAccepted initial
    (Oak.CNFReplayMemo.check_memo_sound allocation _ consistent)

/-- For the supplied list of corresponding Boolean result expressions,
accepted replay and RUP imply equality at every original input assignment. -/
theorem replayed_pairs_equal {snapshot : Oak.CNFClauseTrace.Snapshot}
    {checked : Oak.CNFClauseTrace.Checked} {database : Database}
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    {maxInt edge : Nat} {pairs : List (Term × Term)}
    (replayed : replayTerm snapshot.allocation maxInt (differenceTerm pairs) = some edge)
    (singleton : snapshot.obligation = [edge])
    (certificateAccepted : Oak.RupCheck.Accepted database) (initial : Assignment) :
    ∀ pair ∈ pairs, pair.1.eval initial = pair.2.eval initial :=
  (differenceTerm_false_iff initial pairs).mp
    (replayed_term_false traceAccepted decoded replayed singleton certificateAccepted initial)

/-- Pack one side of the supplied result pairs in least-significant-bit-first
order. This defines model words, not a projection of arbitrary Go terms. -/
def resultWord (pairs : List (Term × Term)) (side : Term × Term → Term)
    (initial : Assignment) : BitVec pairs.length :=
  (BitVec.ofBoolListLE (pairs.map fun pair => (side pair).eval initial)).cast (by simp)

/-- The direct result-word theorem now obtains its root meaning by checked
replay. The two words are explicitly defined by the supplied bit expressions;
their correspondence with Go/source word terms remains a separate seam. -/
theorem replayed_words_equal {snapshot : Oak.CNFClauseTrace.Snapshot}
    {checked : Oak.CNFClauseTrace.Checked} {database : Database}
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    {maxInt edge : Nat} {pairs : List (Term × Term)}
    (replayed : replayTerm snapshot.allocation maxInt (differenceTerm pairs) = some edge)
    (singleton : snapshot.obligation = [edge])
    (certificateAccepted : Oak.RupCheck.Accepted database) (initial : Assignment) :
    resultWord pairs Prod.fst initial = resultWord pairs Prod.snd initial := by
  have equalBits := replayed_pairs_equal traceAccepted decoded replayed singleton
    certificateAccepted initial
  have equalLists : pairs.map (fun pair => pair.1.eval initial) =
      pairs.map (fun pair => pair.2.eval initial) := by
    exact List.map_congr_left equalBits
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofBoolListLE (pairs.map fun pair => pair.1.eval initial)).toNat =
    (BitVec.ofBoolListLE (pairs.map fun pair => pair.2.eval initial)).toNat
  rw [equalLists]

end Oak.CNFReplayCertificate
