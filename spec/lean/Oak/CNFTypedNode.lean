import Oak.CNFTypedCircuit
import Oak.CNFReplayCertificate

/-!
# Checked local typed-node roots

A supplied node circuit is replayed from established child edges and compared
with every recorded output edge. The resulting rule is compositional: child
meanings come from earlier node derivations, and mux/arithmetic rules provide
the local circuit meaning. No semantic equality is inferred from a hash or
from repeating the producer. Complete graph coverage remains a separate
check; this module does not claim an actual captured-instance theorem.
-/

set_option autoImplicit false

namespace Oak.CNFTypedNode

open Oak.RupCheck Oak.TseitinCNF Oak.CNFReplayApply Oak.CNFReplayTerm
open Oak.CNFTypedCircuit

abbrev Snapshot := Oak.CNFDenseAllocation.Snapshot

def rootBits (roots : List Nat) : Bits := fun bit => .input (roots.getD bit 0)

def RootMeaning {width : Nat} (assignment : Assignment) (roots : List Nat)
    (value : BitVec width) : Prop :=
  roots.length = width ∧ Meaning (edgeAssignment assignment) (rootBits roots) value

/-- Every result bit is checked, including zero-extended high bits. -/
def checkVector (snapshot : Snapshot) (maxInt width : Nat)
    (circuits : Bits) (roots : List Nat) : Bool :=
  decide (roots.length = width) && (List.range width).all fun bit =>
    decide (replayCircuit snapshot maxInt (circuits bit) = some (roots.getD bit 0))

theorem checkVector_sound {snapshot : Snapshot} {maxInt width : Nat}
    {assignment : Assignment} {circuits : Bits} {roots : List Nat} {value : BitVec width}
    (sound : MemoSound assignment snapshot.memo)
    (checked : checkVector snapshot maxInt width circuits roots = true)
    (meaning : Meaning (edgeAssignment assignment) circuits value) :
    RootMeaning assignment roots value := by
  simp only [checkVector, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at checked
  refine ⟨checked.1, ?_⟩
  intro bit within
  exact (replayCircuit_sound sound (checked.2 bit within)).trans (meaning bit within)

/-- The public wrapper discharges memo semantics from the exact accepted
allocation and its constructive gate evaluation. -/
theorem checked_node_sound {snapshot : Snapshot} {gates : List RawGate}
    {maxInt width : Nat} {circuits : Bits} {roots : List Nat} {value : BitVec width}
    (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    (checked : checkVector snapshot maxInt width circuits roots = true)
    (initial : Assignment)
    (meaning : Meaning (edgeAssignment (evalSequence gates initial)) circuits value) :
    RootMeaning (evalSequence gates initial) roots value := by
  have consistent := evalSequence_gateConsistent
    (Oak.CNFDenseAllocation.check_wellFormed accepted) initial
  exact checkVector_sound (Oak.CNFReplayMemo.check_memo_sound accepted _ consistent)
    checked meaning

/-- Root bit zero of a nonempty Boolean word is exactly its truth value. -/
theorem RootMeaning.boolean {width : Nat} {assignment : Assignment} {roots : List Nat}
    {truth : Bool} (positive : 0 < width)
    (meaning : RootMeaning assignment roots (boolWord width truth)) :
    evalEdge assignment (roots.getD 0 0) = truth := by
  have bit := meaning.2 0 positive
  simpa [rootBits, Term.eval, edgeAssignment, boolWord, BitVec.getLsbD_ofBool, positive] using bit

/-- A locally replayed implication root has the original polarity: the
complemented claim denotes premise AND disequality. -/
theorem implication_root_meaning {snapshot : Snapshot} {maxInt : Nat}
    {assignment : Assignment} {premise equality result : Nat} {p q : Bool}
    (sound : MemoSound assignment snapshot.memo)
    (premiseMeaning : evalEdge assignment premise = p)
    (equalityMeaning : evalEdge assignment equality = q)
    (checked : replayIte snapshot.variables maxInt snapshot.memo premise equality 1 = some result) :
    evalEdge assignment (flipEdge result) = (p && !q) := by
  rw [evalEdge_flip, replayIte_sound sound checked, premiseMeaning, equalityMeaning]
  cases p <;> cases q <;> rfl

end Oak.CNFTypedNode
