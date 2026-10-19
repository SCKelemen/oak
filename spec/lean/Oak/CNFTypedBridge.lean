import Oak.CNFTypedNode
import Oak.CNFTypedReadInput
import Oak.CNFTypedMemory

/-!
# Supplied typed derivations and concrete implication soundness

The derivation constructors carry executable local root checks and exact
source/read-table equalities, not unexplained term/root semantic premises.
Their inductive soundness composes typed circuit rules, allocation-derived
input meaning, and the structural concrete-memory embedding. Constructing an
accepted derivation for every node of a captured Go graph and obtaining an
accepted refutation of that same database are separate instance obligations.
-/

set_option autoImplicit false

namespace Oak.CNFTypedBridge

open Oak.RupCheck Oak.TseitinCNF Oak.CNFReplayApply Oak.CNFReplayTerm
open Oak.CNFTypedCircuit Oak.CNFTypedNode Oak.CNFTypedMemory
open Oak.CNFWordInput

structure ReadKey where
  span : String
  index : Word 32

def defaultReadKey : ReadKey := ⟨"", .constant 0⟩

structure Context where
  allocation : Oak.CNFDenseAllocation.Snapshot
  parameters : List Parameter
  reads : List ReadKey
  maxInt : Nat

def slotReads (context : Context) (reads : IndependentReads) : Oak.CNFTypedReadInput.Reads :=
  fun slot => let key := context.reads.getD slot defaultReadKey
    reads key.span key.index

def initial (context : Context) (scalars : Scalars) (reads : IndependentReads) : Assignment :=
  Oak.CNFTypedReadInput.initialAssignment context.allocation context.parameters scalars
    (slotReads context reads)

/-- Source vectors use only positive allocated outputs. -/
def sourceRoot? (snapshot : Oak.CNFDenseAllocation.Snapshot) (maxInt source : Nat) : Option Nat :=
  if source ≤ maxInt then
    match lookupInput? snapshot.inputs source with
    | none => none
    | some output =>
        if 0 < output ∧ output ≤ snapshot.variables ∧ output ≤ maxInt / 2 then
          some (2 * output) else none
  else none

def checkSources (context : Context) (width : Nat) (source : Nat → Nat) (roots : List Nat) : Bool :=
  decide (roots.length = width) && (List.range width).all fun bit =>
    decide (sourceRoot? context.allocation context.maxInt (source bit) = some (roots.getD bit 0))

private theorem sourceRoot_sound {context : Context} {gates : List RawGate}
    {source edge : Nat} (accepted : Oak.CNFDenseAllocation.check context.allocation = some gates)
    (found : sourceRoot? context.allocation context.maxInt source = some edge)
    (scalars : Scalars) (reads : IndependentReads) :
    evalEdge (evalSequence gates (initial context scalars reads)) edge =
      Oak.CNFTypedReadInput.sourceBit context.parameters scalars (slotReads context reads) source := by
  unfold sourceRoot? at found
  split at found
  · cases lookup : lookupInput? context.allocation.inputs source with
    | none => simp [lookup] at found
    | some output =>
        simp only [lookup] at found
        split at found
        · rename_i bounds
          cases Option.some.inj found
          exact Oak.CNFTypedReadInput.input_edge_meaning accepted lookup bounds.1 _ _ _
        · contradiction
  · contradiction

private theorem checkSources_spec {context : Context} {width : Nat}
    {source : Nat → Nat} {roots : List Nat}
    (checked : checkSources context width source roots = true) :
    roots.length = width ∧ ∀ bit, bit < width →
      sourceRoot? context.allocation context.maxInt (source bit) = some (roots.getD bit 0) := by
  simpa [checkSources, List.all_eq_true, List.mem_range] using checked

def binaryCircuit (width : Nat) (op : BinaryOp) (left right : Bits) : Option Bits :=
  match op with
  | .and => some (fun bit => .binary 0 (left bit) (right bit))
  | .or => some (fun bit => .binary 1 (left bit) (right bit))
  | .xor => some (fun bit => .binary 2 (left bit) (right bit))
  | .add => some (sumTerm left right (.constant false))
  | .sub => some (sumTerm left (complementBits right) (.constant true))
  | .shl =>
      if width = 32 then some (barrelBits width true left right 5)
      else if width = 64 then some (barrelBits width true left right 6) else none
  | .shr =>
      if width = 32 then some (barrelBits width false left right 5)
      else if width = 64 then some (barrelBits width false left right 6) else none

theorem binaryCircuit_meaning {width : Nat} {op : BinaryOp} {assignment : Assignment}
    {left right circuits : Bits} {a b : BitVec width}
    (built : binaryCircuit width op left right = some circuits)
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    Meaning assignment circuits (Oak.CNFTypedMemory.binaryValue op a b) := by
  cases op with
  | and =>
      cases Option.some.inj built
      intro bit within
      change ((left bit).eval assignment && (right bit).eval assignment) = (a &&& b).getLsbD bit
      rw [BitVec.getLsbD_and, leftMeaning bit within, rightMeaning bit within]
  | or =>
      cases Option.some.inj built
      intro bit within
      change ((left bit).eval assignment || (right bit).eval assignment) = (a ||| b).getLsbD bit
      rw [BitVec.getLsbD_or, leftMeaning bit within, rightMeaning bit within]
  | xor =>
      cases Option.some.inj built
      intro bit within
      change xor ((left bit).eval assignment) ((right bit).eval assignment) = (a ^^^ b).getLsbD bit
      rw [BitVec.getLsbD_xor, leftMeaning bit within, rightMeaning bit within]
  | add =>
      cases Option.some.inj built
      exact add_meaning leftMeaning rightMeaning
  | sub =>
      cases Option.some.inj built
      exact sub_meaning leftMeaning rightMeaning
  | shl =>
      simp only [binaryCircuit] at built
      split at built
      · rename_i widthEq
        subst width
        cases Option.some.inj built
        exact barrel32_meaning leftMeaning rightMeaning true
      · split at built
        · rename_i widthEq
          subst width
          cases Option.some.inj built
          exact barrel64_meaning leftMeaning rightMeaning true
        · contradiction
  | shr =>
      simp only [binaryCircuit] at built
      split at built
      · rename_i widthEq
        subst width
        cases Option.some.inj built
        exact barrel32_meaning leftMeaning rightMeaning false
      · split at built
        · rename_i widthEq
          subst width
          cases Option.some.inj built
          exact barrel64_meaning leftMeaning rightMeaning false
        · contradiction

def comparisonCircuit (width : Nat) (op : CompareOp) (left right : Bits) : Term :=
  match op with
  | .eq => equalFrom left right width (.constant true)
  | .ne => .complement (equalFrom left right width (.constant true))
  | .lo => .complement (carryTerm left (complementBits right) (.constant true) width)
  | .hs => carryTerm left (complementBits right) (.constant true) width

theorem comparisonCircuit_meaning {width : Nat} {op : CompareOp} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    (comparisonCircuit width op left right).eval assignment = compareValue op a b := by
  apply Bool.eq_iff_iff.mpr
  cases op with
  | eq => simpa [comparisonCircuit, compareValue] using eq_meaning leftMeaning rightMeaning
  | ne => simpa [comparisonCircuit, compareValue] using ne_meaning leftMeaning rightMeaning
  | lo => simpa [comparisonCircuit, compareValue] using lo_true_iff leftMeaning rightMeaning
  | hs => simpa [comparisonCircuit, compareValue] using hs_true_iff leftMeaning rightMeaning

/-- Syntactic Boolean range evidence, including declared-width-one values
and wide views of comparisons. -/
inductive BooleanWord : {width : Nat} → Word width → Prop where
  | narrow (term : Word 1) : BooleanWord term
  | view {width : Nat} {term : Word width} (useWidth : Nat)
      (boolean : BooleanWord term) : BooleanWord (.view useWidth term)
  | constant {width : Nat} (value : BitVec width) (bounded : value.toNat ≤ 1) :
      BooleanWord (.constant value)

theorem BooleanWord.range {width : Nat} {term : Word width}
    (boolean : BooleanWord term) (scalars : Scalars) (reads : IndependentReads) :
    (abstractEval scalars reads term).toNat ≤ 1 := by
  induction boolean with
  | narrow term => have bound := (abstractEval scalars reads term).isLt; omega
  | view useWidth boolean ih =>
      simp only [abstractEval, BitVec.toNat_setWidth]
      exact Nat.le_trans (Nat.mod_le _ _) ih
  | constant value bounded => exact bounded

theorem BooleanWord.guard {width : Nat} {term : Word width}
    (boolean : BooleanWord term) (scalars : Scalars) (reads : IndependentReads) :
    ((abstractEval scalars reads term).toNat != 0) =
      (abstractEval scalars reads term).getLsbD 0 := by
  have bound := boolean.range scalars reads
  have casesValue : (abstractEval scalars reads term).toNat = 0 ∨
      (abstractEval scalars reads term).toNat = 1 := by omega
  rcases casesValue with h | h <;> simp [BitVec.getLsbD, h]

/-- Every constructor is a syntactic/local-circuit check. The read constructor
also requires a derivation of the index, even though its abstract result is an
independent class word. -/
inductive Derivation (context : Context) : {width : Nat} → Word width → List Nat → Prop where
  | constant {width : Nat} (value : BitVec width) (roots : List Nat)
      (checked : checkVector context.allocation context.maxInt width
        (fun bit => .constant (value.getLsbD bit)) roots = true) :
      Derivation context (.constant value) roots
  | parameter {declared position : Nat} {name : String} {roots : List Nat}
      (atIndex : context.parameters[position]? = some ⟨name, declared⟩)
      (bounded : position < context.parameters.length) (widthBound : declared ≤ 64)
      (checked : checkSources context declared
        (fun bit => bit * (context.parameters.length + 8) + position) roots = true) :
      Derivation context (.parameter declared name) roots
  | view {width : Nat} {value : Word width} {child roots : List Nat} (useWidth : Nat)
      (childDerived : Derivation context value child)
      (checked : checkVector context.allocation context.maxInt useWidth
        (adapt width useWidth (rootBits child)) roots = true) :
      Derivation context (.view useWidth value) roots
  | binary {width : Nat} {left right : Word width} {leftRoots rightRoots roots : List Nat}
      (op : BinaryOp) (circuits : Bits)
      (leftDerived : Derivation context left leftRoots)
      (rightDerived : Derivation context right rightRoots)
      (built : binaryCircuit width op (rootBits leftRoots) (rootBits rightRoots) = some circuits)
      (checked : checkVector context.allocation context.maxInt width circuits roots = true) :
      Derivation context (.binary op left right) roots
  | compare {width : Nat} {left right : Word width} {leftRoots rightRoots roots : List Nat}
      (op : CompareOp) (leftDerived : Derivation context left leftRoots)
      (rightDerived : Derivation context right rightRoots)
      (checked : checkVector context.allocation context.maxInt 1
        (boolBits (comparisonCircuit width op (rootBits leftRoots) (rootBits rightRoots))) roots = true) :
      Derivation context (.compare op left right) roots
  | ite {width guardWidth : Nat} {guard : Word guardWidth} {left right : Word width}
      {guardRoots leftRoots rightRoots roots : List Nat}
      (guardDerived : Derivation context guard guardRoots)
      (leftDerived : Derivation context left leftRoots)
      (rightDerived : Derivation context right rightRoots)
      (positive : 0 < guardWidth) (boolean : BooleanWord guard)
      (checked : checkVector context.allocation context.maxInt width
        (muxBits (.input (guardRoots.getD 0 0)) (rootBits leftRoots) (rootBits rightRoots)) roots = true) :
      Derivation context (.ite guard left right) roots
  | read {span : String} {index : Word 32} {indexRoots roots : List Nat} {slot : Nat}
      (indexDerived : Derivation context index indexRoots)
      (atIndex : context.reads[slot]? = some ⟨span, index⟩)
      (checked : checkSources context 32
        (Oak.CNFTypedReadInput.readSource context.parameters.length slot) roots = true) :
      Derivation context (.read span index) roots

/-- The semantic bridge is proved by induction over the supplied derivation.
The only public assumptions are structural checks, allocation acceptance, and
the derivation constructors above. -/
theorem Derivation.sound {context : Context} {gates : List RawGate}
    {width : Nat} {term : Word width} {roots : List Nat}
    (derived : Derivation context term roots)
    (accepted : Oak.CNFDenseAllocation.check context.allocation = some gates)
    (scalars : Scalars) (reads : IndependentReads) :
    RootMeaning (evalSequence gates (initial context scalars reads)) roots
      (abstractEval scalars reads term) := by
  induction derived with
  | constant value roots checked =>
      apply checked_node_sound accepted checked
      intro bit within
      rfl
  | @parameter declared position name roots atIndex bounded widthBound checked =>
      obtain ⟨length, found⟩ := checkSources_spec checked
      refine ⟨length, ?_⟩
      intro bit within
      change evalEdge _ (roots.getD bit 0) = _
      rw [sourceRoot_sound accepted (found bit within)]
      rw [Oak.CNFTypedReadInput.sourceBit_parameter atIndex bounded _ _ bit (by omega)]
      simp [abstractEval, within]
  | view useWidth childDerived checked childIH =>
      exact checked_node_sound accepted checked _ (adapt_meaning useWidth childIH.2)
  | binary op circuits leftDerived rightDerived built checked leftIH rightIH =>
      exact checked_node_sound accepted checked _
        (binaryCircuit_meaning built leftIH.2 rightIH.2)
  | @compare width left right leftRoots rightRoots roots op leftDerived rightDerived checked leftIH rightIH =>
      have meaning := boolBits_meaning 1 (edgeAssignment (evalSequence gates
        (initial context scalars reads)))
          (comparisonCircuit width op (rootBits leftRoots) (rootBits rightRoots))
      rw [comparisonCircuit_meaning leftIH.2 rightIH.2] at meaning
      simpa only [boolWord, BitVec.setWidth_eq, abstractEval] using
        checked_node_sound accepted checked _ meaning
  | @ite width guardWidth guard left right guardRoots leftRoots rightRoots roots
      guardDerived leftDerived rightDerived positive boolean checked guardIH leftIH rightIH =>
      have guardMeaning := guardIH.2 0 positive
      dsimp only [rootBits] at guardMeaning
      have guardTruth := boolean.guard scalars reads
      have meaning := muxBits_meaning (condition := .input (guardRoots.getD 0 0))
        leftIH.2 rightIH.2
      rw [guardMeaning, ← guardTruth] at meaning
      exact checked_node_sound accepted checked _ meaning
  | @read span index indexRoots roots slot indexDerived atIndex checked indexIH =>
      obtain ⟨length, found⟩ := checkSources_spec checked
      refine ⟨length, ?_⟩
      intro bit within
      change evalEdge _ (roots.getD bit 0) = _
      rw [sourceRoot_sound accepted (found bit within),
        Oak.CNFTypedReadInput.sourceBit_read _ _ _ slot bit within]
      simp [slotReads, List.getD_eq_getElem?_getD, atIndex, abstractEval]

/-- A concrete violation constructs a model of the exact checked database.
This is the one-way embedding needed for an UNSAT-only conclusion. -/
theorem concrete_violation_models {context : Context}
    {snapshot : Oak.CNFClauseTrace.Snapshot} {checked : Oak.CNFClauseTrace.Checked}
    {database : Database} {width edge : Nat} {premise : Word 1} {left right : Word width}
    (sameAllocation : context.allocation = snapshot.allocation)
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    (derived : Derivation context (implication premise left right) [edge])
    (polarity : snapshot.obligation = [flipEdge edge])
    (scalars : Scalars) (memory : Memory)
    (premiseTrue : (concreteEval scalars memory premise).toNat ≠ 0)
    (different : concreteEval scalars memory left ≠ concreteEval scalars memory right) :
    ∃ assignment, Models assignment database := by
  have allocation : Oak.CNFDenseAllocation.check context.allocation = some checked.gates := by
    rw [sameAllocation]
    exact (Oak.CNFClauseTrace.check_accepted traceAccepted).allocation
  let reads := embedReads scalars memory
  let input := initial context scalars reads
  have meaning := derived.sound allocation scalars reads
  have rootMeaning := meaning.2 0 (by decide)
  change evalEdge (evalSequence checked.gates input) edge =
    (abstractEval scalars reads (implication premise left right)).getLsbD 0 at rootMeaning
  have concreteZero := (implication_false_iff premise left right scalars memory).mpr
    ⟨premiseTrue, different⟩
  have rootFalse : evalEdge (evalSequence checked.gates input) edge = false := by
    simpa [reads, concrete_embeds, BitVec.getLsbD, concreteZero] using rootMeaning
  have finalTrue : clauseValue (evalSequence checked.gates input) checked.obligation = true := by
    rw [Oak.CNFReplayCertificate.singleton_obligation_value traceAccepted polarity,
      evalEdge_flip, rootFalse]
    rfl
  exact ⟨evalSequence checked.gates input,
    Oak.CNFClauseTrace.check_evalSequence_models_of_obligation traceAccepted decoded input
      ((clauseValue_eq_true_iff _ _).mp finalTrue)⟩

/-- A checked propositional refutation composes with the constructive typed
and memory bridge. This is a generic supplied-model theorem; it does not
assert that a particular Go snapshot or LRAT execution supplies its premises. -/
theorem refutation_implies_concrete {context : Context}
    {snapshot : Oak.CNFClauseTrace.Snapshot} {checked : Oak.CNFClauseTrace.Checked}
    {database : Database} {width edge : Nat} {premise : Word 1} {left right : Word width}
    (sameAllocation : context.allocation = snapshot.allocation)
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    (derived : Derivation context (implication premise left right) [edge])
    (polarity : snapshot.obligation = [flipEdge edge])
    (refuted : Unsatisfiable database) :
    ∀ scalars memory, (concreteEval scalars memory premise).toNat ≠ 0 →
      concreteEval scalars memory left = concreteEval scalars memory right := by
  intro scalars memory premiseTrue
  by_cases equal : concreteEval scalars memory left = concreteEval scalars memory right
  · exact equal
  · obtain ⟨assignment, model⟩ := concrete_violation_models sameAllocation traceAccepted decoded
      derived polarity scalars memory premiseTrue equal
    exact False.elim (refuted assignment model)

theorem accepted_implies_concrete {context : Context}
    {snapshot : Oak.CNFClauseTrace.Snapshot} {checked : Oak.CNFClauseTrace.Checked}
    {database : Database} {width edge : Nat} {premise : Word 1} {left right : Word width}
    (sameAllocation : context.allocation = snapshot.allocation)
    (traceAccepted : Oak.CNFClauseTrace.check snapshot = some checked)
    (decoded : Oak.CNFClauseTrace.emittedDatabase? snapshot = some database)
    (derived : Derivation context (implication premise left right) [edge])
    (polarity : snapshot.obligation = [flipEdge edge])
    (certificateAccepted : Oak.RupCheck.Accepted database) :
    ∀ scalars memory, (concreteEval scalars memory premise).toNat ≠ 0 →
      concreteEval scalars memory left = concreteEval scalars memory right :=
  refutation_implies_concrete sameAllocation traceAccepted decoded derived polarity
    (accepted_unsatisfiable certificateAccepted)

end Oak.CNFTypedBridge
