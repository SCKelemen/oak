import Oak.CNFDenseAllocation

/-!
# Native CNF replay completion and admitted domain coverage

`finish` is the numeric projection of `nativeCNFReplay.finish`: it compares
three replay-map sizes and the nine scalar fields of the saved builder shape.
Those checks alone do not inspect keys, roots, or any builder content.

The coverage theorem additionally requires a state reached from empty by
admitted recordings against one fixed producer. Term recording requires an
exact producer lookup and root vector; input and gate recordings require
producer membership. Unique replay keys and supported entries are preserved,
so matching counts then imply exact domains and term root vectors.

Natural term identities abstract Go pointers; natural gate identities require
a faithful injective projection of CNF keys. Fixed producer contents, map
projection and the actual recording trace remain explicit boundaries. Shape
equality is only scalar snapshot equality, not content immutability. No graph
topology, term semantics, or native-verdict authority follows from this file.
-/

set_option autoImplicit false

namespace Oak.CNFReplayCoverage

/-- Field order is exactly `cnfObligationCounts` in the production checker. -/
structure Shape where
  variables : Nat
  clauses : Nat
  inputs : Nat
  gates : Nat
  gateMemo : Nat
  termMemo : Nat
  owners : Nat
  selects : Nat
  exceeded : Bool
  deriving Repr, DecidableEq

def finish (termCount inputCount gateCount : Nat) (start current : Shape) : Bool :=
  decide (termCount = current.termMemo) &&
    decide (inputCount = current.inputs) &&
    decide (gateCount = current.gateMemo) && decide (current = start)

theorem finish_iff (termCount inputCount gateCount : Nat) (start current : Shape) :
    finish termCount inputCount gateCount start current = true ↔
      termCount = current.termMemo ∧ inputCount = current.inputs ∧
      gateCount = current.gateMemo ∧ current = start := by
  simp [finish, and_assoc]

structure TermEntry where
  key : Nat
  roots : List Nat
  deriving Repr, DecidableEq

def termKeys (entries : List TermEntry) : List Nat := entries.map TermEntry.key

def lookupTerm? : List TermEntry → Nat → Option (List Nat)
  | [], _ => none
  | entry :: rest, key =>
      if entry.key = key then some entry.roots else lookupTerm? rest key

structure Producer where
  terms : List TermEntry
  inputs : List Nat
  gates : List Nat
  deriving Repr, DecidableEq

structure State where
  terms : List TermEntry
  inputs : List Nat
  gates : List Nat
  deriving Repr, DecidableEq

def empty : State := ⟨[], [], []⟩

/-- Closure of admitted fresh recordings against a fixed producer. Repeated
map writes do not change a state and therefore need no fresh transition.
Term cache hits likewise leave the previously admitted state unchanged. -/
inductive Reachable (producer : Producer) : State → Prop where
  | empty : Reachable producer empty
  | term {state : State} (prior : Reachable producer state) (key : Nat) (roots : List Nat)
      (fresh : key ∉ termKeys state.terms)
      (admitted : lookupTerm? producer.terms key = some roots) :
      Reachable producer { state with terms := ⟨key, roots⟩ :: state.terms }
  | input {state : State} (prior : Reachable producer state) (key : Nat)
      (fresh : key ∉ state.inputs) (admitted : key ∈ producer.inputs) :
      Reachable producer { state with inputs := key :: state.inputs }
  | gate {state : State} (prior : Reachable producer state) (key : Nat)
      (fresh : key ∉ state.gates) (admitted : key ∈ producer.gates) :
      Reachable producer { state with gates := key :: state.gates }

structure Supported (producer : Producer) (state : State) : Prop where
  termUnique : (termKeys state.terms).Nodup
  termAgreement : ∀ entry ∈ state.terms,
    lookupTerm? producer.terms entry.key = some entry.roots
  inputUnique : state.inputs.Nodup
  inputSupport : state.inputs ⊆ producer.inputs
  gateUnique : state.gates.Nodup
  gateSupport : state.gates ⊆ producer.gates

/-- Admission establishes the invariant which count-only completion needs. -/
theorem reachable_supported {producer : Producer} {state : State}
    (reachable : Reachable producer state) : Supported producer state := by
  induction reachable with
  | empty =>
      constructor <;> simp [empty, termKeys]
  | @term state prior key roots fresh admitted induction =>
      refine ⟨?_, ?_, induction.inputUnique, induction.inputSupport,
        induction.gateUnique, induction.gateSupport⟩
      · simpa [termKeys] using List.nodup_cons.mpr ⟨fresh, induction.termUnique⟩
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact admitted
        · exact induction.termAgreement entry member
  | @input state prior key fresh admitted induction =>
      refine ⟨induction.termUnique, induction.termAgreement,
        List.nodup_cons.mpr ⟨fresh, induction.inputUnique⟩, ?_,
        induction.gateUnique, induction.gateSupport⟩
      intro input member
      rcases List.mem_cons.mp member with rfl | member
      · exact admitted
      · exact induction.inputSupport member
  | @gate state prior key fresh admitted induction =>
      refine ⟨induction.termUnique, induction.termAgreement,
        induction.inputUnique, induction.inputSupport,
        List.nodup_cons.mpr ⟨fresh, induction.gateUnique⟩, ?_⟩
      intro gate member
      rcases List.mem_cons.mp member with rfl | member
      · exact admitted
      · exact induction.gateSupport member

theorem lookupTerm?_mem {entries : List TermEntry} {key : Nat} {roots : List Nat}
    (found : lookupTerm? entries key = some roots) : (⟨key, roots⟩ : TermEntry) ∈ entries := by
  induction entries with
  | nil => simp [lookupTerm?] at found
  | cons entry rest induction =>
      simp only [lookupTerm?] at found
      split at found
      · have keyEq : entry.key = key := by assumption
        have rootsEq : entry.roots = roots := Option.some.inj found
        have equal : entry = ⟨key, roots⟩ := by cases entry; simp_all
        exact List.mem_cons.mpr (Or.inl equal.symm)
      · exact List.mem_cons_of_mem _ (induction found)

theorem lookupTerm?_of_mem {entries : List TermEntry}
    (unique : (termKeys entries).Nodup) {entry : TermEntry} (member : entry ∈ entries) :
    lookupTerm? entries entry.key = some entry.roots := by
  induction entries with
  | nil => contradiction
  | cons head rest induction =>
      have separated := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | member
      · simp [lookupTerm?]
      · have different : head.key ≠ entry.key := by
          intro equal
          apply separated.1
          exact equal ▸ List.mem_map.mpr ⟨entry, member, rfl⟩
        simp only [lookupTerm?, different, if_false]
        exact induction separated.2 member

/-- A supported duplicate-free domain with matching cardinality is exact.
Uniqueness of the replay domain is essential; counts alone are insufficient. -/
theorem reverse_subset_of_length {α : Type} {left right : List α}
    (unique : left.Nodup) (subset : left ⊆ right)
    (sameLength : left.length = right.length) : right ⊆ left := by
  classical
  intro value member
  by_cases present : value ∈ left
  · exact present
  have enlargedUnique : (value :: left).Nodup := List.nodup_cons.mpr ⟨present, unique⟩
  have enlargedSubset : value :: left ⊆ right := by
    intro item itemMember
    rcases List.mem_cons.mp itemMember with rfl | itemMember
    · exact member
    · exact subset itemMember
  have tooLong := enlargedUnique.length_le_of_subset enlargedSubset
  simp only [List.length_cons] at tooLong
  omega

structure Exact (producer : Producer) (state : State) : Prop where
  termDomain : ∀ key, key ∈ termKeys state.terms ↔ key ∈ termKeys producer.terms
  termRoots : ∀ key roots,
    lookupTerm? state.terms key = some roots ↔ lookupTerm? producer.terms key = some roots
  inputDomain : ∀ key, key ∈ state.inputs ↔ key ∈ producer.inputs
  gateDomain : ∀ key, key ∈ state.gates ↔ key ∈ producer.gates

theorem supported_exact_of_counts {producer : Producer} {state : State}
    (supported : Supported producer state)
    (termCount : state.terms.length = producer.terms.length)
    (inputCount : state.inputs.length = producer.inputs.length)
    (gateCount : state.gates.length = producer.gates.length) : Exact producer state := by
  have termSubset : termKeys state.terms ⊆ termKeys producer.terms := by
    intro key member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨⟨entry.key, entry.roots⟩,
      lookupTerm?_mem (supported.termAgreement entry entryMember), rfl⟩
  have termReverse := reverse_subset_of_length supported.termUnique termSubset
    (by simpa [termKeys] using termCount)
  have inputReverse := reverse_subset_of_length supported.inputUnique supported.inputSupport inputCount
  have gateReverse := reverse_subset_of_length supported.gateUnique supported.gateSupport gateCount
  refine ⟨(fun _ => ⟨fun member => termSubset member, fun member => termReverse member⟩), ?_,
    (fun _ => ⟨fun member => supported.inputSupport member, fun member => inputReverse member⟩),
    (fun _ => ⟨fun member => supported.gateSupport member, fun member => gateReverse member⟩)⟩
  intro key roots
  constructor
  · intro found
    exact supported.termAgreement ⟨key, roots⟩ (lookupTerm?_mem found)
  · intro found
    have recordedKey : key ∈ termKeys state.terms := termReverse
      (List.mem_map.mpr ⟨⟨key, roots⟩, lookupTerm?_mem found, rfl⟩)
    obtain ⟨entry, member, keyEq⟩ := List.mem_map.mp recordedKey
    have agreement := supported.termAgreement entry member
    rw [keyEq, found] at agreement
    have rootsEq : roots = entry.roots := Option.some.inj agreement
    simpa [keyEq, rootsEq] using lookupTerm?_of_mem supported.termUnique member

/-- Numeric finish yields exact coverage only together with the admitted
recording invariant and the fixed producer's actual projected map counts.
The final conjunction records scalar shape equality, not content equality. -/
theorem finish_exact {producer : Producer} {state : State} {start current : Shape}
    (reachable : Reachable producer state)
    (completed : finish state.terms.length state.inputs.length state.gates.length start current = true)
    (termCount : current.termMemo = producer.terms.length)
    (inputCount : current.inputs = producer.inputs.length)
    (gateCount : current.gateMemo = producer.gates.length) :
    Exact producer state ∧ current = start := by
  obtain ⟨terms, inputs, gates, shape⟩ := (finish_iff _ _ _ _ _).mp completed
  exact ⟨supported_exact_of_counts (reachable_supported reachable)
    (terms.trans termCount) (inputs.trans inputCount) (gates.trans gateCount), shape⟩

/-! A forged same-size state passes numeric finish but is not admitted. -/

private def exampleProducer : Producer := ⟨[⟨0, [2]⟩], [0], [0]⟩
private def forgedState : State := ⟨[⟨9, [99]⟩], [9], [9]⟩
private def exampleShape : Shape := ⟨1, 1, 1, 1, 1, 1, 0, 0, false⟩

example : finish forgedState.terms.length forgedState.inputs.length forgedState.gates.length
    exampleShape exampleShape = true := by decide

example : ¬Reachable exampleProducer forgedState := by
  intro reachable
  have agreement := (reachable_supported reachable).termAgreement ⟨9, [99]⟩ (by decide)
  simp [exampleProducer, lookupTerm?] at agreement

end Oak.CNFReplayCoverage
