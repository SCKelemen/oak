import Oak.CNFReplayCoverage

/-!
# Executable checked replay recordings

Input and gate recordings require an explicitly present producer allocation
and a positive, bounded, safely doubled output. Term recordings require the
producer's exact root vector. Repeated writes preserve existing key positions;
fresh writes prepend their keys. Accepted runs from empty establish the
admitted-state invariant required by `CNFReplayCoverage`.

Producer contents are fixed throughout a run. Natural term identities and
gate identities require faithful injective projections of Go pointers and
CNF keys. Signed fields, nil pointers and Go map projection remain boundary
obligations. Input/gate flag values are erased to membership: the real maps
record `true`, and completion observes their keys/counts. Term roots are
caller-computed data here; these helpers do not validate syntax, widths,
expression evaluation, source provenance or complete traversal of a graph.
-/

set_option autoImplicit false

namespace Oak.CNFReplayRecording

open Oak.CNFReplayCoverage

structure Snapshot where
  terms : List TermEntry
  inputs : List (Nat × Nat)
  gates : List (Nat × Nat)
  variables : Nat
  maxInt : Nat
  deriving Repr, DecidableEq

def producer (snapshot : Snapshot) : Producer :=
  ⟨snapshot.terms, snapshot.inputs.map Prod.fst, snapshot.gates.map Prod.fst⟩

def lookupOutput? : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | allocation :: rest, key =>
      if allocation.1 = key then some allocation.2 else lookupOutput? rest key

def touchKey (key : Nat) (keys : List Nat) : List Nat :=
  if key ∈ keys then keys else key :: keys

/-- Replace an existing entry without changing its position. The states
reached from empty have unique keys, as proved below. -/
def replaceTerm (key : Nat) (roots : List Nat) : List TermEntry → List TermEntry
  | [] => []
  | entry :: rest =>
      if entry.key = key then ⟨key, roots⟩ :: rest
      else entry :: replaceTerm key roots rest

def upsertTerm (key : Nat) (roots : List Nat) (entries : List TermEntry) : List TermEntry :=
  if key ∈ termKeys entries then replaceTerm key roots entries
  else ⟨key, roots⟩ :: entries

def inputEdge (snapshot : Snapshot) (state : State) (key : Nat) : Option (Nat × State) :=
  match lookupOutput? snapshot.inputs key with
  | none => none
  | some output =>
      if 0 < output ∧ output ≤ snapshot.variables ∧ output ≤ snapshot.maxInt / 2 then
        some (2 * output, { state with inputs := touchKey key state.inputs })
      else none

def gateEdge (snapshot : Snapshot) (state : State) (key : Nat) : Option (Nat × State) :=
  match lookupOutput? snapshot.gates key with
  | none => none
  | some output =>
      if 0 < output ∧ output ≤ snapshot.variables ∧ output ≤ snapshot.maxInt / 2 then
        some (2 * output, { state with gates := touchKey key state.gates })
      else none

def recordTerm (snapshot : Snapshot) (state : State) (key : Nat)
    (roots : List Nat) : Option State :=
  match lookupTerm? snapshot.terms key with
  | none => none
  | some expected =>
      if roots = expected then some { state with terms := upsertTerm key roots state.terms }
      else none

/-- Successful input recording exposes the exact producer allocation,
guarded output, doubled edge, and membership update. -/
theorem inputEdge_spec {snapshot : Snapshot} {state next : State} {key edge : Nat}
    (accepted : inputEdge snapshot state key = some (edge, next)) :
    ∃ output, lookupOutput? snapshot.inputs key = some output ∧
      0 < output ∧ output ≤ snapshot.variables ∧ output ≤ snapshot.maxInt / 2 ∧
      edge = 2 * output ∧ next = { state with inputs := touchKey key state.inputs } := by
  unfold inputEdge at accepted
  cases found : lookupOutput? snapshot.inputs key with
  | none => simp [found] at accepted
  | some output =>
      simp only [found] at accepted
      split at accepted
      · rename_i bounds
        have resultEq := Option.some.inj accepted
        exact ⟨output, rfl, bounds.1, bounds.2.1, bounds.2.2,
          (congrArg Prod.fst resultEq).symm, (congrArg Prod.snd resultEq).symm⟩
      · contradiction

/-- Successful gate recording retains the exact requested key; only its
producer output is doubled after the range checks. -/
theorem gateEdge_spec {snapshot : Snapshot} {state next : State} {key edge : Nat}
    (accepted : gateEdge snapshot state key = some (edge, next)) :
    ∃ output, lookupOutput? snapshot.gates key = some output ∧
      0 < output ∧ output ≤ snapshot.variables ∧ output ≤ snapshot.maxInt / 2 ∧
      edge = 2 * output ∧ next = { state with gates := touchKey key state.gates } := by
  unfold gateEdge at accepted
  cases found : lookupOutput? snapshot.gates key with
  | none => simp [found] at accepted
  | some output =>
      simp only [found] at accepted
      split at accepted
      · rename_i bounds
        have resultEq := Option.some.inj accepted
        exact ⟨output, rfl, bounds.1, bounds.2.1, bounds.2.2,
          (congrArg Prod.fst resultEq).symm, (congrArg Prod.snd resultEq).symm⟩
      · contradiction

theorem inputEdge_safe {snapshot : Snapshot} {state next : State} {key edge : Nat}
    (accepted : inputEdge snapshot state key = some (edge, next)) :
    0 < edge ∧ edge ≤ snapshot.maxInt := by
  obtain ⟨output, _, positive, _, bounded, equal, _⟩ := inputEdge_spec accepted
  rw [equal]
  omega

theorem gateEdge_safe {snapshot : Snapshot} {state next : State} {key edge : Nat}
    (accepted : gateEdge snapshot state key = some (edge, next)) :
    0 < edge ∧ edge ≤ snapshot.maxInt := by
  obtain ⟨output, _, positive, _, bounded, equal, _⟩ := gateEdge_spec accepted
  rw [equal]
  omega

theorem lookupOutput?_mem {allocations : List (Nat × Nat)} {key output : Nat}
    (found : lookupOutput? allocations key = some output) : (key, output) ∈ allocations := by
  induction allocations with
  | nil => simp [lookupOutput?] at found
  | cons allocation rest induction =>
      simp only [lookupOutput?] at found
      split at found
      · have keyEq : allocation.1 = key := by assumption
        have outputEq : allocation.2 = output := Option.some.inj found
        exact List.mem_cons.mpr (Or.inl (Prod.ext keyEq outputEq).symm)
      · exact List.mem_cons_of_mem _ (induction found)

private theorem replaceTerm_unchanged {entries : List TermEntry} {key : Nat} {roots : List Nat}
    (agreement : ∀ entry ∈ entries, entry.key = key → entry.roots = roots) :
    replaceTerm key roots entries = entries := by
  induction entries with
  | nil => rfl
  | cons entry rest induction =>
      simp only [replaceTerm]
      split
      · rename_i sameKey
        have sameRoots := agreement entry (by simp) sameKey
        have sameEntry : (⟨key, roots⟩ : TermEntry) = entry := by
          cases entry
          simp_all
        rw [sameEntry]
      · rw [induction (fun candidate member => agreement candidate (List.mem_cons_of_mem _ member))]

/-- Rewriting an already admitted term with the same producer roots is a
no-op. This uses the prior supported-state invariant, not arbitrary state
contents supplied by a caller. -/
theorem upsertTerm_existing {snapshot : Snapshot} {state : State} {key : Nat} {roots : List Nat}
    (supported : Supported (producer snapshot) state)
    (existing : key ∈ termKeys state.terms)
    (admitted : lookupTerm? snapshot.terms key = some roots) :
    upsertTerm key roots state.terms = state.terms := by
  simp only [upsertTerm, existing, if_true]
  apply replaceTerm_unchanged
  intro entry member sameKey
  have agreement := supported.termAgreement entry member
  change lookupTerm? snapshot.terms entry.key = some entry.roots at agreement
  rw [sameKey, admitted] at agreement
  exact (Option.some.inj agreement).symm

theorem inputEdge_reachable {snapshot : Snapshot} {state next : State} {key edge : Nat}
    (prior : Reachable (producer snapshot) state)
    (accepted : inputEdge snapshot state key = some (edge, next)) :
    Reachable (producer snapshot) next := by
  unfold inputEdge at accepted
  cases found : lookupOutput? snapshot.inputs key with
  | none => simp [found] at accepted
  | some output =>
      simp only [found] at accepted
      split at accepted
      · have stateEq := congrArg Prod.snd (Option.some.inj accepted)
        simp only at stateEq
        subst next
        have supportedKey : key ∈ (producer snapshot).inputs :=
          List.mem_map.mpr ⟨(key, output), lookupOutput?_mem found, rfl⟩
        by_cases existing : key ∈ state.inputs
        · simpa [touchKey, existing] using prior
        · simpa [touchKey, existing] using Reachable.input prior key existing supportedKey
      · contradiction

theorem gateEdge_reachable {snapshot : Snapshot} {state next : State} {key edge : Nat}
    (prior : Reachable (producer snapshot) state)
    (accepted : gateEdge snapshot state key = some (edge, next)) :
    Reachable (producer snapshot) next := by
  unfold gateEdge at accepted
  cases found : lookupOutput? snapshot.gates key with
  | none => simp [found] at accepted
  | some output =>
      simp only [found] at accepted
      split at accepted
      · have stateEq := congrArg Prod.snd (Option.some.inj accepted)
        simp only at stateEq
        subst next
        have supportedKey : key ∈ (producer snapshot).gates :=
          List.mem_map.mpr ⟨(key, output), lookupOutput?_mem found, rfl⟩
        by_cases existing : key ∈ state.gates
        · simpa [touchKey, existing] using prior
        · simpa [touchKey, existing] using Reachable.gate prior key existing supportedKey
      · contradiction

theorem recordTerm_reachable {snapshot : Snapshot} {state next : State} {key : Nat}
    {roots : List Nat} (prior : Reachable (producer snapshot) state)
    (accepted : recordTerm snapshot state key roots = some next) :
    Reachable (producer snapshot) next := by
  unfold recordTerm at accepted
  cases found : lookupTerm? snapshot.terms key with
  | none => simp [found] at accepted
  | some expected =>
      simp only [found] at accepted
      split at accepted
      · rename_i equalRoots
        subst expected
        have stateEq := Option.some.inj accepted
        subst next
        by_cases existing : key ∈ termKeys state.terms
        · have unchanged := upsertTerm_existing (reachable_supported prior) existing found
          simpa only [unchanged] using prior
        · simpa [upsertTerm, existing] using Reachable.term prior key roots existing found
      · contradiction

inductive Event where
  | input (key : Nat)
  | gate (key : Nat)
  | term (key : Nat) (roots : List Nat)
  deriving Repr, DecidableEq

def step (snapshot : Snapshot) (state : State) : Event → Option State
  | .input key => (inputEdge snapshot state key).map Prod.snd
  | .gate key => (gateEdge snapshot state key).map Prod.snd
  | .term key roots => recordTerm snapshot state key roots

def runFrom (snapshot : Snapshot) : State → List Event → Option State
  | state, [] => some state
  | state, event :: events =>
      match step snapshot state event with
      | none => none
      | some next => runFrom snapshot next events

def run (snapshot : Snapshot) (events : List Event) : Option State :=
  runFrom snapshot empty events

theorem step_reachable {snapshot : Snapshot} {state next : State} {event : Event}
    (prior : Reachable (producer snapshot) state)
    (accepted : step snapshot state event = some next) :
    Reachable (producer snapshot) next := by
  cases event with
  | input key =>
      cases recorded : inputEdge snapshot state key with
      | none => simp [step, recorded] at accepted
      | some result =>
          rcases result with ⟨edge, result⟩
          simp only [step, recorded, Option.map_some, Option.some.injEq] at accepted
          subst next
          exact inputEdge_reachable prior recorded
  | gate key =>
      cases recorded : gateEdge snapshot state key with
      | none => simp [step, recorded] at accepted
      | some result =>
          rcases result with ⟨edge, result⟩
          simp only [step, recorded, Option.map_some, Option.some.injEq] at accepted
          subst next
          exact gateEdge_reachable prior recorded
  | term key roots => exact recordTerm_reachable prior accepted

theorem runFrom_reachable {snapshot : Snapshot} {initial final : State} {events : List Event}
    (prior : Reachable (producer snapshot) initial)
    (accepted : runFrom snapshot initial events = some final) :
    Reachable (producer snapshot) final := by
  induction events generalizing initial with
  | nil =>
      simp only [runFrom, Option.some.injEq] at accepted
      subst final
      exact prior
  | cons event events induction =>
      simp only [runFrom] at accepted
      cases recorded : step snapshot initial event with
      | none => simp [recorded] at accepted
      | some next =>
          simp only [recorded] at accepted
          exact induction (step_reachable prior recorded) accepted

/-- The concrete recording decisions establish the previously relational
coverage premise for a supplied event sequence, including repeated writes. -/
theorem run_reachable {snapshot : Snapshot} {events : List Event} {final : State}
    (accepted : run snapshot events = some final) : Reachable (producer snapshot) final :=
  runFrom_reachable .empty accepted

private def exampleSnapshot : Snapshot :=
  ⟨[⟨3, [2, 4]⟩], [(0, 1)], [(9, 2)], 2, 8⟩

-- Repeated recordings are executable no-ops after their first admission.
example : run exampleSnapshot
    [.input 0, .input 0, .gate 9, .gate 9, .term 3 [2, 4], .term 3 [2, 4]] =
    some ⟨[⟨3, [2, 4]⟩], [0], [9]⟩ := by decide

example : run exampleSnapshot [.term 3 [2, 5]] = none := by decide

end Oak.CNFReplayRecording
