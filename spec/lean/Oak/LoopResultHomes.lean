import Oak.LoopArrayHomes

/-!
# Loop-scoped homes in a separate result region

This module lifts `Oak.LoopArrayHomes` to a world split into an exact result
region and external state. The split is an explicit premise of the model: it
is not derived from an ABI, caller allocation, or a no-alias theorem.

Cached execution may have stale backing result memory while selected values
live in scalar homes. Its logical result is `materialize`; resident execution
updates result memory directly. An admitted external step must supply both a
frame proof saying that it leaves the result region unchanged and a
noninterference proof saying that its external result is independent of the
result contents. Thus the theorems do not assert that arbitrary calls or
instructions are safe to interleave.

This is conditional algebra. It proves no Go matcher or generator refinement,
caller-allocation or AAPCS fact, ASL semantics, atomicity, memory ordering, or
backend code-generation property.
-/

namespace Oak.LoopResultHomes

/-- The exact logical result region. Bounds remain a separate obligation. -/
abbrev ResultMem (α : Type) := Oak.LoopArrayHomes.Mem α

/-- Cached result representation paired with state structurally outside it. -/
structure CachedWorld (α σ : Type) where
  result : Oak.LoopArrayHomes.State α
  external : σ

/-- Fully memory-resident result paired with the same kind of external state. -/
structure ResidentWorld (α σ : Type) where
  result : ResultMem α
  external : σ

/-- Cached and resident worlds agree on the logical result and external state.
The cached backing memory itself need not equal the resident result. -/
def Equivalent (selected : Nat → Bool) (cached : CachedWorld α σ)
    (resident : ResidentWorld α σ) : Prop :=
  Oak.LoopArrayHomes.materialize selected cached.result = resident.result ∧
    cached.external = resident.external

/-- Common initialization preloads homes without changing the logical result. -/
def preloadWorld (result : ResultMem α) (external : σ) : CachedWorld α σ :=
  { result := Oak.LoopArrayHomes.preload result, external }

/-- The matching fully resident initial world. -/
def residentWorld (result : ResultMem α) (external : σ) : ResidentWorld α σ :=
  { result, external }

theorem preload_equivalent (selected : Nat → Bool) (result : ResultMem α)
    (external : σ) :
    Equivalent selected (preloadWorld result external)
      (residentWorld result external) := by
  constructor
  · exact Oak.LoopArrayHomes.materialize_preload selected result
  · rfl

/-- An observer is result-blind when its observation cannot depend on any
contents of the exact result region. This is a supplied unobservability
premise, not a consequence of an ABI. -/
def ResultBlind (observe : ResultMem α → σ → ω) : Prop :=
  ∀ left right external, observe left external = observe right external

/-- A structurally external observer sees the same value in equivalent worlds. -/
theorem external_observation_eq (selected : Nat → Bool)
    (cached : CachedWorld α σ) (resident : ResidentWorld α σ)
    (observe : σ → ω) (hequivalent : Equivalent selected cached resident) :
    observe cached.external = observe resident.external := by
  exact congrArg observe hequivalent.2

/-- Even while cached backing result memory is stale, an explicitly
result-blind observer cannot distinguish it from resident result memory. -/
theorem resultBlind_observation_eq (selected : Nat → Bool)
    (cached : CachedWorld α σ) (resident : ResidentWorld α σ)
    (observe : ResultMem α → σ → ω) (hblind : ResultBlind observe)
    (hequivalent : Equivalent selected cached resident) :
    observe cached.result.memory cached.external =
      observe resident.result resident.external := by
  rw [hequivalent.2]
  exact hblind cached.result.memory resident.result resident.external

/-- An external action admitted for interleaving. `resultFrame` rules out a
result-region write. `resultBlind` rules out any externally visible dependence
on result contents; it is the semantic no-observation obligation supplied for
the particular action. -/
structure ExternalStep (α σ : Type) where
  run : ResultMem α → σ → ResultMem α × σ
  resultFrame : ∀ result external, (run result external).1 = result
  resultBlind : ∀ left right external,
    (run left external).2 = (run right external).2

/-- Cached execution exposes its actual backing result memory, which may be
stale while selected values live in homes, and retains its cached
representation. The step's blindness proof makes that stale view
unobservable externally. -/
def applyCachedExternal (step : ExternalStep α σ)
    (world : CachedWorld α σ) : CachedWorld α σ :=
  { result := world.result
    external := (step.run world.result.memory world.external).2 }

/-- Resident execution applies the same external-step relation directly. -/
def applyResidentExternal (step : ExternalStep α σ)
    (world : ResidentWorld α σ) : ResidentWorld α σ :=
  { result := (step.run world.result world.external).1
    external := (step.run world.result world.external).2 }

/-- A result-framed, result-blind external step preserves logical equivalence. -/
theorem externalStep_preserves_equivalent (selected : Nat → Bool)
    (step : ExternalStep α σ) (cached : CachedWorld α σ)
    (resident : ResidentWorld α σ)
    (hequivalent : Equivalent selected cached resident) :
    Equivalent selected (applyCachedExternal step cached)
      (applyResidentExternal step resident) := by
  rcases hequivalent with ⟨hresult, hexternal⟩
  constructor
  · change Oak.LoopArrayHomes.materialize selected cached.result =
      (step.run resident.result resident.external).1
    rw [step.resultFrame]
    exact hresult
  · change
      (step.run cached.result.memory cached.external).2 =
      (step.run resident.result resident.external).2
    rw [hexternal]
    exact step.resultBlind _ _ _

/-- Apply one ordinary result write to the cached representation. -/
def applyCachedWrite (selected : Nat → Bool)
    (world : CachedWorld α σ) (write : Oak.LoopArrayHomes.Write α) :
    CachedWorld α σ :=
  { result := Oak.LoopArrayHomes.writeCached selected world.result write
    external := world.external }

/-- Apply the same result write directly to resident memory. -/
def applyResidentWrite (world : ResidentWorld α σ)
    (write : Oak.LoopArrayHomes.Write α) : ResidentWorld α σ :=
  { result := Oak.LoopArrayHomes.writeResident world.result write
    external := world.external }

/-- One selected or unselected result write preserves world equivalence. -/
theorem resultWrite_preserves_equivalent (selected : Nat → Bool)
    (cached : CachedWorld α σ) (resident : ResidentWorld α σ)
    (write : Oak.LoopArrayHomes.Write α)
    (hequivalent : Equivalent selected cached resident) :
    Equivalent selected (applyCachedWrite selected cached write)
      (applyResidentWrite resident write) := by
  rcases hequivalent with ⟨hresult, hexternal⟩
  constructor
  · change
      Oak.LoopArrayHomes.materialize selected
          (Oak.LoopArrayHomes.writeCached selected cached.result write) =
        Oak.LoopArrayHomes.writeResident resident.result write
    rw [Oak.LoopArrayHomes.materialize_writeCached, hresult]
  · exact hexternal

/-- Interleavings consist only of ordinary result writes and external actions
carrying their frame and blindness proofs. -/
inductive Event (α σ : Type) where
  | resultWrite (write : Oak.LoopArrayHomes.Write α)
  | external (step : ExternalStep α σ)

def applyCachedEvent (selected : Nat → Bool) (world : CachedWorld α σ) :
    Event α σ → CachedWorld α σ
  | .resultWrite write => applyCachedWrite selected world write
  | .external step => applyCachedExternal step world

def applyResidentEvent (world : ResidentWorld α σ) :
    Event α σ → ResidentWorld α σ
  | .resultWrite write => applyResidentWrite world write
  | .external step => applyResidentExternal step world

/-- Run an admitted interleaving in program order over cached state. -/
def runCached (selected : Nat → Bool) (world : CachedWorld α σ) :
    List (Event α σ) → CachedWorld α σ
  | [] => world
  | event :: rest =>
      runCached selected (applyCachedEvent selected world event) rest

/-- Run the matching interleaving over fully resident result memory. -/
def runResident (world : ResidentWorld α σ) :
    List (Event α σ) → ResidentWorld α σ
  | [] => world
  | event :: rest => runResident (applyResidentEvent world event) rest

theorem event_preserves_equivalent (selected : Nat → Bool)
    (cached : CachedWorld α σ) (resident : ResidentWorld α σ)
    (event : Event α σ) (hequivalent : Equivalent selected cached resident) :
    Equivalent selected (applyCachedEvent selected cached event)
      (applyResidentEvent resident event) := by
  cases event with
  | resultWrite write =>
      exact resultWrite_preserves_equivalent selected cached resident write
        hequivalent
  | external step =>
      exact externalStep_preserves_equivalent selected step cached resident
        hequivalent

/-- Logical result and external state remain equal through any admitted
interleaving. Writes may target either selected or unselected result cells. -/
theorem run_preserves_equivalent (selected : Nat → Bool)
    (cached : CachedWorld α σ) (resident : ResidentWorld α σ)
    (events : List (Event α σ))
    (hequivalent : Equivalent selected cached resident) :
    Equivalent selected (runCached selected cached events)
      (runResident resident events) := by
  induction events generalizing cached resident with
  | nil => exact hequivalent
  | cons event rest ih =>
      apply ih
      exact event_preserves_equivalent selected cached resident event
        hequivalent

/-- Starting from a common result and external state, the final flush equals
the resident result after any admitted interleaving, and external state agrees. -/
theorem flush_after_interleaving_eq_resident (selected : Nat → Bool)
    (initial : ResultMem α) (external : σ) (events : List (Event α σ)) :
    Oak.LoopArrayHomes.flush selected
        (runCached selected (preloadWorld initial external) events).result =
      (runResident (residentWorld initial external) events).result ∧
    (runCached selected (preloadWorld initial external) events).external =
      (runResident (residentWorld initial external) events).external := by
  have hequivalent := run_preserves_equivalent selected
    (preloadWorld initial external) (residentWorld initial external) events
    (preload_equivalent selected initial external)
  exact hequivalent

end Oak.LoopResultHomes
