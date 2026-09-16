import Oak.AArch64Memory

/-!
# AArch64 weak-memory projection

This module states the small application-level projection of Arm's official
`aarch64hwreqs.cat` / `aarch64.cat` model that Oak's scalar atomic mapping uses.
The names deliberately follow the CAT model:

* `bob` orders memory before a release write, an acquire read before following
  memory, a release write before a following acquire read, and memory accesses
  separated by a full DMB;
* external reads-from and coherence-after edges enter `obs`;
* `ob` contains those relations, is transitively closed, and is irreflexive.

The primitive execution below is deliberately smaller than the complete Arm
event structure.  `OrderedBefore` is the least transitive relation containing
the six scalar `bob` / `obs` edge classes used by Oak.  A separate structural
gate checks those constructors against the pinned CAT parser AST.  This is a
mechanically pinned projection, not a translation of the complete CAT model.
The theorems then prove the MP, SB, and IRIW outcomes on which Oak's AArch64 OS
profile relies.
-/

namespace Oak.AArch64WeakMemory

open Oak.MemoryOrder
open Oak.AArch64Memory

/-- The explicit scalar memory events needed by the litmus projection. -/
inductive Op where
  | load (loc : Nat)
  | store (loc : Nat)
  deriving DecidableEq, Repr

/-- Primitive event facts consumed by the restricted CAT projection.
    `releaseWrite` classifies `Exp & W & L`, `acquireRead` classifies the
    narrower `Exp & R & A` class Oak emits, and `coherenceAfter` is CAT's
    `ca` relation. -/
structure BaseExecution (Event : Type) where
  thread : Event → Nat
  po : Event → Event → Prop
  op : Event → Op
  releaseWrite : Event → Prop
  acquireRead : Event → Prop
  dmbFullBetween : Event → Event → Prop
  readsFrom : Event → Event → Prop
  coherenceAfter : Event → Event → Prop

/-- The least transitive relation containing the scalar edges certified from
    Arm's `bob` and `Exp-obs` definitions. -/
inductive OrderedBefore {Event : Type} (x : BaseExecution Event) : Event → Event → Prop where
  /-- `[Exp & M]; po; [Exp & W & L]` in `bob`. -/
  | bobBeforeRelease : ∀ a b, x.po a b → x.releaseWrite b → OrderedBefore x a b
  /-- `[(Exp & R & A) | (Exp & R & Q)]; po; [Exp & M]` in `bob`. -/
  | bobAfterAcquire : ∀ a b, x.acquireRead a → x.po a b → OrderedBefore x a b
  /-- `[Exp & W & L]; po; [Exp & R & A]` in `bob`. -/
  | bobReleaseAcquire : ∀ a b,
      x.releaseWrite a → x.acquireRead b → x.po a b → OrderedBefore x a b
  /-- `[Exp & M]; po; [dmb.full]; po; [Exp & M]` in `bob`. -/
  | bobFullDmb : ∀ a b, x.dmbFullBetween a b → OrderedBefore x a b
  /-- External reads-from is in `Exp-obs`, hence in `obs` and `ob`. -/
  | obsExternalReadsFrom : ∀ store load,
      x.readsFrom store load → x.thread store ≠ x.thread load →
      OrderedBefore x store load
  /-- External coherence-after is in `Exp-obs`, hence in `obs` and `ob`. -/
  | obsExternalCoherenceAfter : ∀ before after,
      x.coherenceAfter before after → x.thread before ≠ x.thread after →
      OrderedBefore x before after
  /-- The `ob; ob` arm makes ordered-before transitive. -/
  | trans : ∀ a b c,
      OrderedBefore x a b → OrderedBefore x b c → OrderedBefore x a c

/-- A valid execution satisfies Arm's external `irreflexive ob` requirement
    for the restricted ordered-before projection. -/
structure Execution (Event : Type) extends BaseExecution Event where
  obIrrefl : ∀ event, ¬ OrderedBefore toBaseExecution event event

abbrev Execution.ob {Event : Type} (x : Execution Event) : Event → Event → Prop :=
  OrderedBefore x.toBaseExecution

variable {Event : Type} (x : Execution Event)

/-- Release/acquire message passing orders the payload write before the
    consumer's payload read in Arm ordered-before. -/
theorem message_passing
    (payloadW flagW flagR payloadR : Event)
    (hPayloadFlag : x.po payloadW flagW)
    (hRelease : x.releaseWrite flagW)
    (hReads : x.readsFrom flagW flagR)
    (hExternal : x.thread flagW ≠ x.thread flagR)
    (hAcquire : x.acquireRead flagR)
    (hFlagPayload : x.po flagR payloadR) :
    x.ob payloadW payloadR := by
  have h₁ : x.ob payloadW flagW := .bobBeforeRelease _ _ hPayloadFlag hRelease
  have h₂ : x.ob flagW flagR := .obsExternalReadsFrom _ _ hReads hExternal
  have h₃ : x.ob flagR payloadR := .bobAfterAcquire _ _ hAcquire hFlagPayload
  exact .trans _ _ _ h₁ (.trans _ _ _ h₂ h₃)

/-- If the acquire observes the release flag, the later payload read cannot
    still observe the initial value: that would close an `ob` cycle. -/
theorem message_passing_forbids_stale_payload
    (payloadW flagW flagR payloadR : Event)
    (hPayloadFlag : x.po payloadW flagW)
    (hRelease : x.releaseWrite flagW)
    (hReads : x.readsFrom flagW flagR)
    (hExternal : x.thread flagW ≠ x.thread flagR)
    (hAcquire : x.acquireRead flagR)
    (hFlagPayload : x.po flagR payloadR)
    (hCoherenceAfter : x.coherenceAfter payloadR payloadW)
    (hPayloadExternal : x.thread payloadR ≠ x.thread payloadW) : False := by
  have hForward : x.ob payloadW payloadR :=
    message_passing x payloadW flagW flagR payloadR
      hPayloadFlag hRelease hReads hExternal hAcquire hFlagPayload
  have hBack : x.ob payloadR payloadW :=
    .obsExternalCoherenceAfter _ _ hCoherenceAfter hPayloadExternal
  exact x.obIrrefl payloadW (.trans _ _ _ hForward hBack)

/-- Oak seq-cst stores and loads map to STLR then LDAR.  Arm's release-to-
    acquire `bob` edge makes the store-buffering both-initial outcome cyclic. -/
theorem seqCst_store_buffering_forbidden
    (writeX readY writeY readX : Event)
    (hReleaseX : x.releaseWrite writeX)
    (hAcquireY : x.acquireRead readY)
    (hReleaseY : x.releaseWrite writeY)
    (hAcquireX : x.acquireRead readX)
    (hPo0 : x.po writeX readY)
    (hPo1 : x.po writeY readX)
    (hCoherenceY : x.coherenceAfter readY writeY)
    (hCoherenceX : x.coherenceAfter readX writeX)
    (hExternalY : x.thread readY ≠ x.thread writeY)
    (hExternalX : x.thread readX ≠ x.thread writeX) : False := by
  have h₁ : x.ob writeX readY :=
    .bobReleaseAcquire _ _ hReleaseX hAcquireY hPo0
  have h₂ : x.ob readY writeY :=
    .obsExternalCoherenceAfter _ _ hCoherenceY hExternalY
  have h₃ : x.ob writeY readX :=
    .bobReleaseAcquire _ _ hReleaseY hAcquireX hPo1
  have h₄ : x.ob readX writeX :=
    .obsExternalCoherenceAfter _ _ hCoherenceX hExternalX
  exact x.obIrrefl writeX
    (.trans _ _ _ h₁ (.trans _ _ _ h₂ (.trans _ _ _ h₃ h₄)))

/-- A full DMB between each store and load also excludes the store-buffering
    both-initial outcome.  This covers Oak's `atomic_fence_seq_cst` mapping. -/
theorem full_dmb_store_buffering_forbidden
    (writeX readY writeY readX : Event)
    (hDmb0 : x.dmbFullBetween writeX readY)
    (hDmb1 : x.dmbFullBetween writeY readX)
    (hCoherenceY : x.coherenceAfter readY writeY)
    (hCoherenceX : x.coherenceAfter readX writeX)
    (hExternalY : x.thread readY ≠ x.thread writeY)
    (hExternalX : x.thread readX ≠ x.thread writeX) : False := by
  have h₁ : x.ob writeX readY := .bobFullDmb _ _ hDmb0
  have h₂ : x.ob readY writeY :=
    .obsExternalCoherenceAfter _ _ hCoherenceY hExternalY
  have h₃ : x.ob writeY readX := .bobFullDmb _ _ hDmb1
  have h₄ : x.ob readX writeX :=
    .obsExternalCoherenceAfter _ _ hCoherenceX hExternalX
  exact x.obIrrefl writeX
    (.trans _ _ _ h₁ (.trans _ _ _ h₂ (.trans _ _ _ h₃ h₄)))

/-- Two seq-cst readers cannot observe two seq-cst writers in contradictory
    orders.  Each first LDAR orders the following LDAR; external reads-from and
    initial/coherence edges would otherwise form an `ob` cycle. -/
theorem seqCst_iriw_split_forbidden
    (writeX writeY readXOne readYZero readYOne readXZero : Event)
    (hReadXAcquire : x.acquireRead readXOne)
    (hReadYAcquire : x.acquireRead readYOne)
    (hPoXThenY : x.po readXOne readYZero)
    (hPoYThenX : x.po readYOne readXZero)
    (hReadsX : x.readsFrom writeX readXOne)
    (hReadsY : x.readsFrom writeY readYOne)
    (hExternalReadsX : x.thread writeX ≠ x.thread readXOne)
    (hExternalReadsY : x.thread writeY ≠ x.thread readYOne)
    (hCoherenceY : x.coherenceAfter readYZero writeY)
    (hCoherenceX : x.coherenceAfter readXZero writeX)
    (hExternalInitialY : x.thread readYZero ≠ x.thread writeY)
    (hExternalInitialX : x.thread readXZero ≠ x.thread writeX) : False := by
  have h₁ : x.ob writeX readXOne :=
    .obsExternalReadsFrom _ _ hReadsX hExternalReadsX
  have h₂ : x.ob readXOne readYZero :=
    .bobAfterAcquire _ _ hReadXAcquire hPoXThenY
  have h₃ : x.ob readYZero writeY :=
    .obsExternalCoherenceAfter _ _ hCoherenceY hExternalInitialY
  have h₄ : x.ob writeY readYOne :=
    .obsExternalReadsFrom _ _ hReadsY hExternalReadsY
  have h₅ : x.ob readYOne readXZero :=
    .bobAfterAcquire _ _ hReadYAcquire hPoYThenX
  have h₆ : x.ob readXZero writeX :=
    .obsExternalCoherenceAfter _ _ hCoherenceX hExternalInitialX
  exact x.obIrrefl writeX
    (.trans _ _ _ h₁
      (.trans _ _ _ h₂
        (.trans _ _ _ h₃
          (.trans _ _ _ h₄ (.trans _ _ _ h₅ h₆)))))

/-! The instruction selections that connect these projected theorems to Oak's
native AArch64 mapping. -/

theorem oak_release_acquire_pair_is_stlr_ldar :
    baselineStore .release = some .stlr ∧ baselineLoad .acquire = some .ldar := by
  exact ⟨rfl, rfl⟩

theorem oak_seqCst_pair_is_stlr_ldar :
    baselineStore .seqCst = some .stlr ∧ baselineLoad .seqCst = some .ldar := by
  exact ⟨rfl, rfl⟩

theorem oak_seqCst_fence_is_full_dmb :
    baselineFence .seqCst = some .dmbIsh := rfl

end Oak.AArch64WeakMemory
