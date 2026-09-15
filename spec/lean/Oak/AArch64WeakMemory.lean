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

The structure below exposes precisely those consequences as proof obligations.
It is not a mechanical translation of the CAT model.  The theorems then prove
the MP, SB, and IRIW outcomes on which Oak's AArch64 OS profile relies.
-/

namespace Oak.AArch64WeakMemory

open Oak.MemoryOrder
open Oak.AArch64Memory

/-- The explicit scalar memory events needed by the litmus projection. -/
inductive Op where
  | load (loc : Nat)
  | store (loc : Nat)
  deriving DecidableEq, Repr

/-- The relevant consequences of Arm's `bob`, `obs`, and `ob` relations.
    `releaseWrite` classifies STLR/release RMW writes and `acquireRead`
    classifies LDAR/acquire RMW reads. -/
structure Execution (Event : Type) where
  thread : Event → Nat
  po : Event → Event → Prop
  op : Event → Op
  releaseWrite : Event → Prop
  acquireRead : Event → Prop
  dmbFullBetween : Event → Event → Prop
  readsFrom : Event → Event → Prop
  readsInitial : Event → Prop
  ob : Event → Event → Prop
  ob_irrefl : ∀ event, ¬ ob event event
  ob_trans : ∀ a b c, ob a b → ob b c → ob a c
  /-- `[Exp & M]; po; [Exp & W & L]` in `bob`. -/
  bob_before_release : ∀ a b, po a b → releaseWrite b → ob a b
  /-- `[(Exp & R & A) | (Exp & R & Q)]; po; [Exp & M]` in `bob`. -/
  bob_after_acquire : ∀ a b, acquireRead a → po a b → ob a b
  /-- `[Exp & W & L]; po; [Exp & R & A]` in `bob`. -/
  bob_release_acquire : ∀ a b, releaseWrite a → acquireRead b → po a b → ob a b
  /-- `[Exp & M]; po; [dmb.full]; po; [Exp & M]` in `bob`. -/
  bob_full_dmb : ∀ a b, dmbFullBetween a b → ob a b
  /-- External reads-from is in `Exp-obs`, hence in `obs` and `ob`. -/
  obs_external_reads_from : ∀ store load,
    readsFrom store load → thread store ≠ thread load → ob store load
  /-- An initial read is coherence-before every external store to the same
      location (`fr`/`ca & ext`), hence the edge is in `obs` and `ob`. -/
  obs_initial_before_store : ∀ load store loc,
    readsInitial load → op load = .load loc → op store = .store loc →
    thread load ≠ thread store → ob load store

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
  have h₁ : x.ob payloadW flagW := x.bob_before_release _ _ hPayloadFlag hRelease
  have h₂ : x.ob flagW flagR := x.obs_external_reads_from _ _ hReads hExternal
  have h₃ : x.ob flagR payloadR := x.bob_after_acquire _ _ hAcquire hFlagPayload
  exact x.ob_trans _ _ _ h₁ (x.ob_trans _ _ _ h₂ h₃)

/-- If the acquire observes the release flag, the later payload read cannot
    still observe the initial value: that would close an `ob` cycle. -/
theorem message_passing_forbids_stale_payload
    (payloadW flagW flagR payloadR : Event)
    (hPayloadStore : x.op payloadW = .store 0)
    (hPayloadRead : x.op payloadR = .load 0)
    (hPayloadFlag : x.po payloadW flagW)
    (hRelease : x.releaseWrite flagW)
    (hReads : x.readsFrom flagW flagR)
    (hExternal : x.thread flagW ≠ x.thread flagR)
    (hAcquire : x.acquireRead flagR)
    (hFlagPayload : x.po flagR payloadR)
    (hInitial : x.readsInitial payloadR)
    (hPayloadExternal : x.thread payloadR ≠ x.thread payloadW) : False := by
  have hForward : x.ob payloadW payloadR :=
    message_passing x payloadW flagW flagR payloadR
      hPayloadFlag hRelease hReads hExternal hAcquire hFlagPayload
  have hBack : x.ob payloadR payloadW :=
    x.obs_initial_before_store _ _ 0 hInitial hPayloadRead hPayloadStore hPayloadExternal
  exact x.ob_irrefl payloadW (x.ob_trans _ _ _ hForward hBack)

/-- Oak seq-cst stores and loads map to STLR then LDAR.  Arm's release-to-
    acquire `bob` edge makes the store-buffering both-initial outcome cyclic. -/
theorem seqCst_store_buffering_forbidden
    (writeX readY writeY readX : Event)
    (hWriteX : x.op writeX = .store 0)
    (hReadY : x.op readY = .load 1)
    (hWriteY : x.op writeY = .store 1)
    (hReadX : x.op readX = .load 0)
    (hReleaseX : x.releaseWrite writeX)
    (hAcquireY : x.acquireRead readY)
    (hReleaseY : x.releaseWrite writeY)
    (hAcquireX : x.acquireRead readX)
    (hPo0 : x.po writeX readY)
    (hPo1 : x.po writeY readX)
    (hInitialY : x.readsInitial readY)
    (hInitialX : x.readsInitial readX)
    (hExternalY : x.thread readY ≠ x.thread writeY)
    (hExternalX : x.thread readX ≠ x.thread writeX) : False := by
  have h₁ : x.ob writeX readY :=
    x.bob_release_acquire _ _ hReleaseX hAcquireY hPo0
  have h₂ : x.ob readY writeY :=
    x.obs_initial_before_store _ _ 1 hInitialY hReadY hWriteY hExternalY
  have h₃ : x.ob writeY readX :=
    x.bob_release_acquire _ _ hReleaseY hAcquireX hPo1
  have h₄ : x.ob readX writeX :=
    x.obs_initial_before_store _ _ 0 hInitialX hReadX hWriteX hExternalX
  exact x.ob_irrefl writeX
    (x.ob_trans _ _ _ h₁ (x.ob_trans _ _ _ h₂ (x.ob_trans _ _ _ h₃ h₄)))

/-- A full DMB between each store and load also excludes the store-buffering
    both-initial outcome.  This covers Oak's `atomic_fence_seq_cst` mapping. -/
theorem full_dmb_store_buffering_forbidden
    (writeX readY writeY readX : Event)
    (hWriteX : x.op writeX = .store 0)
    (hReadY : x.op readY = .load 1)
    (hWriteY : x.op writeY = .store 1)
    (hReadX : x.op readX = .load 0)
    (hDmb0 : x.dmbFullBetween writeX readY)
    (hDmb1 : x.dmbFullBetween writeY readX)
    (hInitialY : x.readsInitial readY)
    (hInitialX : x.readsInitial readX)
    (hExternalY : x.thread readY ≠ x.thread writeY)
    (hExternalX : x.thread readX ≠ x.thread writeX) : False := by
  have h₁ : x.ob writeX readY := x.bob_full_dmb _ _ hDmb0
  have h₂ : x.ob readY writeY :=
    x.obs_initial_before_store _ _ 1 hInitialY hReadY hWriteY hExternalY
  have h₃ : x.ob writeY readX := x.bob_full_dmb _ _ hDmb1
  have h₄ : x.ob readX writeX :=
    x.obs_initial_before_store _ _ 0 hInitialX hReadX hWriteX hExternalX
  exact x.ob_irrefl writeX
    (x.ob_trans _ _ _ h₁ (x.ob_trans _ _ _ h₂ (x.ob_trans _ _ _ h₃ h₄)))

/-- Two seq-cst readers cannot observe two seq-cst writers in contradictory
    orders.  Each first LDAR orders the following LDAR; external reads-from and
    initial/coherence edges would otherwise form an `ob` cycle. -/
theorem seqCst_iriw_split_forbidden
    (writeX writeY readXOne readYZero readYOne readXZero : Event)
    (hWriteX : x.op writeX = .store 0)
    (hWriteY : x.op writeY = .store 1)
    (hReadYZero : x.op readYZero = .load 1)
    (hReadXZero : x.op readXZero = .load 0)
    (hReadXAcquire : x.acquireRead readXOne)
    (hReadYAcquire : x.acquireRead readYOne)
    (hPoXThenY : x.po readXOne readYZero)
    (hPoYThenX : x.po readYOne readXZero)
    (hReadsX : x.readsFrom writeX readXOne)
    (hReadsY : x.readsFrom writeY readYOne)
    (hExternalReadsX : x.thread writeX ≠ x.thread readXOne)
    (hExternalReadsY : x.thread writeY ≠ x.thread readYOne)
    (hInitialY : x.readsInitial readYZero)
    (hInitialX : x.readsInitial readXZero)
    (hExternalInitialY : x.thread readYZero ≠ x.thread writeY)
    (hExternalInitialX : x.thread readXZero ≠ x.thread writeX) : False := by
  have h₁ : x.ob writeX readXOne :=
    x.obs_external_reads_from _ _ hReadsX hExternalReadsX
  have h₂ : x.ob readXOne readYZero :=
    x.bob_after_acquire _ _ hReadXAcquire hPoXThenY
  have h₃ : x.ob readYZero writeY :=
    x.obs_initial_before_store _ _ 1 hInitialY hReadYZero hWriteY hExternalInitialY
  have h₄ : x.ob writeY readYOne :=
    x.obs_external_reads_from _ _ hReadsY hExternalReadsY
  have h₅ : x.ob readYOne readXZero :=
    x.bob_after_acquire _ _ hReadYAcquire hPoYThenX
  have h₆ : x.ob readXZero writeX :=
    x.obs_initial_before_store _ _ 0 hInitialX hReadXZero hWriteX hExternalInitialX
  exact x.ob_irrefl writeX
    (x.ob_trans _ _ _ h₁
      (x.ob_trans _ _ _ h₂
        (x.ob_trans _ _ _ h₃
          (x.ob_trans _ _ _ h₄ (x.ob_trans _ _ _ h₅ h₆)))))

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
