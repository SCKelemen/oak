import Oak.MemoryOrder

namespace Oak.HappensBefore

open Oak.MemoryOrder

universe u

/-- Release-like orders may publish a write to another thread. -/
def releaseLike : Order -> Bool
  | .release | .acqRel | .seqCst => true
  | _ => false

/-- Acquire-like orders may consume a published write from another thread. -/
def acquireLike : Order -> Bool
  | .acquire | .acqRel | .seqCst => true
  | _ => false

theorem release_is_releaseLike : releaseLike .release = true := rfl
theorem acqRel_is_releaseLike : releaseLike .acqRel = true := rfl
theorem seqCst_is_releaseLike : releaseLike .seqCst = true := rfl

theorem acquire_is_acquireLike : acquireLike .acquire = true := rfl
theorem acqRel_is_acquireLike : acquireLike .acqRel = true := rfl
theorem seqCst_is_acquireLike : acquireLike .seqCst = true := rfl

theorem relaxed_not_releaseLike : releaseLike .relaxed = false := rfl
theorem relaxed_not_acquireLike : acquireLike .relaxed = false := rfl

/-- A release sequence is its release head followed by zero or more contiguous
    RMW steps. `nextRmw a b` is the abstract proof that b is an RMW that reads
    from and immediately follows a in modification order. -/
inductive ReleaseSequence {Event : Type u}
    (nextRmw : Event -> Event -> Prop) (head : Event) : Event -> Prop where
  | head : ReleaseSequence nextRmw head head
  | step {previous member}
      (hPrevious : ReleaseSequence nextRmw head previous)
      (hNext : nextRmw previous member) :
      ReleaseSequence nextRmw head member

theorem release_sequence_contains_head
    {Event : Type u} {nextRmw : Event -> Event -> Prop} {head : Event} :
    ReleaseSequence nextRmw head head :=
  .head

theorem release_sequence_extends_by_rmw
    {Event : Type u} {nextRmw : Event -> Event -> Prop}
    {head previous member : Event}
    (hPrevious : ReleaseSequence nextRmw head previous)
    (hNext : nextRmw previous member) :
    ReleaseSequence nextRmw head member :=
  .step hPrevious hNext

/-- Explicit synchronization reasons. Keeping these constructors distinct makes
    the proof object retain the same causal provenance as Semantic IR. -/
inductive SynchronizesWith {Event : Type u}
    (sequencedBefore readsFrom nextRmw : Event -> Event -> Prop)
    (isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
      isAtomicWrite isAtomicRead : Event -> Prop) :
    Event -> Event -> Prop where
  | releaseAcquire {write read}
      (hRelease : isReleaseWrite write)
      (hAcquire : isAcquireRead read)
      (hReads : readsFrom write read) :
      SynchronizesWith sequencedBefore readsFrom nextRmw
        isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
        isAtomicWrite isAtomicRead write read
  | releaseSequenceAcquire {head member read}
      (hRelease : isReleaseWrite head)
      (hAcquire : isAcquireRead read)
      (hSequence : ReleaseSequence nextRmw head member)
      (hReads : readsFrom member read) :
      SynchronizesWith sequencedBefore readsFrom nextRmw
        isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
        isAtomicWrite isAtomicRead head read
  | releaseFenceAcquire {fence write read}
      (hFence : isReleaseFence fence)
      (hWrite : isAtomicWrite write)
      (hAcquire : isAcquireRead read)
      (hFenceBeforeWrite : sequencedBefore fence write)
      (hReads : readsFrom write read) :
      SynchronizesWith sequencedBefore readsFrom nextRmw
        isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
        isAtomicWrite isAtomicRead fence read
  | releaseAcquireFence {head member read fence}
      (hRelease : isReleaseWrite head)
      (hRead : isAtomicRead read)
      (hFence : isAcquireFence fence)
      (hSequence : ReleaseSequence nextRmw head member)
      (hReads : readsFrom member read)
      (hReadBeforeFence : sequencedBefore read fence) :
      SynchronizesWith sequencedBefore readsFrom nextRmw
        isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
        isAtomicWrite isAtomicRead head fence
  | releaseFenceAcquireFence {releaseFence write read acquireFence}
      (hReleaseFence : isReleaseFence releaseFence)
      (hWrite : isAtomicWrite write)
      (hRead : isAtomicRead read)
      (hAcquireFence : isAcquireFence acquireFence)
      (hReleaseBeforeWrite : sequencedBefore releaseFence write)
      (hReads : readsFrom write read)
      (hReadBeforeAcquire : sequencedBefore read acquireFence) :
      SynchronizesWith sequencedBefore readsFrom nextRmw
        isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
        isAtomicWrite isAtomicRead releaseFence acquireFence

/-- Oak happens-before is the transitive closure of per-thread
    sequenced-before and inter-thread synchronizes-with. -/
inductive HappensBefore {Event : Type u}
    (sequencedBefore synchronizesWith : Event -> Event -> Prop) :
    Event -> Event -> Prop where
  | base {a b}
      (h : sequencedBefore a b ∨ synchronizesWith a b) :
      HappensBefore sequencedBefore synchronizesWith a b
  | trans {a b c}
      (hab : HappensBefore sequencedBefore synchronizesWith a b)
      (hbc : HappensBefore sequencedBefore synchronizesWith b c) :
      HappensBefore sequencedBefore synchronizesWith a c

theorem sequencedBefore_implies_hb
    {Event : Type u} {sb sw : Event -> Event -> Prop} {a b : Event}
    (h : sb a b) : HappensBefore sb sw a b :=
  .base (Or.inl h)

theorem synchronizesWith_implies_hb
    {Event : Type u} {sb sw : Event -> Event -> Prop} {a b : Event}
    (h : sw a b) : HappensBefore sb sw a b :=
  .base (Or.inr h)

theorem hb_transitive
    {Event : Type u} {sb sw : Event -> Event -> Prop} {a b c : Event}
    (hab : HappensBefore sb sw a b)
    (hbc : HappensBefore sb sw b c) :
    HappensBefore sb sw a c :=
  .trans hab hbc

/-- The generic publication chain used by queues and message passing. -/
theorem release_acquire_publication
    {Event : Type u} {sb sw : Event -> Event -> Prop}
    {payloadWrite releaseWrite acquireRead payloadRead : Event}
    (hPayloadRelease : sb payloadWrite releaseWrite)
    (hPublication : sw releaseWrite acquireRead)
    (hAcquirePayload : sb acquireRead payloadRead) :
    HappensBefore sb sw payloadWrite payloadRead := by
  exact .trans
    (.base (Or.inl hPayloadRelease))
    (.trans
      (.base (Or.inr hPublication))
      (.base (Or.inl hAcquirePayload)))

/-- Reading any member of a release sequence with an acquire operation carries
    the release head's publication to subsequent payload reads. -/
theorem release_sequence_publication
    {Event : Type u}
    {sb rf nextRmw : Event -> Event -> Prop}
    {isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
      isAtomicWrite isAtomicRead : Event -> Prop}
    {payloadWrite head member acquireRead payloadRead : Event}
    (hPayloadHead : sb payloadWrite head)
    (hRelease : isReleaseWrite head)
    (hAcquire : isAcquireRead acquireRead)
    (hSequence : ReleaseSequence nextRmw head member)
    (hReads : rf member acquireRead)
    (hAcquirePayload : sb acquireRead payloadRead) :
    HappensBefore sb
      (SynchronizesWith sb rf nextRmw
        isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
        isAtomicWrite isAtomicRead)
      payloadWrite payloadRead := by
  apply release_acquire_publication hPayloadHead
  · exact SynchronizesWith.releaseSequenceAcquire
      hRelease hAcquire hSequence hReads
  · exact hAcquirePayload

/-- A release fence before an atomic write can publish through an acquire read
    that reads from that write. -/
theorem release_fence_publication
    {Event : Type u}
    {sb rf nextRmw : Event -> Event -> Prop}
    {isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
      isAtomicWrite isAtomicRead : Event -> Prop}
    {payloadWrite fence write acquireRead payloadRead : Event}
    (hPayloadFence : sb payloadWrite fence)
    (hFence : isReleaseFence fence)
    (hWrite : isAtomicWrite write)
    (hAcquire : isAcquireRead acquireRead)
    (hFenceWrite : sb fence write)
    (hReads : rf write acquireRead)
    (hAcquirePayload : sb acquireRead payloadRead) :
    HappensBefore sb
      (SynchronizesWith sb rf nextRmw
        isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
        isAtomicWrite isAtomicRead)
      payloadWrite payloadRead := by
  apply release_acquire_publication hPayloadFence
  · exact SynchronizesWith.releaseFenceAcquire
      hFence hWrite hAcquire hFenceWrite hReads
  · exact hAcquirePayload

/-- A release fence and acquire fence can form the publication edge when an
    intervening atomic read observes an atomic write sequenced after release. -/
theorem fence_fence_publication
    {Event : Type u}
    {sb rf nextRmw : Event -> Event -> Prop}
    {isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
      isAtomicWrite isAtomicRead : Event -> Prop}
    {payloadWrite releaseFence write read acquireFence payloadRead : Event}
    (hPayloadRelease : sb payloadWrite releaseFence)
    (hReleaseFence : isReleaseFence releaseFence)
    (hWrite : isAtomicWrite write)
    (hRead : isAtomicRead read)
    (hAcquireFence : isAcquireFence acquireFence)
    (hReleaseWrite : sb releaseFence write)
    (hReads : rf write read)
    (hReadAcquire : sb read acquireFence)
    (hAcquirePayload : sb acquireFence payloadRead) :
    HappensBefore sb
      (SynchronizesWith sb rf nextRmw
        isReleaseWrite isAcquireRead isReleaseFence isAcquireFence
        isAtomicWrite isAtomicRead)
      payloadWrite payloadRead := by
  apply release_acquire_publication hPayloadRelease
  · exact SynchronizesWith.releaseFenceAcquireFence
      hReleaseFence hWrite hRead hAcquireFence
      hReleaseWrite hReads hReadAcquire
  · exact hAcquirePayload

/-- Abstract language-level data-race predicate. At least one conflicting
    access is non-atomic and neither access happens-before the other. -/
def DataRace {Event : Type u}
    (hb : Event -> Event -> Prop)
    (thread : Event -> Nat)
    (conflict : Event -> Event -> Prop)
    (atomic : Event -> Bool)
    (a b : Event) : Prop :=
  thread a ≠ thread b ∧
  conflict a b ∧
  (atomic a = false ∨ atomic b = false) ∧
  ¬ hb a b ∧
  ¬ hb b a

/-- Any established happens-before edge excludes a data race in that pair. -/
theorem hb_excludes_data_race
    {Event : Type u}
    {hb : Event -> Event -> Prop}
    {thread : Event -> Nat}
    {conflict : Event -> Event -> Prop}
    {atomic : Event -> Bool}
    {a b : Event}
    (hab : hb a b) :
    ¬ DataRace hb thread conflict atomic a b := by
  intro race
  rcases race with ⟨_, _, _, hNotAB, _⟩
  exact hNotAB hab

/-- Therefore a correctly published payload cannot constitute a data race
    between the publishing write and consuming read. -/
theorem publication_excludes_data_race
    {Event : Type u} {sb sw : Event -> Event -> Prop}
    {thread : Event -> Nat}
    {conflict : Event -> Event -> Prop}
    {atomic : Event -> Bool}
    {payloadWrite releaseWrite acquireRead payloadRead : Event}
    (hPayloadRelease : sb payloadWrite releaseWrite)
    (hPublication : sw releaseWrite acquireRead)
    (hAcquirePayload : sb acquireRead payloadRead) :
    ¬ DataRace (HappensBefore sb sw) thread conflict atomic
        payloadWrite payloadRead := by
  apply hb_excludes_data_race
  exact release_acquire_publication
    hPayloadRelease hPublication hAcquirePayload

end Oak.HappensBefore
