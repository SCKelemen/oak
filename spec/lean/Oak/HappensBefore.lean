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

/-- The publication chain used by queues and message passing:

      payload write
          sb
      release publication
          sw
      acquire consumption
          sb
      payload read

    establishes happens-before from payload write to payload read. -/
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
