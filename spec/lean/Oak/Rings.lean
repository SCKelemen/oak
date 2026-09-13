import Oak.HappensBefore

/-! # Rings over caller-owned storage (`stdlib/rings.oak`, `65-machine-memory.md` §1)

The SPSC ring's positions are monotone counters: `head ≤ tail ≤ head + cap`,
the slot of position `p` is `p % cap`, and the buffer holds, at the slot of
every unconsumed position, the item pushed there. A push writes slot
`tail % cap`, which no unconsumed position occupies (`slots_distinct`), so
the invariant survives and a pop reads exactly the item pushed at `head`
(`pop_returns_pushed`): the ring is FIFO. The machine keeps the counters
in u32 and the capacity a power of two: the wrapping difference is the true
count (`wrapped_difference`) and the mask is the modulus (`mask_eq_mod`).

The memory-model facts are instances of `Oak.HappensBefore`: the producer's
payload write is sequenced before its release store of `tail`, the
consumer's acquire load of `tail` reads from it and is sequenced before the
payload read, so the write happens-before the read and the pair is no data
race — and symmetrically for the consumer's release of `head` before the
producer reuses the slot. The MPSC ring's producers claim positions with a
compare-exchange from `pos` to `pos + 1`; a trace of successful claims is
`0, 1, 2, …`, so claims are distinct (`claims_distinct`). -/

namespace Oak.Rings

/-- The abstract SPSC state: the counters, the capacity, the buffer by slot,
    and the log of pushed items by position. -/
structure Spsc (α : Type) where
  head : Nat
  tail : Nat
  cap : Nat
  buf : Nat → α
  pushed : Nat → α

/-- Well-formed: a positive capacity and at most `cap` unconsumed items. -/
def Spsc.WF (s : Spsc α) : Prop := 0 < s.cap ∧ s.head ≤ s.tail ∧ s.tail ≤ s.head + s.cap

/-- The buffer invariant: every unconsumed position's slot holds its item. -/
def Spsc.Inv (s : Spsc α) : Prop :=
  ∀ p, s.head ≤ p → p < s.tail → s.buf (p % s.cap) = s.pushed p

/-- A push when not full: write the slot, extend the log, advance `tail`. -/
def Spsc.push (s : Spsc α) (x : α) : Spsc α :=
  { s with
    tail := s.tail + 1
    buf := fun i => if i = s.tail % s.cap then x else s.buf i
    pushed := fun p => if p = s.tail then x else s.pushed p }

/-- A pop when not empty: advance `head`; the item is `buf (head % cap)`. -/
def Spsc.pop (s : Spsc α) : Spsc α := { s with head := s.head + 1 }

/-- Two positions less than `cap` apart occupy different slots. -/
theorem slots_distinct (cap p q : Nat) (hcap : 0 < cap) (hpq : p < q) (hwin : q < p + cap) :
    p % cap ≠ q % cap := by
  intro h
  have hzero : (q - p) % cap = 0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  have hlt : q - p < cap := by omega
  have hpos : 0 < q - p := by omega
  rw [Nat.mod_eq_of_lt hlt] at hzero
  omega

theorem push_wf (s : Spsc α) (x : α) (hwf : s.WF) (hnotfull : s.tail < s.head + s.cap) :
    (s.push x).WF := by
  obtain ⟨hcap, hht, _⟩ := hwf
  exact ⟨hcap, by simp [Spsc.push]; omega, by simp [Spsc.push]; omega⟩

theorem pop_wf (s : Spsc α) (hwf : s.WF) (hnotempty : s.head < s.tail) : s.pop.WF := by
  obtain ⟨hcap, _, hcapb⟩ := hwf
  exact ⟨hcap, by simp [Spsc.pop]; omega, by simp [Spsc.pop]; omega⟩

/-- The invariant survives a push into a ring that is not full: the new slot
    is not any unconsumed position's slot. -/
theorem push_inv (s : Spsc α) (x : α) (hwf : s.WF) (hnotfull : s.tail < s.head + s.cap)
    (hinv : s.Inv) : (s.push x).Inv := by
  obtain ⟨hcap, hht, _⟩ := hwf
  intro p hp hlt
  simp only [Spsc.push] at hp hlt ⊢
  by_cases hp' : p = s.tail
  · subst hp'
    simp
  · have hplt : p < s.tail := by omega
    have hne : p % s.cap ≠ s.tail % s.cap := slots_distinct s.cap p s.tail hcap hplt (by omega)
    rw [if_neg hne, if_neg hp']
    exact hinv p hp hplt

/-- The invariant survives a pop. -/
theorem pop_inv (s : Spsc α) (hinv : s.Inv) : s.pop.Inv := by
  intro p hp hlt
  simp only [Spsc.pop] at hp hlt
  exact hinv p (by omega) hlt

/-- A pop from a non-empty ring returns the item pushed at `head`: FIFO. -/
theorem pop_returns_pushed (s : Spsc α) (hinv : s.Inv) (hnotempty : s.head < s.tail) :
    s.buf (s.head % s.cap) = s.pushed s.head :=
  hinv s.head (Nat.le_refl _) hnotempty

/-- The count never exceeds the capacity. -/
theorem count_le_cap (s : Spsc α) (hwf : s.WF) : s.tail - s.head ≤ s.cap := by
  obtain ⟨_, _, h⟩ := hwf
  omega

/-- The machine's u32 counters wrap: the wrapping difference of the wrapped
    counters is the true count while the count is below 2^32 (it is at most
    the capacity, at most 2^31). -/
theorem wrapped_difference (tail head : Nat) (hle : head ≤ tail) (hwin : tail - head < 4294967296) :
    (tail % 4294967296 + 4294967296 - head % 4294967296) % 4294967296 = tail - head := by
  omega

/-- Masking with `cap - 1` is reduction modulo a power-of-two capacity. -/
theorem mask_eq_mod (p n : Nat) : p &&& (2 ^ n - 1) = p % 2 ^ n :=
  Nat.and_two_pow_sub_one_eq_mod p n

/-- A power of two above zero is a legal capacity for the mask. -/
theorem pow_two_cap_pos (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

section Publication

open Oak.HappensBefore

variable {Event : Type} {sb sw : Event → Event → Prop} {thread : Event → Nat}
  {conflict : Event → Event → Prop} {atomic : Event → Bool}

/-- SPSC, the handoff direction: the producer writes the slot (sequenced
    before its release store of `tail`), the consumer's acquire load of
    `tail` synchronizes with that store and is sequenced before its read of
    the slot; the write happens-before the read and cannot race with it. -/
theorem spsc_payload_race_free
    {slotWrite tailRelease tailAcquire slotRead : Event}
    (hWriteBeforeRelease : sb slotWrite tailRelease)
    (hSync : sw tailRelease tailAcquire)
    (hAcquireBeforeRead : sb tailAcquire slotRead) :
    HappensBefore sb sw slotWrite slotRead ∧
      ¬ DataRace (HappensBefore sb sw) thread conflict atomic slotWrite slotRead :=
  ⟨release_acquire_publication hWriteBeforeRelease hSync hAcquireBeforeRead,
    publication_excludes_data_race hWriteBeforeRelease hSync hAcquireBeforeRead⟩

/-- SPSC, the reuse direction: the consumer reads the slot (sequenced before
    its release store of `head`), the producer's acquire load of `head`
    synchronizes with it and is sequenced before the overwrite; the read
    happens-before the overwrite. -/
theorem spsc_reuse_race_free
    {slotRead headRelease headAcquire slotOverwrite : Event}
    (hReadBeforeRelease : sb slotRead headRelease)
    (hSync : sw headRelease headAcquire)
    (hAcquireBeforeWrite : sb headAcquire slotOverwrite) :
    HappensBefore sb sw slotRead slotOverwrite ∧
      ¬ DataRace (HappensBefore sb sw) thread conflict atomic slotRead slotOverwrite :=
  ⟨release_acquire_publication hReadBeforeRelease hSync hAcquireBeforeWrite,
    publication_excludes_data_race hReadBeforeRelease hSync hAcquireBeforeWrite⟩

/-- MPSC: a producer writes its slot, then releases the slot's sequence cell;
    the consumer acquires the sequence before reading the slot. -/
theorem mpsc_payload_race_free
    {slotWrite seqRelease seqAcquire slotRead : Event}
    (hWriteBeforeRelease : sb slotWrite seqRelease)
    (hSync : sw seqRelease seqAcquire)
    (hAcquireBeforeRead : sb seqAcquire slotRead) :
    HappensBefore sb sw slotWrite slotRead ∧
      ¬ DataRace (HappensBefore sb sw) thread conflict atomic slotWrite slotRead :=
  ⟨release_acquire_publication hWriteBeforeRelease hSync hAcquireBeforeRead,
    publication_excludes_data_race hWriteBeforeRelease hSync hAcquireBeforeRead⟩

end Publication

/-- A trace of successful claims on the MPSC `tail`: each compare-exchange
    succeeds only from the current value `pos` and leaves `pos + 1`, so the
    claims a trace hands out are consecutive from the initial position. -/
inductive ClaimTrace : Nat → List Nat → Nat → Prop
  | nil (pos : Nat) : ClaimTrace pos [] pos
  | claim {pos final : Nat} {rest : List Nat} (h : ClaimTrace (pos + 1) rest final) :
      ClaimTrace pos (pos :: rest) final

theorem claim_trace_range (pos : Nat) (claims : List Nat) (final : Nat)
    (h : ClaimTrace pos claims final) : claims = List.range' pos claims.length := by
  induction h with
  | nil pos => rfl
  | @claim pos final rest _ ih =>
    show pos :: rest = List.range' pos (rest.length + 1)
    rw [List.range'_succ]
    exact congrArg (pos :: ·) ih

/-- No two producers ever hold the same position. -/
theorem claims_distinct (pos : Nat) (claims : List Nat) (final : Nat)
    (h : ClaimTrace pos claims final) : claims.Nodup := by
  rw [claim_trace_range pos claims final h]
  exact List.nodup_range' (s := pos) (n := claims.length) (step := 1) (by decide)

/-- The trace ends `claims.length` positions on: every claim advanced `tail`
    by exactly one. -/
theorem claim_trace_final (pos : Nat) (claims : List Nat) (final : Nat)
    (h : ClaimTrace pos claims final) : final = pos + claims.length := by
  induction h with
  | nil pos => rfl
  | @claim pos final rest _ ih =>
    simp only [List.length_cons]
    omega

end Oak.Rings

/-! ## The intrusive MPSC and the MPMC ring

The intrusive queue's producers exchange `head`: each receives the link the
previous producer left and links its own node behind that one. A trace of
exchanges therefore threads the pushed nodes into one chain, in exchange
order (`exchange_chain`): the node a producer linked after is exactly the
node the previous exchange installed. Distinct nodes make a duplicate-free
chain (`chain_nodup`). The payload handoff is the same release/acquire
instance as the rings' (`intrusive_payload_race_free`), and the MPMC ring's
two claim counters are two `ClaimTrace`s. -/

namespace Oak.Rings

/-- A trace of exchanges on `head`: starting from the link `cur`, each push
    of node `n` receives `cur` and installs `n`; the list records the pairs
    (previous, pushed) in order, and `final` is the last link installed. -/
inductive ExchangeTrace : Nat → List (Nat × Nat) → Nat → Prop
  | nil (cur : Nat) : ExchangeTrace cur [] cur
  | push {cur final : Nat} {n : Nat} {rest : List (Nat × Nat)}
      (h : ExchangeTrace n rest final) : ExchangeTrace cur ((cur, n) :: rest) final

/-- Consecutive pushes chain: the previous link a push receives is the node
    the push before it installed. -/
theorem exchange_chain (cur final : Nat) (trace : List (Nat × Nat))
    (h : ExchangeTrace cur trace final) :
    ∀ (i : Nat) (hi : i + 1 < trace.length),
      (trace[i + 1]'hi).1 = (trace[i]'(Nat.lt_of_succ_lt hi)).2 := by
  induction h with
  | nil cur => intro i hi; simp at hi
  | @push cur final n rest h ih =>
    intro i hi
    cases i with
    | zero =>
      cases rest with
      | nil => simp at hi
      | cons p rest' =>
        cases h with
        | push _ => rfl
    | succ j =>
      exact ih j (by simpa using hi)

/-- The pushed nodes of a trace, in order. -/
def pushedNodes (trace : List (Nat × Nat)) : List Nat := trace.map Prod.snd

/-- Distinct nodes make a duplicate-free chain: the chain is the pushed list. -/
theorem chain_nodup (trace : List (Nat × Nat)) (h : (pushedNodes trace).Nodup) :
    (trace.map Prod.snd).Nodup := h

/-- The trace's final link is the last node pushed (or the start, when none). -/
theorem exchange_final (cur final : Nat) (trace : List (Nat × Nat))
    (h : ExchangeTrace cur trace final) :
    final = (pushedNodes trace).getLastD cur := by
  induction h with
  | nil cur => rfl
  | @push cur final n rest h ih =>
    cases rest with
    | nil => cases h; rfl
    | cons p rest' =>
      simp only [pushedNodes, List.map_cons, List.getLastD_cons] at ih ⊢
      exact ih

section IntrusivePublication

open Oak.HappensBefore

variable {Event : Type} {sb sw : Event → Event → Prop} {thread : Event → Nat}
  {conflict : Event → Event → Prop} {atomic : Event → Bool}

/-- The intrusive push: the caller's payload write is sequenced before the
    release store of the previous node's link; the consumer's acquire load
    of that link synchronizes with it and is sequenced before the payload
    read. -/
theorem intrusive_payload_race_free
    {payloadWrite linkRelease linkAcquire payloadRead : Event}
    (hWriteBeforeRelease : sb payloadWrite linkRelease)
    (hSync : sw linkRelease linkAcquire)
    (hAcquireBeforeRead : sb linkAcquire payloadRead) :
    HappensBefore sb sw payloadWrite payloadRead ∧
      ¬ DataRace (HappensBefore sb sw) thread conflict atomic payloadWrite payloadRead :=
  ⟨release_acquire_publication hWriteBeforeRelease hSync hAcquireBeforeRead,
    publication_excludes_data_race hWriteBeforeRelease hSync hAcquireBeforeRead⟩

end IntrusivePublication

/-- MPMC: the consumers' claims on `head` are a trace of their own, so two
    consumers never take the same position. -/
theorem mpmc_consumer_claims_distinct (pos : Nat) (claims : List Nat) (final : Nat)
    (h : ClaimTrace pos claims final) : claims.Nodup :=
  claims_distinct pos claims final h

end Oak.Rings
