import MemoryBridge
import Std.Data.ExtDHashMap.Lemmas

/-!
# An independent Oak byte memory related to the generated RAM state

Unlike a byte view *defined from* Sail's memory, `Related` accepts an
independently supplied Oak memory. Every byte of the supplied physical span
must be present and equal, and the generated RAM-selector register must be
initialized. The relation is preserved by actual generated `__WriteMemory`
calls, individually and in source-list order.

The span and in-range indices are mathematical premises, not evidence of
allocation, ownership, virtual-to-physical translation, or source guards.
Values are already in the wrapper's little-endian byte order. This is not
dynamic STR execution, a native-verifier admission rule, or Arm concurrency.
Only the pinned Lean runtime is involved: its tags are Unit. We neither
erase Lem tags in a claimed refinement nor translate undefined Lem bits.
-/

namespace Oak.SailBridge.SequentialRAM.SpanState

abbrev Bytes := Nat → BitVec 8

/-- A supplied aligned physical span of 64-bit elements. The source-length
carrier is u32; the complete byte extent fits in the 52-bit physical range.
These conditions do not themselves authorize an access. -/
structure Span64 where
  base : BitVec 52
  length : BitVec 32
  aligned : base.toNat % 8 = 0
  bounded : base.toNat + length.toNat * 8 ≤ 2 ^ 52

def Contains (span : Span64) (address : Nat) : Prop :=
  span.base.toNat ≤ address ∧ address < span.base.toNat + span.length.toNat * 8

def elementAddress (span : Span64) (index : Fin span.length.toNat) : Nat :=
  span.base.toNat + index.val * 8

theorem element_bytes_inside (span : Span64) (index : Fin span.length.toNat)
    (offset : Fin 8) : Contains span (elementAddress span index + offset.val) := by
  have := index.isLt
  have := offset.isLt
  unfold Contains elementAddress
  omega

theorem element_address_aligned (span : Span64) (index : Fin span.length.toNat) :
    elementAddress span index % 8 = 0 := by
  simp [elementAddress, Nat.add_mod, span.aligned]

/-- Prove representability before constructing the 56-bit wrapper address;
no truncating conversion is used to justify a physical-address bound. -/
theorem element_address_bound (span : Span64) (index : Fin span.length.toNat) :
    elementAddress span index + 8 ≤ 2 ^ 52 := by
  have := index.isLt
  have := span.bounded
  unfold elementAddress
  omega

theorem element_address_roundtrip (span : Span64) (index : Fin span.length.toNat) :
    (BitVec.ofNat 56 (elementAddress span index)).toNat = elementAddress span index := by
  have := element_address_bound span index
  exact Nat.mod_eq_of_lt (by omega)

/-- Byte presence is mandatory; a fallback value never manufactures an
initialized byte. No agreement outside this span is required. -/
structure Related (span : Span64) (selector : BitVec 56) (oak : Bytes)
    (state : State) : Prop where
  initialized : state.regs.get? Register.__defaultRAM = some selector
  bytes : ∀ address, Contains span address → state.mem[address]? = some (oak address)

/-- All runtime fields except memory are unchanged, including any fields
added to the imported runtime in a future pinned revision. -/
def NonMemoryFrame (before after : State) : Prop :=
  after = { before with mem := after.mem }

theorem NonMemoryFrame.refl (state : State) : NonMemoryFrame state state := rfl

theorem NonMemoryFrame.trans {first second third : State}
    (left : NonMemoryFrame first second) (right : NonMemoryFrame second third) :
    NonMemoryFrame first third := by
  unfold NonMemoryFrame at *
  rw [right, left]

/-- The existing Oak store, not a new source-memory semantics. -/
def oakStore (span : Span64) (index : Fin span.length.toNat)
    (value : BitVec 64) (oak : Bytes) : Bytes :=
  Oak.SpanArguments.storeBytes oak (elementAddress span index) 8 value

/-- The original generated effect. The Fin argument is an external
in-range premise, not a claim that this wrapper checks Oak's bounds. -/
def writeElement (span : Span64) (index : Fin span.length.toNat)
    (value : BitVec 64) : SailM Unit :=
  Out.Functions.__WriteMemory 8 (BitVec.ofNat 56 (elementAddress span index)) value

theorem related_store (span : Span64) (selector : BitVec 56) (oak : Bytes)
    (state : State) (related : Related span selector oak state)
    (index : Fin span.length.toNat) (value : BitVec 64) :
    Related span selector (oakStore span index value oak)
      { state with mem := store64 state.mem (elementAddress span index) value } := by
  refine ⟨related.initialized, ?_⟩
  intro address inside
  change (store64 state.mem (elementAddress span index) value)[address]? = _
  rw [store64_lookup]
  unfold oakStore Oak.SpanArguments.storeBytes
  split
  · rfl
  · exact related.bytes address inside

/-- One actual successful generated call preserves the independently
supplied state relation and the exact partial-memory frame. -/
theorem writeElement_simulates (span : Span64) (selector : BitVec 56) (oak : Bytes)
    (state : State) (related : Related span selector oak state)
    (index : Fin span.length.toNat) (value : BitVec 64) :
    ∃ post : State,
      (writeElement span index value).run state = .ok () post ∧
      Related span selector (oakStore span index value oak) post ∧
      NonMemoryFrame state post ∧
      (∀ address, address < elementAddress span index ∨
        elementAddress span index + 8 ≤ address → post.mem[address]? = state.mem[address]?) := by
  refine ⟨{ state with mem := store64 state.mem (elementAddress span index) value },
    ?_, related_store span selector oak state related index value, rfl, ?_⟩
  · unfold writeElement
    rw [writeMemory64_initialized state selector _ value related.initialized,
      element_address_roundtrip]
  · exact store64_frame state.mem (elementAddress span index) value

abbrev Store (span : Span64) := Fin span.length.toNat × BitVec 64

/-- Ordered source stores; no commutation or overwritten-store erasure. -/
def oakStores (span : Span64) : List (Store span) → Bytes → Bytes
  | [], oak => oak
  | (index, value) :: rest, oak => oakStores span rest (oakStore span index value oak)

/-- A sequence of actual generated calls in exactly the same list order. -/
def writeElements (span : Span64) : List (Store span) → SailM Unit
  | [] => pure ()
  | (index, value) :: rest => do
    writeElement span index value
    writeElements span rest

/-- Sequential simulation for every finite list of in-range stores. The
frame preserves both values and absence outside the whole span. This is
not an event-trace or publication theorem: sequential final state alone
cannot distinguish an overwritten intermediate descriptor write. -/
theorem writeElements_simulates (span : Span64) (selector : BitVec 56)
    (stores : List (Store span)) (oak : Bytes) (state : State)
    (related : Related span selector oak state) :
    ∃ post : State,
      (writeElements span stores).run state = .ok () post ∧
      Related span selector (oakStores span stores oak) post ∧
      NonMemoryFrame state post ∧
      (∀ address, ¬ Contains span address → post.mem[address]? = state.mem[address]?) := by
  induction stores generalizing oak state with
  | nil => exact ⟨state, rfl, related, .refl state, fun _ _ => rfl⟩
  | cons store rest ih =>
    obtain ⟨middle, executed, relatedMiddle, frameMiddle, bytesMiddle⟩ :=
      writeElement_simulates span selector oak state related store.1 store.2
    obtain ⟨post, executedRest, relatedPost, framePost, bytesPost⟩ :=
      ih (oakStore span store.1 store.2 oak) middle relatedMiddle
    refine ⟨post, ?_, relatedPost, frameMiddle.trans framePost, ?_⟩
    · change (do writeElement span store.1 store.2; writeElements span rest).run state = _
      simp only [EStateM.run, Bind.bind, EStateM.bind] at executed executedRest ⊢
      rw [executed]
      exact executedRest
    · intro address outside
      rw [bytesPost address outside]
      apply bytesMiddle
      have := store.1.isLt
      unfold Contains elementAddress at *
      omega

/-- No relation can silently fill an absent byte, even if Oak reads zero. -/
theorem absent_byte_refuses (span : Span64) (selector : BitVec 56) (oak : Bytes)
    (state : State) (address : Nat) (inside : Contains span address)
    (absent : state.mem[address]? = none) : ¬ Related span selector oak state := by
  intro related
  have := related.bytes address inside
  rw [absent] at this
  contradiction

theorem wrong_byte_refuses (span : Span64) (selector : BitVec 56) (oak : Bytes)
    (state : State) (address : Nat) (inside : Contains span address)
    (value : BitVec 8) (present : state.mem[address]? = some value)
    (different : value ≠ oak address) : ¬ Related span selector oak state := by
  intro related
  have same := related.bytes address inside
  rw [present] at same
  exact different (Option.some.inj same)

/-- Missing selector initialization is excluded by the relation and is an
actual runtime error, not a successful store or an architectural Data Abort. -/
theorem missing_selector_refuses (span : Span64) (selector : BitVec 56) (oak : Bytes)
    (state : State) (missing : state.regs.get? Register.__defaultRAM = none)
    (index : Fin span.length.toNat) (value : BitVec 64) :
    ¬ Related span selector oak state ∧
      (writeElement span index value).run state = .error .Unreachable state := by
  constructor
  · intro related
    have := related.initialized
    rw [missing] at this
    contradiction
  · exact writeMemory64_uninitialized state _ value missing

namespace Examples

def pair : Span64 := ⟨4096#52, 2#32, by decide, by decide⟩
def lastPhysicalElement : Span64 := ⟨0xffffffffffff8#52, 1#32, by decide, by decide⟩
def empty : Span64 := ⟨0#52, 0#32, by decide, by decide⟩

example : elementAddress lastPhysicalElement ⟨0, by decide⟩ + 7 = 2 ^ 52 - 1 := by decide
example : (BitVec.ofNat 56 (elementAddress lastPhysicalElement ⟨0, by decide⟩)).toNat =
    2 ^ 52 - 8 := by decide

/-- The same last base cannot describe two physical elements. -/
example (span : Span64) (base : span.base = 0xffffffffffff8#52)
    (length : span.length = 2#32) : False := by
  have := span.bounded
  rw [base, length] at this
  contradiction

example (span : Span64) (base : span.base = 1#52) : False := by
  have := span.aligned
  rw [base] at this
  contradiction

example (index : Fin empty.length.toNat) : False := Fin.elim0 index
example : writeElements empty [] = pure () := rfl

def initializedState (mem : Memory) : State := {
  regs := (∅ : Std.ExtDHashMap Register RegisterType).insert Register.__defaultRAM (0x1234#56)
  choiceState := (), mem := mem, tags := (), cycleCount := 37, sailOutput := #["prior output"]
}

def initialPair : State := initializedState (store64 (store64 ∅ 4096 (0#64)) 4104 (0#64))

/-- Non-vacuity: independent all-zero Oak bytes agree with a concrete
initialized generated register state and two present eight-byte slots. -/
theorem initialPair_related : Related pair (0x1234#56) (fun _ => 0#8) initialPair := by
  constructor
  · simp [initialPair, initializedState]
  · intro address inside
    change (store64 (store64 ∅ 4096 (0#64)) 4104 (0#64))[address]? = _
    rw [store64_lookup]
    split
    · simp only [BitVec.extractLsb'_zero]
    · rw [store64_lookup]
      split
      · simp only [BitVec.extractLsb'_zero]
      · change 4096 ≤ address ∧ address < 4112 at inside
        omega

def writes : List (Store pair) :=
  [(⟨0, by decide⟩, 0x0123456789abcdef#64),
   (⟨1, by decide⟩, 0xffffffffffffffff#64),
   (⟨0, by decide⟩, 0#64)]

/-- Distinct slots, a repeated index, and nonzero high bytes exercise
ordered composition, frame preservation, and independence from default RAM
selector zero. The original output and cycle counter also survive. -/
theorem ordered_calls : ∃ post : State,
    (writeElements pair writes).run initialPair = .ok () post ∧
    post.mem[4096]? = some (0#8) ∧ post.mem[4111]? = some (255#8) ∧
    post.mem[4112]? = none ∧ post.cycleCount = 37 ∧ post.sailOutput = #["prior output"] := by
  obtain ⟨post, executed, related, frame, outside⟩ :=
    writeElements_simulates pair (0x1234#56) writes (fun _ => 0#8) initialPair initialPair_related
  refine ⟨post, executed, ?_, ?_, ?_, ?_, ?_⟩
  · have := related.bytes 4096 (by unfold Contains; decide)
    exact this
  · have := related.bytes 4111 (by unfold Contains; decide)
    exact this
  · rw [outside 4112 (by unfold Contains; decide)]
    simp [initialPair, initializedState, store64_lookup]
  · exact congrArg (fun s : State => s.cycleCount) frame
  · exact congrArg (fun s : State => s.sailOutput) frame

example : ¬ Related pair (0x1234#56) (fun _ => 0#8) (initializedState ∅) :=
  absent_byte_refuses pair _ _ _ 4096 (by unfold Contains; decide)
    (by simp [initializedState])

example : ¬ Related pair (0x1234#56) (fun _ => 1#8) initialPair :=
  wrong_byte_refuses pair _ _ _ 4096 (by unfold Contains; decide) (0#8)
    (by simp [initialPair, initializedState, store64_lookup]) (by decide)

example : ¬ Related pair (0#56) (fun _ => 0#8) initialPair := by
  intro related
  have := related.initialized
  simp [initialPair, initializedState] at this

/-- The bare runtime is *not* a bounds/ownership checker: an empty span
can be related while a raw generated call outside it still succeeds. The
Fin premise above must eventually come from the source/architectural path. -/
theorem raw_wrapper_has_no_span_guard :
    Related empty (0x1234#56) (fun _ => 0#8) (initializedState ∅) ∧
    (Out.Functions.__WriteMemory 8 (4096#56) (1#64)).run (initializedState ∅) =
      .ok () { initializedState ∅ with mem := store64 ∅ 4096 (1#64) } := by
  constructor
  · refine ⟨by simp [initializedState], ?_⟩
    intro address inside
    have : address < 0 := inside.2
    omega
  · exact writeMemory64_initialized (initializedState ∅) (0x1234#56) _ _
      (by simp [initializedState])

end Examples

/--
info: 'Oak.SailBridge.SequentialRAM.SpanState.writeElements_simulates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms writeElements_simulates

/--
info: 'Oak.SailBridge.SequentialRAM.SpanState.Examples.ordered_calls' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.ordered_calls

/--
info: 'Oak.SailBridge.SequentialRAM.SpanState.Examples.raw_wrapper_has_no_span_guard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.raw_wrapper_has_no_span_guard

end Oak.SailBridge.SequentialRAM.SpanState
