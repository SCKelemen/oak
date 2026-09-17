import Bridge
import Oak.SpanArguments
import Std.Data.ExtHashMap.Lemmas

/-!
# The no-device RAM wrapper in Sail's sequential Lean runtime

Unlike the pure request projections, this module evaluates the generated
`__WriteRAM` effect against the actual imported `PreSail.write_ram` runtime.
The register-reading `__WriteMemory` wrapper is also generated unchanged,
including the no-device trace helper. Its success requires a populated
`__defaultRAM` entry in the actual generated register state.
`SpanRefinement` connects this byte update to Oak's existing span store
model, preserving byte presence separately from a total observation.
The footprint is a sequential byte-map update, not an Arm/CAT event, an
atomicity claim, or a proof of the C runtime. Reaching this wrapper from STR
still requires the external alignment/translation/fault/MMIO premises.
-/

namespace Oak.SailBridge.SequentialRAM

abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource
abbrev Memory := Std.ExtHashMap Nat (BitVec 8)

/-- Eight byte updates at mathematical addresses. The runtime places the
least-significant byte first; Arm's endian conversion happens before this
boundary. These inserts do not represent eight architectural events. -/
def store64 (mem : Memory) (address : Nat) (data : BitVec 64) : Memory :=
  let mem := mem.insert address (data.extractLsb' 0 8)
  let mem := mem.insert (address + 1) (data.extractLsb' 8 8)
  let mem := mem.insert (address + 2) (data.extractLsb' 16 8)
  let mem := mem.insert (address + 3) (data.extractLsb' 24 8)
  let mem := mem.insert (address + 4) (data.extractLsb' 32 8)
  let mem := mem.insert (address + 5) (data.extractLsb' 40 8)
  let mem := mem.insert (address + 6) (data.extractLsb' 48 8)
  mem.insert (address + 7) (data.extractLsb' 56 8)

/-- The copied and mechanically generated Arm wrapper returns normally in
the sequential runtime, changing only the eight specified memory bytes.
This is not a proof that a dynamic architectural instruction reaches it. -/
theorem writeRAM64_run (state : State) (defaultRAM address : BitVec 56)
    (data : BitVec 64) :
    (Out.Functions.__WriteRAM 56 8 defaultRAM address data).run state =
      .ok () { state with mem := store64 state.mem address.toNat data } := by
  rfl

theorem store64_byte (mem : Memory) (address : Nat) (data : BitVec 64)
    (index : Fin 8) :
    (store64 mem address data)[address + index.val]? =
      some (data.extractLsb' (8 * index.val) 8) := by
  have h := index.isLt
  have cases : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨
      index.val = 3 ∨ index.val = 4 ∨ index.val = 5 ∨
      index.val = 6 ∨ index.val = 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h <;>
    simp only [store64, Std.ExtHashMap.getElem?_insert] <;> simp [h]

theorem store64_frame (mem : Memory) (address : Nat) (data : BitVec 64)
    (other : Nat) (outside : other < address ∨ address + 8 ≤ other) :
    (store64 mem address data)[other]? = mem[other]? := by
  have ne (i : Nat) (hi : i < 8) : (address + i == other) = false := by
    simp only [beq_eq_false_iff_ne]
    omega
  have ne0 : address ≠ other := by omega
  simp [store64, Std.ExtHashMap.getElem?_insert, ne0,
    ne 1 (by decide), ne 2 (by decide), ne 3 (by decide),
    ne 4 (by decide), ne 5 (by decide), ne 6 (by decide), ne 7 (by decide)]

/-- Exact optional lookup, including absence outside the written range. -/
theorem store64_lookup (mem : Memory) (address : Nat) (data : BitVec 64)
    (other : Nat) :
    (store64 mem address data)[other]? =
      if address ≤ other ∧ other < address + 8 then
        some (data.extractLsb' (8 * (other - address)) 8)
      else mem[other]? := by
  by_cases inside : address ≤ other ∧ other < address + 8
  · rw [if_pos inside]
    have hi : other - address < 8 := by omega
    simpa only [Nat.add_sub_of_le inside.1] using
      store64_byte mem address data ⟨other - address, hi⟩
  · rw [if_neg inside]
    exact store64_frame mem address data other (by omega)

/-- A complete sequential-state footprint for the generated wrapper. The
state equality in `writeRAM64_run` also rules out any exceptional result. -/
theorem writeRAM64_footprint (state : State) (defaultRAM address : BitVec 56)
    (data : BitVec 64) :
    ∃ post : State,
      (Out.Functions.__WriteRAM 56 8 defaultRAM address data).run state = .ok () post ∧
      (∀ i : Fin 8, post.mem[address.toNat + i.val]? =
        some (data.extractLsb' (8 * i.val) 8)) ∧
      (∀ other, other < address.toNat ∨ address.toNat + 8 ≤ other →
        post.mem[other]? = state.mem[other]?) ∧
      post.regs = state.regs ∧ post.choiceState = state.choiceState ∧
      post.tags = state.tags ∧ post.cycleCount = state.cycleCount ∧
      post.sailOutput = state.sailOutput := by
  refine ⟨{ state with mem := store64 state.mem address.toNat data },
    writeRAM64_run state defaultRAM address data, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · exact store64_byte state.mem address.toNat data
  · exact store64_frame state.mem address.toNat data

/-- This runtime ignores the RAM selector; its byte map cannot establish
RAM-namespace provenance or storage custody. -/
theorem writeRAM64_defaultRAM_irrelevant (state : State)
    (ram1 ram2 address : BitVec 56) (data : BitVec 64) :
    (Out.Functions.__WriteRAM 56 8 ram1 address data).run state =
      (Out.Functions.__WriteRAM 56 8 ram2 address data).run state := by
  rw [writeRAM64_run, writeRAM64_run]

/-- The same runtime rule holds with arbitrary register and choice-state
types, not only the generated fragment's single RAM-selector register. -/
theorem runtime_writeRAM64_run {Reg : Type} {RegType : Reg → Type}
    [DecidableEq Reg] [Hashable Reg] {choice : Sail.ChoiceSource} {exception : Type}
    (state : PreSail.SequentialState RegType choice)
    (defaultRAM address : BitVec 56) (data : BitVec 64) :
    (PreSail.write_ram 56 8 defaultRAM address data :
      PreSail.PreSailM RegType choice exception Unit).run state =
      .ok () { state with mem := store64 state.mem address.toNat data } := by
  rfl

/-- Compose the previously proved argument route with the generated
effectful wrapper. PA and endian selection are still supplied externally. -/
theorem aligned_normal_writeRAM64_run (state : State)
    (defaultRAM : BitVec 56) (bigEndian : Bool) (pa : BitVec 52)
    (preMemData : BitVec 64) :
    let args := Out.Functions.str64_aligned_normal_write_memory_arguments_pure
      bigEndian pa preMemData
    (Out.Functions.__WriteRAM 56 8 defaultRAM args.1 args.2).run state =
      .ok () { state with
        mem := store64 state.mem pa.toNat
          (if bigEndian then Oak.ArmASL.bigEndianReverse64 preMemData else preMemData) } := by
  dsimp only
  rw [writeRAM64_run, A64Encoding.str64_aligned_normal_write_memory_arguments_bridge]
  have hpa : pa.toNat < 2 ^ 56 := by have := pa.isLt; omega
  simp only [Oak.ArmASL.str64AlignedNormalWriteMemoryArguments,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpa]

/-- Break's selected zero data produces eight zero bytes under either
endian. This composes projections with an effect, not a dynamic STR trace. -/
theorem str_xzr_x0_selected_writeRAM_run (state : State)
    (defaultRAM : BitVec 56) (bigEndian : Bool) (pa : BitVec 52)
    (x0 discardedRtValue sp : BitVec 64) :
    let args := Out.Functions.str64_aligned_normal_write_memory_arguments_pure
      bigEndian pa (Out.Functions.str64_unsigned_store_request_pure
        0b11111#5 0#5 0#12 x0 discardedRtValue sp).2
    (Out.Functions.__WriteRAM 56 8 defaultRAM args.1 args.2).run state =
      .ok () { state with mem := store64 state.mem pa.toNat (0#64) } := by
  dsimp only
  rw [aligned_normal_writeRAM64_run, A64Encoding.str_xzr_x0_store_request]
  have zeroEndian : Oak.ArmASL.bigEndianReverse64 (0#64) = 0#64 := by decide
  cases bigEndian <;> simp [zeroEndian]

/-- Make retains the exact endian-transformed X2 data at the selected
effect boundary. PA, route reachability and event identity remain external. -/
theorem str_x2_x0_selected_writeRAM_run (state : State)
    (defaultRAM : BitVec 56) (bigEndian : Bool) (pa : BitVec 52)
    (x0 x2 sp : BitVec 64) :
    let args := Out.Functions.str64_aligned_normal_write_memory_arguments_pure
      bigEndian pa (Out.Functions.str64_unsigned_store_request_pure
        2#5 0#5 0#12 x0 x2 sp).2
    (Out.Functions.__WriteRAM 56 8 defaultRAM args.1 args.2).run state =
      .ok () { state with
        mem := store64 state.mem pa.toNat
          (if bigEndian then Oak.ArmASL.bigEndianReverse64 x2 else x2) } := by
  dsimp only
  rw [aligned_normal_writeRAM64_run, A64Encoding.str_x2_x0_store_request]

theorem physical_write64_no_address_wrap (pa : BitVec 52) :
    pa.toNat + 7 < 2 ^ 56 := by
  have := pa.isLt
  omega

/-- Exact execution of the generated register-reading wrapper. A missing
selector causes Sail's runtime initialization error before any write; it is
not an architectural Data Abort or a statement about address translation. -/
theorem writeMemory64_run (state : State) (address : BitVec 56) (data : BitVec 64) :
    (Out.Functions.__WriteMemory 8 address data).run state =
      match state.regs.get? Register.__defaultRAM with
      | none => .error .Unreachable state
      | some _ => .ok () { state with mem := store64 state.mem address.toNat data } := by
  cases h : state.regs.get? Register.__defaultRAM <;>
    simp only [Out.Functions.__WriteMemory, PreSail.readReg, EStateM.run,
      Bind.bind, Pure.pure, MonadState.get, getThe, MonadStateOf.get,
      MonadExcept.throw, throwThe, MonadExceptOf.throw,
      EStateM.bind, EStateM.pure, EStateM.get, EStateM.throw, h] <;> rfl

theorem writeMemory64_initialized (state : State)
    (defaultRAM address : BitVec 56) (data : BitVec 64)
    (initialized : state.regs.get? Register.__defaultRAM = some defaultRAM) :
    (Out.Functions.__WriteMemory 8 address data).run state =
      .ok () { state with mem := store64 state.mem address.toNat data } := by
  rw [writeMemory64_run, initialized]

theorem writeMemory64_uninitialized (state : State)
    (address : BitVec 56) (data : BitVec 64)
    (missing : state.regs.get? Register.__defaultRAM = none) :
    (Out.Functions.__WriteMemory 8 address data).run state = .error .Unreachable state := by
  rw [writeMemory64_run, missing]

/-- A successful call cannot be manufactured by omitting initialization,
even though the lower `write_ram` runtime ignores the selector's value. -/
theorem writeMemory64_success_iff_initialized (state : State)
    (address : BitVec 56) (data : BitVec 64) :
    (∃ post, (Out.Functions.__WriteMemory 8 address data).run state = .ok () post) ↔
      ∃ defaultRAM, state.regs.get? Register.__defaultRAM = some defaultRAM := by
  rw [writeMemory64_run]
  cases h : state.regs.get? Register.__defaultRAM <;> simp

/-- The generated wrapper reaches the lower effect with the register's
actual value. The initialized entry is evidence from this state, not a flag
asserting that a dynamic STR's route checks passed. -/
theorem writeMemory64_eq_writeRAM_of_initialized (state : State)
    (defaultRAM address : BitVec 56) (data : BitVec 64)
    (initialized : state.regs.get? Register.__defaultRAM = some defaultRAM) :
    (Out.Functions.__WriteMemory 8 address data).run state =
      (Out.Functions.__WriteRAM 56 8 defaultRAM address data).run state := by
  rw [writeMemory64_initialized state defaultRAM address data initialized, writeRAM64_run]

theorem writeMemory64_footprint (state : State) (defaultRAM address : BitVec 56)
    (data : BitVec 64)
    (initialized : state.regs.get? Register.__defaultRAM = some defaultRAM) :
    ∃ post : State,
      (Out.Functions.__WriteMemory 8 address data).run state = .ok () post ∧
      (∀ i : Fin 8, post.mem[address.toNat + i.val]? =
        some (data.extractLsb' (8 * i.val) 8)) ∧
      (∀ other, other < address.toNat ∨ address.toNat + 8 ≤ other →
        post.mem[other]? = state.mem[other]?) ∧
      post.regs = state.regs ∧ post.choiceState = state.choiceState ∧
      post.tags = state.tags ∧ post.cycleCount = state.cycleCount ∧
      post.sailOutput = state.sailOutput := by
  rw [writeMemory64_eq_writeRAM_of_initialized state defaultRAM address data initialized]
  exact writeRAM64_footprint state defaultRAM address data

/-- The selected break arguments now compose with the register-reading
wrapper as well. Reaching __WriteMemory from STR is still external. -/
theorem str_xzr_x0_selected_writeMemory_run (state : State)
    (defaultRAM : BitVec 56) (bigEndian : Bool) (pa : BitVec 52)
    (x0 discardedRtValue sp : BitVec 64)
    (initialized : state.regs.get? Register.__defaultRAM = some defaultRAM) :
    let args := Out.Functions.str64_aligned_normal_write_memory_arguments_pure
      bigEndian pa (Out.Functions.str64_unsigned_store_request_pure
        0b11111#5 0#5 0#12 x0 discardedRtValue sp).2
    (Out.Functions.__WriteMemory 8 args.1 args.2).run state =
      .ok () { state with mem := store64 state.mem pa.toNat (0#64) } := by
  dsimp only
  rw [writeMemory64_eq_writeRAM_of_initialized state defaultRAM _ _ initialized]
  exact str_xzr_x0_selected_writeRAM_run state defaultRAM bigEndian pa x0 discardedRtValue sp

theorem str_x2_x0_selected_writeMemory_run (state : State)
    (defaultRAM : BitVec 56) (bigEndian : Bool) (pa : BitVec 52)
    (x0 x2 sp : BitVec 64)
    (initialized : state.regs.get? Register.__defaultRAM = some defaultRAM) :
    let args := Out.Functions.str64_aligned_normal_write_memory_arguments_pure
      bigEndian pa (Out.Functions.str64_unsigned_store_request_pure
        2#5 0#5 0#12 x0 x2 sp).2
    (Out.Functions.__WriteMemory 8 args.1 args.2).run state =
      .ok () { state with
        mem := store64 state.mem pa.toNat
          (if bigEndian then Oak.ArmASL.bigEndianReverse64 x2 else x2) } := by
  dsimp only
  rw [writeMemory64_eq_writeRAM_of_initialized state defaultRAM _ _ initialized]
  exact str_x2_x0_selected_writeRAM_run state defaultRAM bigEndian pa x0 x2 sp

namespace SpanRefinement

/-- A total *observation* of Sail's partial byte map. The fallback is
arbitrary and is not an initialized-byte, address-validity or ownership
certificate. In particular, equality of views cannot establish presence. -/
def byteView (mem : Memory) (fallback : Nat → BitVec 8) : Nat → BitVec 8 :=
  fun address => (mem[address]?).getD (fallback address)

/-- Presence in the sequential runtime's map, not allocation or access
authority. Keep this separate from the total Oak byte observation. -/
def bytePresent (mem : Memory) (address : Nat) : Prop :=
  ∃ value, mem[address]? = some value

theorem store64_presence (mem : Memory) (address other : Nat) (data : BitVec 64) :
    bytePresent (store64 mem address data) other ↔
      (address ≤ other ∧ other < address + 8) ∨ bytePresent mem other := by
  unfold bytePresent
  rw [store64_lookup]
  by_cases inside : address ≤ other ∧ other < address + 8 <;> simp [inside]

/-- The concrete Sail store and Oak's existing owned-array/span byte store
commute with the byte observation, for every fallback and every prior map.
The shift/truncate on the Oak side equals the runtime's byte extraction. -/
theorem store64_refines_span_store (mem : Memory) (fallback : Nat → BitVec 8)
    (address : Nat) (data : BitVec 64) :
    byteView (store64 mem address data) fallback =
      Oak.SpanArguments.storeBytes (byteView mem fallback) address 8 data := by
  funext other
  unfold byteView Oak.SpanArguments.storeBytes
  rw [store64_lookup]
  split <;> rfl

/-- Lift the byte-model refinement to an actual generated wrapper result,
retaining the state-indexed RAM-selector initialization requirement. -/
theorem writeMemory64_refines_span_store (state : State)
    (defaultRAM address : BitVec 56) (data : BitVec 64)
    (fallback : Nat → BitVec 8)
    (initialized : state.regs.get? Register.__defaultRAM = some defaultRAM) :
    ∃ post : State,
      (Out.Functions.__WriteMemory 8 address data).run state = .ok () post ∧
      byteView post.mem fallback =
        Oak.SpanArguments.storeBytes (byteView state.mem fallback) address.toNat 8 data ∧
      (∀ other, bytePresent post.mem other ↔
        (address.toNat ≤ other ∧ other < address.toNat + 8) ∨ bytePresent state.mem other) ∧
      post.regs = state.regs ∧ post.choiceState = state.choiceState ∧
      post.tags = state.tags ∧ post.cycleCount = state.cycleCount ∧
      post.sailOutput = state.sailOutput := by
  refine ⟨{ state with mem := store64 state.mem address.toNat data },
    writeMemory64_initialized state defaultRAM address data initialized,
    store64_refines_span_store state.mem fallback address.toNat data,
    ?_, rfl, rfl, rfl, rfl, rfl⟩
  intro other
  exact store64_presence state.mem address.toNat other data

/-- Preserve the official pre-call endian selection when connecting the
generated effect to the Oak byte store. Translation/reachability is still
external: `pa` and `bigEndian` are inputs, not inferred from the source. -/
theorem aligned_writeMemory64_refines_span_store (state : State)
    (defaultRAM : BitVec 56) (bigEndian : Bool) (pa : BitVec 52)
    (preMemData : BitVec 64) (fallback : Nat → BitVec 8)
    (initialized : state.regs.get? Register.__defaultRAM = some defaultRAM) :
    let args := Out.Functions.str64_aligned_normal_write_memory_arguments_pure
      bigEndian pa preMemData
    ∃ post : State,
      (Out.Functions.__WriteMemory 8 args.1 args.2).run state = .ok () post ∧
      byteView post.mem fallback =
        Oak.SpanArguments.storeBytes (byteView state.mem fallback) pa.toNat 8
          (if bigEndian then Oak.ArmASL.bigEndianReverse64 preMemData else preMemData) := by
  dsimp only
  refine ⟨{ state with
    mem := store64 state.mem pa.toNat
      (if bigEndian then Oak.ArmASL.bigEndianReverse64 preMemData else preMemData) }, ?_, ?_⟩
  · rw [writeMemory64_eq_writeRAM_of_initialized state defaultRAM _ _ initialized]
    exact aligned_normal_writeRAM64_run state defaultRAM bigEndian pa preMemData
  · exact store64_refines_span_store state.mem fallback pa.toNat _

/-- Transport the existing Oak disjoint-element law, without claiming that
these mathematical array slots have been allocated or translated. -/
theorem distinct_element_bytes_survive (mem : Memory) (fallback : Nat → BitVec 8)
    (base i j k : Nat) (first second : BitVec 64) (distinct : i ≠ j) (hk : k < 8) :
    byteView (store64 (store64 mem (base + i * 8) first) (base + j * 8) second)
        fallback (base + i * 8 + k) = (first >>> (8 * k)).truncate 8 := by
  rw [store64_refines_span_store, store64_refines_span_store]
  exact Oak.SpanArguments.two_writes_commute_on_first
    (byteView mem fallback) base i j 8 first second distinct k hk

/-- Keeping both the byte observation and presence is lossless for the
partial map. Observation equality alone, below, is intentionally weaker. -/
theorem eq_of_view_and_presence (left right : Memory) (fallback : Nat → BitVec 8)
    (values : byteView left fallback = byteView right fallback)
    (presence : ∀ address, bytePresent left address ↔ bytePresent right address) :
    left = right := by
  apply Std.ExtHashMap.ext_getElem?
  intro address
  have hv := congrFun values address
  have hp := presence address
  unfold byteView at hv
  unfold bytePresent at hp
  cases hl : left[address]? <;> cases hr : right[address]? <;> simp_all

/-- Regression: absent bytes and explicitly present zero bytes can have
identical total views. Do not infer address validity from the fallback. -/
theorem total_view_can_hide_absence (address : Nat) :
    byteView (∅ : Memory) (fun _ => 0#8) =
        byteView ((∅ : Memory).insert address (0#8)) (fun _ => 0#8) ∧
      ¬ bytePresent (∅ : Memory) address ∧
      bytePresent ((∅ : Memory).insert address (0#8)) address := by
  constructor
  · funext other
    simp only [byteView, Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_empty]
    split <;> rfl
  · simp [bytePresent]

/-- Disjoint byte footprints suffice for sequential map commutation.
This is not an Arm event-order or publication-reordering theorem. -/
theorem disjoint_store64_commute (mem : Memory) (a b : Nat) (first second : BitVec 64)
    (disjoint : a + 8 ≤ b ∨ b + 8 ≤ a) :
    store64 (store64 mem a first) b second = store64 (store64 mem b second) a first := by
  apply Std.ExtHashMap.ext_getElem?
  intro other
  simp only [store64_lookup]
  by_cases ha : a ≤ other ∧ other < a + 8 <;>
    by_cases hb : b ≤ other ∧ other < b + 8
  · omega
  all_goals simp only [ha, hb, ↓reduceIte]

/-- Model limit: even a lossless final byte map cannot observe an
intermediate write overwritten at the same address. In particular, this
equation does NOT justify deleting a published descriptor's BBM break. -/
theorem store64_last_write_wins (mem : Memory) (address : Nat) (first last : BitVec 64) :
    store64 (store64 mem address first) address last = store64 mem address last := by
  apply Std.ExtHashMap.ext_getElem?
  intro other
  simp only [store64_lookup]
  split <;> simp_all

/-- Regression: starts differing by one byte are not independent stores.
The differing shared byte witnesses order sensitivity for every prior map. -/
theorem overlapping_store64_order_matters (mem : Memory) (address : Nat) :
    store64 (store64 mem address (0#64)) (address + 1) (0xffffffffffffffff#64) ≠
      store64 (store64 mem (address + 1) (0xffffffffffffffff#64)) address (0#64) := by
  intro same
  have lastOnes :
      (store64 (store64 mem address (0#64)) (address + 1)
        (0xffffffffffffffff#64))[address + 1]? = some (255#8) := by
    simpa using store64_byte (store64 mem address (0#64)) (address + 1)
      (0xffffffffffffffff#64) ⟨0, by decide⟩
  have lastZero :
      (store64 (store64 mem (address + 1) (0xffffffffffffffff#64))
        address (0#64))[address + 1]? = some (0#8) := by
    simpa using store64_byte (store64 mem (address + 1) (0xffffffffffffffff#64))
      address (0#64) ⟨1, by decide⟩
  have impossible : some (255#8) = some (0#8) :=
    lastOnes.symm.trans ((congrArg (fun m : Memory => m[address + 1]?) same).trans lastZero)
  contradiction

end SpanRefinement

end Oak.SailBridge.SequentialRAM
