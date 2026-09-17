import Bridge
import Std.Data.ExtHashMap.Lemmas

/-!
# The no-device RAM wrapper in Sail's sequential Lean runtime

Unlike the pure request projections, this module evaluates the generated
`__WriteRAM` effect against the actual imported `PreSail.write_ram` runtime.
The register-reading `__WriteMemory` wrapper is also generated unchanged,
including the no-device trace helper. Its success requires a populated
`__defaultRAM` entry in the actual generated register state.
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

end Oak.SailBridge.SequentialRAM
