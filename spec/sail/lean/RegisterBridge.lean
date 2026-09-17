import MemoryBridge
import Std.Data.ExtDHashMap.Lemmas

/-!
# Actual generated reads of Arm's general-register bank

`_R` and `aget_X` are copied unchanged from the pinned Arm Sail model. The
generated Lean bank is a 31-element Vector and the accessor uses slot n
directly, not 30-n. The original width/index constraints become comments
in the export; the theorems retain their domain explicitly. XZR is not a
bank slot and does not require an initialized bank.

`str64GPOperands` below is an operand-only composition of these generated
reads, NOT the generated instruction body. It excludes SP, PostDecode,
syndrome writes, Mem, translation, faults and architectural event semantics.
In particular, its 64-bit address is virtual; no physical-memory write is
obtained by truncating that address into the existing RAM bridge.
-/

namespace Oak.SailBridge.GeneralRegisters

open SequentialRAM

abbrev Bank := Vector (BitVec 64) 31

def SupportedWidth (width : Nat) : Prop :=
  width = 8 ∨ width = 16 ∨ width = 32 ∨ width = 64

/-- Exact state-indexed execution, including initialization failure. The
whole state is preserved in every case; this is not an Arm exception. -/
theorem readX_run (state : State) (width : Nat) (_supported : SupportedWidth width)
    (n : Fin 32) :
    (Out.Functions.aget_X (width := width) n.val).run state =
      if n.val = 31 then .ok (0#width) state else
        match state.regs.get? Register._R with
        | none => .error .Unreachable state
        | some bank => .ok (bank[n.val]!.extractLsb' 0 width) state := by
  by_cases zero : n.val = 31
  · simp [Out.Functions.aget_X, zero, Out.Functions.Zeros, EStateM.run, Pure.pure, EStateM.pure]
  · cases h : state.regs.get? Register._R <;>
      simp [Out.Functions.aget_X, zero, Sail.BitVec.slice, PreSail.readReg, EStateM.run,
        Bind.bind, Pure.pure, MonadState.get, getThe, MonadStateOf.get,
        MonadExcept.throw, throwThe, MonadExceptOf.throw,
        EStateM.bind, EStateM.pure, EStateM.get, EStateM.throw, h]

theorem readX_gp (state : State) (bank : Bank) (width : Nat)
    (supported : SupportedWidth width) (n : Fin 31)
    (initialized : state.regs.get? Register._R = some bank) :
    (Out.Functions.aget_X (width := width) n.val).run state =
      .ok (bank[n.val].extractLsb' 0 width) state := by
  have hn : n.val ≠ 31 := by have := n.isLt; omega
  rw [readX_run state width supported ⟨n.val, by have := n.isLt; omega⟩,
    if_neg hn, initialized]
  simp [getElem!_pos, n.isLt]

theorem readX_zero (state : State) (width : Nat) (supported : SupportedWidth width) :
    (Out.Functions.aget_X (width := width) 31).run state = .ok (0#width) state := by
  exact readX_run state width supported ⟨31, by decide⟩

theorem readX_missing (state : State) (width : Nat) (supported : SupportedWidth width)
    (n : Fin 31) (missing : state.regs.get? Register._R = none) :
    (Out.Functions.aget_X (width := width) n.val).run state = .error .Unreachable state := by
  have hn : n.val ≠ 31 := by have := n.isLt; omega
  rw [readX_run state width supported ⟨n.val, by have := n.isLt; omega⟩, if_neg hn, missing]

/-- An explicit register-number interpretation of the exported bank.
There is no default or out-of-bounds lookup on this side of the relation. -/
def xValue (bank : Bank) (n : Fin 32) : BitVec 64 :=
  if h : n.val < 31 then bank[n.val] else 0#64

theorem read64_initialized (state : State) (bank : Bank) (n : Fin 32)
    (initialized : state.regs.get? Register._R = some bank) :
    (Out.Functions.aget_X (width := 64) n.val).run state = .ok (xValue bank n) state := by
  by_cases gp : n.val < 31
  · rw [readX_gp state bank 64 (by unfold SupportedWidth; simp) ⟨n.val, gp⟩ initialized]
    simp [xValue, gp]
  · have zero : n.val = 31 := by have := n.isLt; omega
    rw [zero, readX_zero state 64 (by unfold SupportedWidth; simp)]
    simp [xValue, gp]

/-- Supplied register values must agree with reads of this exact bank.
The bank's initialization/provenance is still an external premise. -/
def RegistersAgree (bank : Bank) (registers : Fin 32 → BitVec 64) : Prop :=
  ∀ n, xValue bank n = registers n

theorem register_relation_zero (bank : Bank) (registers : Fin 32 → BitVec 64)
    (agree : RegistersAgree bank registers) : registers ⟨31, by decide⟩ = 0#64 := by
  simpa [xValue] using (agree ⟨31, by decide⟩).symm

/-- Only the non-SP operand-reading fragment of unsigned-offset STR64.
The base read precedes the data read, and both are the generated accessor.
This adapter deliberately does not claim architectural execution of STR. -/
def str64GPOperands (rn : Fin 31) (rt : Fin 32) (imm12 : BitVec 12) :
    SailM (BitVec 64 × BitVec 64) := do
  let base ← Out.Functions.aget_X (width := 64) rn.val
  let value ← Out.Functions.aget_X (width := 64) rt.val
  pure (base + (imm12.setWidth 64 <<< 3), value)

theorem str64GPOperands_run (state : State) (bank : Bank)
    (rn : Fin 31) (rt : Fin 32) (imm12 : BitVec 12)
    (initialized : state.regs.get? Register._R = some bank) :
    (str64GPOperands rn rt imm12).run state =
      .ok (bank[rn.val] + (imm12.setWidth 64 <<< 3), xValue bank rt) state := by
  have base := read64_initialized state bank ⟨rn.val, by have := rn.isLt; omega⟩ initialized
  have value := read64_initialized state bank rt initialized
  simp only [xValue, rn.isLt, ↓reduceDIte] at base
  unfold str64GPOperands
  simp only [EStateM.run, Bind.bind, EStateM.bind] at base value ⊢
  rw [base]
  dsimp only
  rw [value]
  rfl

theorem str64GPOperands_missing (state : State) (rn : Fin 31) (rt : Fin 32)
    (imm12 : BitVec 12) (missing : state.regs.get? Register._R = none) :
    (str64GPOperands rn rt imm12).run state = .error .Unreachable state := by
  have base := readX_missing state 64 (by unfold SupportedWidth; simp) rn missing
  unfold str64GPOperands
  simp only [EStateM.run, Bind.bind, EStateM.bind] at base ⊢
  rw [base]

/-- Connect the actual bank reads to the already audited pure STR request.
SP is arbitrary here because the base-register domain excludes register 31. -/
theorem str64GPOperands_matches_request (state : State) (bank : Bank)
    (rn : Fin 31) (rt : Fin 32) (imm12 : BitVec 12) (sp : BitVec 64)
    (initialized : state.regs.get? Register._R = some bank) :
    (str64GPOperands rn rt imm12).run state =
      .ok (Out.Functions.str64_unsigned_store_request_pure
        (BitVec.ofNat 5 rt.val) (BitVec.ofNat 5 rn.val) imm12
        bank[rn.val] (xValue bank rt) sp) state := by
  have rnRep : (BitVec.ofNat 5 rn.val).toNat = rn.val :=
    Nat.mod_eq_of_lt (by have := rn.isLt; omega)
  have rtRep : (BitVec.ofNat 5 rt.val).toNat = rt.val := Nat.mod_eq_of_lt rt.isLt
  have rnNotSP : BitVec.ofNat 5 rn.val ≠ 31#5 := by
    intro same
    have h := congrArg BitVec.toNat same
    rw [rnRep] at h
    change rn.val = 31 at h
    have := rn.isLt
    omega
  have rtZero : BitVec.ofNat 5 rt.val = 31#5 ↔ rt.val = 31 := by
    rw [← BitVec.toNat_inj, rtRep]
    rfl
  rw [str64GPOperands_run state bank rn rt imm12 initialized,
    A64Encoding.str64_unsigned_store_request_bridge]
  simp only [Oak.ArmASL.str64UnsignedStoreRequest, if_neg rnNotSP, rtZero]
  by_cases zero : rt.val = 31
  · simp [zero, xValue]
  · simp only [if_neg zero]

theorem str64GPOperands_from_register_relation (state : State) (bank : Bank)
    (registers : Fin 32 → BitVec 64) (agree : RegistersAgree bank registers)
    (rn : Fin 31) (rt : Fin 32) (imm12 : BitVec 12)
    (initialized : state.regs.get? Register._R = some bank) :
    (str64GPOperands rn rt imm12).run state =
      .ok (registers ⟨rn.val, by have := rn.isLt; omega⟩ +
        (imm12.setWidth 64 <<< 3), registers rt) state := by
  have base := agree ⟨rn.val, by have := rn.isLt; omega⟩
  simp only [xValue, rn.isLt, ↓reduceDIte] at base
  rw [str64GPOperands_run state bank rn rt imm12 initialized, base, agree rt]

/-- The two BBM store operand pairs now come from actual generated bank
reads rather than independent X0/X2 parameters. No Mem call is made here. -/
theorem break_operands (state : State) (bank : Bank)
    (initialized : state.regs.get? Register._R = some bank) :
    (str64GPOperands ⟨0, by decide⟩ ⟨31, by decide⟩ (0#12)).run state =
      .ok (bank[0], 0#64) state := by
  rw [str64GPOperands_run state bank _ _ _ initialized]
  simp [xValue]

theorem make_operands (state : State) (bank : Bank)
    (initialized : state.regs.get? Register._R = some bank) :
    (str64GPOperands ⟨0, by decide⟩ ⟨2, by decide⟩ (0#12)).run state =
      .ok (bank[0], bank[2]) state := by
  rw [str64GPOperands_run state bank _ _ _ initialized]
  simp [xValue]

namespace Examples

def noBank : State := {
  regs := ∅, choiceState := (), mem := ∅, tags := (),
  cycleCount := 37, sailOutput := #["prior output"]
}

def bank : Bank := Vector.ofFn fun i =>
  if i.val = 0 then 0xfffffffffffffff8#64 else BitVec.ofNat 64 (0xfedcba9876543200 + i.val)

def withBank : State := { noBank with regs := noBank.regs.insert Register._R bank }

theorem bank_initialized : withBank.regs.get? Register._R = some bank := by
  simp [withBank]

/-- The RAM selector is absent; general-register reads do not need it. -/
example : withBank.regs.get? Register.__defaultRAM = none := by
  simp [withBank, noBank, Std.ExtDHashMap.get?_insert]

example : (Out.Functions.aget_X (width := 8) 2).run withBank = .ok (2#8) withBank := by
  rw [readX_gp withBank bank 8 (by unfold SupportedWidth; simp) ⟨2, by decide⟩ bank_initialized]
  rfl

example : (Out.Functions.aget_X (width := 16) 30).run withBank = .ok (0x321e#16) withBank := by
  rw [readX_gp withBank bank 16 (by unfold SupportedWidth; simp) ⟨30, by decide⟩ bank_initialized]
  rfl

example : (Out.Functions.aget_X (width := 32) 1).run withBank = .ok (0x76543201#32) withBank := by
  rw [readX_gp withBank bank 32 (by unfold SupportedWidth; simp) ⟨1, by decide⟩ bank_initialized]
  rfl

example : (Out.Functions.aget_X (width := 64) 30).run withBank =
    .ok (0xfedcba987654321e#64) withBank := by
  rw [readX_gp withBank bank 64 (by unfold SupportedWidth; simp) ⟨30, by decide⟩ bank_initialized]
  rfl

example : (Out.Functions.aget_X (width := 64) 31).run noBank = .ok (0#64) noBank :=
  readX_zero noBank 64 (by unfold SupportedWidth; simp)

example : (Out.Functions.aget_X (width := 64) 0).run noBank = .error .Unreachable noBank :=
  readX_missing noBank 64 (by unfold SupportedWidth; simp) ⟨0, by decide⟩
    (by simp [noBank])

example : (str64GPOperands ⟨0, by decide⟩ ⟨31, by decide⟩ (0#12)).run noBank =
    .error .Unreachable noBank :=
  str64GPOperands_missing noBank _ _ _ (by simp [noBank])

/-- A base/data alias reads the same bank twice; the largest immediate
is scaled by eight. The complete state, not just the result, is preserved. -/
theorem alias_and_offset :
    (str64GPOperands ⟨2, by decide⟩ ⟨2, by decide⟩ (4095#12)).run withBank =
      .ok (0xfedcba987654b1fa#64, 0xfedcba9876543202#64) withBank := by
  rw [str64GPOperands_run withBank bank _ _ _ bank_initialized]
  rfl

/-- Architectural-width operand arithmetic can wrap. This result is not
permission to reinterpret a virtual address as a 52-bit physical address. -/
theorem virtual_address_wrap :
    (str64GPOperands ⟨0, by decide⟩ ⟨2, by decide⟩ (1#12)).run withBank =
      .ok (0#64, 0xfedcba9876543202#64) withBank := by
  rw [str64GPOperands_run withBank bank _ _ _ bank_initialized]
  rfl

example : ¬ SupportedWidth 128 := by unfold SupportedWidth; decide

end Examples

/--
info: 'Oak.SailBridge.GeneralRegisters.readX_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms readX_run

/--
info: 'Oak.SailBridge.GeneralRegisters.str64GPOperands_matches_request' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms str64GPOperands_matches_request

/--
info: 'Oak.SailBridge.GeneralRegisters.str64GPOperands_from_register_relation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms str64GPOperands_from_register_relation

/--
info: 'Oak.SailBridge.GeneralRegisters.Examples.virtual_address_wrap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.virtual_address_wrap

end Oak.SailBridge.GeneralRegisters
