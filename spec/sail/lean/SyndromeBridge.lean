import RegisterBridge

/-!
# The original Arm load/store syndrome dependency

The complete ProcState record and both syndrome functions are copied from
the pinned model. This proves their generated sequential execution, not STR
execution, exception entry, ESR construction, or instruction-to-Mem routing.
The undefined size initializer is retained and overwritten; all claims here
use the export's existing trivial choice source, not arbitrary nondeterminism.
-/

namespace Oak.SailBridge.Syndrome

open SequentialRAM

def SupportedSize (size : Nat) : Prop :=
  size = 1 ∨ size = 2 ∨ size = 4 ∨ size = 8

def sizeCode (size : Nat) : BitVec 2 :=
  match size with
  | 1 => 0#2
  | 2 => 1#2
  | 4 => 2#2
  | _ => 3#2

/-- ISV, SAS, SSE, SRT, SF, AR, in the original concatenation order.
The size-code default is used only under SupportedSize below. -/
def encode (size : Nat) (signExtend : Bool) (rt : Fin 32)
    (sixtyFour acqRel : Bool) : BitVec 11 :=
  1#1 ++ sizeCode size ++ (if signExtend then 1#1 else 0#1) ++
    BitVec.ofNat 5 rt.val ++ (if sixtyFour then 1#1 else 0#1) ++
    (if acqRel then 1#1 else 0#1)

theorem make_run (state : State) (size : Nat) (supported : SupportedSize size)
    (signExtend : Bool) (rt : Fin 32) (sixtyFour acqRel : Bool) :
    (Out.Functions.MakeLSInstructionSyndrome size signExtend rt.val sixtyFour acqRel).run state =
      .ok (encode size signExtend rt sixtyFour acqRel) state := by
  have hrt : rt.val ≤ 31 := by have := rt.isLt; omega
  have slice : Out.Functions.__GetSlice_int 5 (Int.ofNat rt.val) 0 = BitVec.ofNat 5 rt.val := by
    apply BitVec.eq_of_toNat_eq
    simp [Out.Functions.__GetSlice_int, Sail.get_slice_int, BitVec.extractLsb'_toNat]
  have slice' : Out.Functions.__GetSlice_int 5 (rt.val : Int) 0 = ({ toFin := rt } : BitVec 5) := by
    simpa using slice
  have hc : state.choiceState = () := by
    change (state.choiceState : Unit) = ()
    exact Subsingleton.elim (α := Unit) _ _
  have hu : (PreSail.undefined_bitvector 2 : SailM (BitVec 2)) state = .ok (0#2) state := by
    change EStateM.Result.ok (0#2) { state with choiceState := () } = .ok (0#2) state
    rw [← hc]
  rcases supported with rfl | rfl | rfl | rfl <;>
    simp [Out.Functions.MakeLSInstructionSyndrome, encode, sizeCode,
      PreSail.assert, EStateM.run, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, hrt, hu]
  all_goals exact congrArg (fun x =>
    _ ++ (if signExtend then 1#1 else 0#1) ++ x ++
      (if sixtyFour then 1#1 else 0#1) ++ (if acqRel then 1#1 else 0#1)) slice'

def active (pstate : ProcState) : Bool := pstate.EL == 0#2 || pstate.EL == 1#2

def update (state : State) (value : BitVec 11) : State :=
  { state with regs := state.regs.insert Register.__LSISyndrome value }

theorem set_initialized (state : State) (pstate : ProcState)
    (initialized : state.regs.get? Register.PSTATE = some pstate)
    (size : Nat) (supported : SupportedSize size) (signExtend : Bool)
    (rt : Fin 32) (sixtyFour acqRel : Bool) :
    (Out.Functions.AArch64_SetLSInstructionSyndrome size signExtend rt.val sixtyFour acqRel).run state =
      .ok () (if active pstate then update state (encode size signExtend rt sixtyFour acqRel)
        else state) := by
  have make := make_run state size supported signExtend rt sixtyFour acqRel
  simp only [EStateM.run] at make
  by_cases low : active pstate = true <;>
    simp only [active, Bool.or_eq_true, beq_iff_eq] at low
  all_goals simp [Out.Functions.AArch64_SetLSInstructionSyndrome, active, low,
    Out.Functions.EL0, Out.Functions.EL1, PreSail.readReg, PreSail.writeReg,
    EStateM.run, Bind.bind, Pure.pure, MonadState.get, getThe, MonadStateOf.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    EStateM.bind, EStateM.pure, EStateM.get, initialized, make, update]

theorem set_missing (state : State) (missing : state.regs.get? Register.PSTATE = none)
    (size : Nat) (_supported : SupportedSize size) (signExtend : Bool)
    (rt : Fin 32) (sixtyFour acqRel : Bool) :
    (Out.Functions.AArch64_SetLSInstructionSyndrome size signExtend rt.val sixtyFour acqRel).run state =
      .error .Unreachable state := by
  simp [Out.Functions.AArch64_SetLSInstructionSyndrome, PreSail.readReg,
    EStateM.run, Bind.bind, MonadState.get, getThe, MonadStateOf.get,
    MonadExcept.throw, throwThe, MonadExceptOf.throw,
    EStateM.bind, EStateM.get, EStateM.throw, missing]

/-- Complete execution split; no PSTATE initializer is silently supplied. -/
theorem set_run (state : State) (size : Nat) (supported : SupportedSize size)
    (signExtend : Bool) (rt : Fin 32) (sixtyFour acqRel : Bool) :
    (Out.Functions.AArch64_SetLSInstructionSyndrome size signExtend rt.val sixtyFour acqRel).run state =
      match state.regs.get? Register.PSTATE with
      | none => .error .Unreachable state
      | some pstate => .ok () (if active pstate then
          update state (encode size signExtend rt sixtyFour acqRel) else state) := by
  cases h : state.regs.get? Register.PSTATE with
  | none => exact set_missing state h size supported signExtend rt sixtyFour acqRel
  | some pstate => exact set_initialized state pstate h size supported signExtend rt sixtyFour acqRel

theorem encode_fields (size : Nat) (signExtend : Bool) (rt : Fin 32)
    (sixtyFour acqRel : Bool) :
    let value := encode size signExtend rt sixtyFour acqRel
    value.extractLsb' 10 1 = 1#1 ∧
    value.extractLsb' 8 2 = sizeCode size ∧
    value.extractLsb' 7 1 = (if signExtend then 1#1 else 0#1) ∧
    value.extractLsb' 2 5 = BitVec.ofNat 5 rt.val ∧
    value.extractLsb' 1 1 = (if sixtyFour then 1#1 else 0#1) ∧
    value.extractLsb' 0 1 = (if acqRel then 1#1 else 0#1) := by
  simp only [encode]
  bv_decide

theorem set_low (state : State) (pstate : ProcState)
    (initialized : state.regs.get? Register.PSTATE = some pstate)
    (low : pstate.EL = 0#2 ∨ pstate.EL = 1#2)
    (size : Nat) (supported : SupportedSize size) (signExtend : Bool)
    (rt : Fin 32) (sixtyFour acqRel : Bool) :
    (Out.Functions.AArch64_SetLSInstructionSyndrome size signExtend rt.val sixtyFour acqRel).run state =
      .ok () (update state (encode size signExtend rt sixtyFour acqRel)) := by
  rw [set_initialized state pstate initialized size supported signExtend rt sixtyFour acqRel]
  simp [active, low]

theorem set_high (state : State) (pstate : ProcState)
    (initialized : state.regs.get? Register.PSTATE = some pstate)
    (high : pstate.EL = 2#2 ∨ pstate.EL = 3#2)
    (size : Nat) (supported : SupportedSize size) (signExtend : Bool)
    (rt : Fin 32) (sixtyFour acqRel : Bool) :
    (Out.Functions.AArch64_SetLSInstructionSyndrome size signExtend rt.val sixtyFour acqRel).run state =
      .ok () state := by
  rw [set_initialized state pstate initialized size supported signExtend rt sixtyFour acqRel]
  rcases high with high | high <;> simp [active, high]

theorem update_syndrome (state : State) (value : BitVec 11) :
    (update state value).regs.get? Register.__LSISyndrome = some value := by
  simp [update]

/-- Includes exact optional presence for PSTATE, the GPR bank, and RAM selector. -/
theorem update_other_register (state : State) (value : BitVec 11) (reg : Register)
    (other : reg ≠ Register.__LSISyndrome) :
    (update state value).regs.get? reg = state.regs.get? reg := by
  simp [update, Std.ExtDHashMap.get?_insert, Ne.symm other]

theorem update_non_registers (state : State) (value : BitVec 11) :
    (update state value).mem = state.mem ∧
    (update state value).tags = state.tags ∧
    (update state value).choiceState = state.choiceState ∧
    (update state value).cycleCount = state.cycleCount ∧
    (update state value).sailOutput = state.sailOutput := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

open GeneralRegisters

/-- A composition of proven dependencies, NOT the original STR instruction.
It deliberately has no PostDecode, SP, MTE check, Mem call, or fault routing. -/
def str64GPDependencies (rn : Fin 31) (rt : Fin 32) (imm12 : BitVec 12) :
    SailM (BitVec 64 × BitVec 64) := do
  let operands ← str64GPOperands rn rt imm12
  Out.Functions.AArch64_SetLSInstructionSyndrome 8 false rt.val true false
  pure operands

theorem str64GPDependencies_run (state : State) (bank : Bank) (pstate : ProcState)
    (bankInitialized : state.regs.get? Register._R = some bank)
    (stateInitialized : state.regs.get? Register.PSTATE = some pstate)
    (rn : Fin 31) (rt : Fin 32) (imm12 : BitVec 12) :
    (str64GPDependencies rn rt imm12).run state =
      .ok (bank[rn.val] + (imm12.setWidth 64 <<< 3), xValue bank rt)
        (if active pstate then update state (encode 8 false rt true false) else state) := by
  have operands := str64GPOperands_run state bank rn rt imm12 bankInitialized
  have syndrome := set_initialized state pstate stateInitialized 8 (by simp [SupportedSize])
    false rt true false
  unfold str64GPDependencies
  simp only [EStateM.run, Bind.bind, EStateM.bind] at operands syndrome ⊢
  rw [operands]
  dsimp only
  rw [syndrome]
  rfl

theorem str64GPDependencies_missingPSTATE (state : State) (bank : Bank)
    (bankInitialized : state.regs.get? Register._R = some bank)
    (missing : state.regs.get? Register.PSTATE = none)
    (rn : Fin 31) (rt : Fin 32) (imm12 : BitVec 12) :
    (str64GPDependencies rn rt imm12).run state = .error .Unreachable state := by
  have operands := str64GPOperands_run state bank rn rt imm12 bankInitialized
  have syndrome := set_missing state missing 8 (by simp [SupportedSize]) false rt true false
  unfold str64GPDependencies
  simp only [EStateM.run, Bind.bind, EStateM.bind] at operands syndrome ⊢
  rw [operands]
  dsimp only
  rw [syndrome]

theorem str64GPDependencies_el2 (state : State) (bank : Bank) (pstate : ProcState)
    (bankInitialized : state.regs.get? Register._R = some bank)
    (stateInitialized : state.regs.get? Register.PSTATE = some pstate)
    (el2 : pstate.EL = 2#2) (rn : Fin 31) (rt : Fin 32) (imm12 : BitVec 12) :
    (str64GPDependencies rn rt imm12).run state =
      .ok (bank[rn.val] + (imm12.setWidth 64 <<< 3), xValue bank rt) state := by
  rw [str64GPDependencies_run state bank pstate bankInitialized stateInitialized rn rt imm12]
  simp [active, el2]

namespace Examples

-- No initialized GPR bank or RAM selector, and no prior syndrome entry.
private def base : State :=
  { regs := ∅, choiceState := (), mem := (∅ : Memory).insert 17 (0xa5#8),
    tags := (), cycleCount := 37, sailOutput := #["prior output"] }

private def ps (el : BitVec 2) : ProcState :=
  { (default : ProcState) with EL := el, N := 1#1, GE := 0xa#4, IT := 0x81#8 }

private def atEL (el : BitVec 2) : State :=
  { base with regs := base.regs.insert Register.PSTATE (ps el) }

theorem break_el0 :
    (Out.Functions.AArch64_SetLSInstructionSyndrome 8 false 31 true false).run (atEL (0#2)) =
      .ok () (update (atEL (0#2)) (0x77e#11)) := by
  rw [set_low (atEL (0#2)) (ps (0#2)) (by simp [atEL]) (by simp [ps])
    8 (by simp [SupportedSize]) false ⟨31, by decide⟩ true false]
  rfl

theorem make_el1 :
    (Out.Functions.AArch64_SetLSInstructionSyndrome 8 false 2 true false).run (atEL (1#2)) =
      .ok () (update (atEL (1#2)) (0x70a#11)) := by
  rw [set_low (atEL (1#2)) (ps (1#2)) (by simp [atEL]) (by simp [ps])
    8 (by simp [SupportedSize]) false ⟨2, by decide⟩ true false]
  rfl

example : (atEL (0#2)).regs.get? Register.__LSISyndrome = none := by
  simp [atEL, base, Std.ExtDHashMap.get?_insert]

example : (update (atEL (0#2)) (0x77e#11)).regs.get? Register.__LSISyndrome = some (0x77e#11) :=
  update_syndrome _ _

example :
    (Out.Functions.AArch64_SetLSInstructionSyndrome 8 false 31 true false).run (atEL (2#2)) =
      .ok () (atEL (2#2)) :=
  set_high _ (ps (2#2)) (by simp [atEL]) (by simp [ps])
    8 (by simp [SupportedSize]) false ⟨31, by decide⟩ true false

example :
    (Out.Functions.AArch64_SetLSInstructionSyndrome 8 false 2 true false).run (atEL (3#2)) =
      .ok () (atEL (3#2)) :=
  set_high _ (ps (3#2)) (by simp [atEL]) (by simp [ps])
    8 (by simp [SupportedSize]) false ⟨2, by decide⟩ true false

/-- A high-EL no-op neither clears nor overwrites an existing syndrome. -/
example : let prior := update (atEL (2#2)) (0x555#11)
    (Out.Functions.AArch64_SetLSInstructionSyndrome 8 false 2 true false).run prior =
      .ok () prior := by
  dsimp only
  apply set_high _ (ps (2#2)) ?_ (by simp [ps])
    8 (by simp [SupportedSize]) false ⟨2, by decide⟩ true false
  rw [update_other_register _ _ _ (by decide)]
  simp [atEL]

example :
    (Out.Functions.AArch64_SetLSInstructionSyndrome 8 false 31 true false).run base =
      .error .Unreachable base :=
  set_missing base (by simp [base]) 8 (by simp [SupportedSize]) false ⟨31, by decide⟩ true false

-- Generated signatures erase source constraints, but retained assertions
-- reject these out-of-domain maker calls. Neither is an Arm Data Abort.
example : ∃ message,
    (Out.Functions.MakeLSInstructionSyndrome 16 false 0 true false).run base =
      .error (.Assertion message) base := ⟨_, rfl⟩

example : ∃ message,
    (Out.Functions.MakeLSInstructionSyndrome 8 false 32 true false).run base =
      .error (.Assertion message) base := ⟨_, rfl⟩

end Examples

/--
info: 'Oak.SailBridge.Syndrome.make_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms make_run

/--
info: 'Oak.SailBridge.Syndrome.set_initialized' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms set_initialized

/--
info: 'Oak.SailBridge.Syndrome.encode_fields' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms encode_fields

/--
info: 'Oak.SailBridge.Syndrome.str64GPDependencies_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms str64GPDependencies_run

/--
info: 'Oak.SailBridge.Syndrome.Examples.break_el0' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.break_el0

end Oak.SailBridge.Syndrome
