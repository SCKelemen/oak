import STRExecution
import Std.Data.ExtDHashMap.Lemmas

/-!
# A conditional execution theorem for the original STR instruction body

Unlike the earlier dependency adapters, the left side below is generated from
the entire, unchanged Arm instruction body. Unimplemented callees remain
arbitrary explicit callbacks. This is a callee-parametric execution theorem,
not a proof that Arm's actual Mem, translation, PostDecode, or CAT events have
been implemented. The separate generated state and full exception union are
not identified with the older Out model. Undefined locals use the export's
trivial choice source, not arbitrary nondeterminism.
-/

namespace STRExecution.Bridge

open PreSail
open Functions

abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource
abbrev Bank := Vector (BitVec 64) 31

/-- Even with a non-SP base, MTE=true calls SetNotTagCheckedInstruction(false).
Both callbacks retain all effects and failures; no state-preservation premise
is silently supplied. -/
def featurePrefix (boundaries : Boundaries) : SailM Unit := do
  if ← boundaries.HaveMTEExt () then
    boundaries.SetNotTagCheckedInstruction false

/-- The original generated reads and syndrome setter remain concrete. -/
def storeTail (boundaries : Boundaries) (rn : Fin 31) (rt : Fin 32)
    (offset : BitVec 64) : SailM Unit := do
  let base ← aget_X (width := 64) rn.val
  let value ← aget_X (width := 64) rt.val
  AArch64_SetLSInstructionSyndrome 8 false rt.val true false
  boundaries.aset_Mem (base + offset) 8 .AccType_NORMAL value

private theorem undefined_bits_eq (width : Nat) :
    (PreSail.undefined_bitvector width : SailM (BitVec width)) = pure (0 : BitVec width) := by
  funext state
  have hc : state.choiceState = () := by
    change (state.choiceState : Unit) = ()
    exact Subsingleton.elim (α := Unit) _ _
  change EStateM.Result.ok (0 : BitVec width) { state with choiceState := () } = .ok _ state
  rw [← hc]

private theorem undefined_constraint_eq :
    undefined_Constraint () = (pure .Constraint_NONE : SailM Constraint) := by
  funext state
  have hc : state.choiceState = () := by
    change (state.choiceState : Unit) = ()
    exact Subsingleton.elim (α := Unit) _ _
  change EStateM.Result.ok Constraint.Constraint_NONE { state with choiceState := () } = .ok _ state
  rw [← hc]

/-- Exact callee-parametric equality, including every error and its post-state.
Only the non-SP unsigned 64-bit store domain is claimed. -/
theorem str64_factorization (boundaries : Boundaries) (rn : Fin 31) (rt : Fin 32)
    (offset : BitVec 64) :
    memory_single_general_immediate_signed_postidx boundaries .AccType_NORMAL 64
      .MemOp_STORE rn.val offset false 64 false rt.val false =
    (do featurePrefix boundaries; storeTail boundaries rn rt offset) := by
  have hn : rn.val ≠ 31 := by have := rn.isLt; omega
  have hbeq : (rn.val == 31) = false := beq_eq_false_iff_ne.mpr hn
  have hd : Nat.div 64 8 = 8 := by decide
  simp [memory_single_general_immediate_signed_postidx, featurePrefix, storeTail,
    undefined_bits_eq, undefined_constraint_eq, hn, hbeq, hd]
  funext state
  simp only [Bind.bind, EStateM.bind]
  cases h : boundaries.HaveMTEExt () state with
  | error e after => rfl
  | ok enabled after => cases enabled <;> rfl

/-- This is the bank representation of this generated module, proved directly;
no equality to the older Out.RegisterType is assumed. -/
def xValue (bank : Bank) (n : Fin 32) : BitVec 64 :=
  if h : n.val < 31 then bank[n.val] else 0#64

theorem read64_initialized (state : State) (bank : Bank) (n : Fin 32)
    (initialized : state.regs.get? Register._R = some bank) :
    (aget_X (width := 64) n.val).run state = .ok (xValue bank n) state := by
  by_cases gp : n.val < 31
  · have hn : n.val ≠ 31 := by omega
    simp [aget_X, hn, xValue, gp, Sail.BitVec.slice, readReg, EStateM.run,
      Bind.bind, Pure.pure, MonadState.get, getThe, MonadStateOf.get,
      EStateM.bind, EStateM.pure, EStateM.get, initialized, getElem!_pos]
  · have hn : n.val = 31 := by have := n.isLt; omega
    simp [aget_X, hn, xValue, Zeros, EStateM.run, Pure.pure, EStateM.pure]

theorem read64_missing (state : State) (n : Fin 31)
    (missing : state.regs.get? Register._R = none) :
    (aget_X (width := 64) n.val).run state = .error .Unreachable state := by
  have hn : n.val ≠ 31 := by have := n.isLt; omega
  simp [aget_X, hn, readReg, EStateM.run, Bind.bind,
    MonadState.get, getThe, MonadStateOf.get,
    MonadExcept.throw, throwThe, MonadExceptOf.throw,
    EStateM.bind, EStateM.get, EStateM.throw, missing]

def syndrome64 (rt : Fin 32) : BitVec 11 :=
  1#1 ++ 3#2 ++ 0#1 ++ __GetSlice_int 5 rt.val 0 ++ 1#1 ++ 0#1

private theorem make64 (rt : Fin 32) :
    MakeLSInstructionSyndrome 8 false rt.val true false =
      (pure (syndrome64 rt) : SailM (BitVec 11)) := by
  have ht : rt.val ≤ 31 := by have := rt.isLt; omega
  simp [MakeLSInstructionSyndrome, syndrome64, undefined_bits_eq, PreSail.assert, ht]

def syndromeState (state : State) (pstate : ProcState) (rt : Fin 32) : State :=
  if pstate.EL == 0#2 || pstate.EL == 1#2 then
    { state with regs := state.regs.insert Register.__LSISyndrome (syndrome64 rt) }
  else state

theorem set64_initialized (state : State) (pstate : ProcState) (rt : Fin 32)
    (initialized : state.regs.get? Register.PSTATE = some pstate) :
    (AArch64_SetLSInstructionSyndrome 8 false rt.val true false).run state =
      .ok () (syndromeState state pstate rt) := by
  by_cases el0 : pstate.EL = 0#2 <;> by_cases el1 : pstate.EL = 1#2
  all_goals simp [AArch64_SetLSInstructionSyndrome, make64, syndromeState, EL0, EL1,
    readReg, writeReg, EStateM.run, Bind.bind, Pure.pure,
    MonadState.get, getThe, MonadStateOf.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.bind, EStateM.pure,
    EStateM.get, initialized, el0, el1]

theorem set64_missing (state : State) (rt : Fin 32)
    (missing : state.regs.get? Register.PSTATE = none) :
    (AArch64_SetLSInstructionSyndrome 8 false rt.val true false).run state =
      .error .Unreachable state := by
  simp [AArch64_SetLSInstructionSyndrome, readReg, EStateM.run, Bind.bind,
    MonadState.get, getThe, MonadStateOf.get, MonadExcept.throw, throwThe,
    MonadExceptOf.throw, EStateM.bind, EStateM.get, EStateM.throw, missing]

theorem storeTail_run (boundaries : Boundaries) (state : State) (bank : Bank)
    (pstate : ProcState) (rn : Fin 31) (rt : Fin 32) (offset : BitVec 64)
    (bankInitialized : state.regs.get? Register._R = some bank)
    (pstateInitialized : state.regs.get? Register.PSTATE = some pstate) :
    (storeTail boundaries rn rt offset).run state =
      (boundaries.aset_Mem (bank[rn.val] + offset) 8 .AccType_NORMAL
        (xValue bank rt)).run (syndromeState state pstate rt) := by
  have base := read64_initialized state bank ⟨rn.val, by have := rn.isLt; omega⟩ bankInitialized
  have value := read64_initialized state bank rt bankInitialized
  have syndrome := set64_initialized state pstate rt pstateInitialized
  simp only [xValue, rn.isLt, ↓reduceDIte] at base
  unfold storeTail
  simp only [EStateM.run, Bind.bind, EStateM.bind] at base value syndrome ⊢
  rw [base]
  dsimp only
  rw [value]
  dsimp only
  rw [syndrome]

/-- Register initialization is required after the arbitrary feature callbacks,
not in the original state. The final Mem callback's complete result is retained. -/
theorem str64_run (boundaries : Boundaries) (state afterFeature : State)
    (prefixRun : (featurePrefix boundaries).run state = .ok () afterFeature)
    (bank : Bank) (pstate : ProcState) (rn : Fin 31) (rt : Fin 32) (offset : BitVec 64)
    (bankInitialized : afterFeature.regs.get? Register._R = some bank)
    (pstateInitialized : afterFeature.regs.get? Register.PSTATE = some pstate) :
    (memory_single_general_immediate_signed_postidx boundaries .AccType_NORMAL 64
      .MemOp_STORE rn.val offset false 64 false rt.val false).run state =
      (boundaries.aset_Mem (bank[rn.val] + offset) 8 .AccType_NORMAL
        (xValue bank rt)).run (syndromeState afterFeature pstate rt) := by
  rw [str64_factorization]
  simp only [EStateM.run, Bind.bind, EStateM.bind] at prefixRun ⊢
  rw [prefixRun]
  exact storeTail_run boundaries afterFeature bank pstate rn rt offset bankInitialized pstateInitialized

theorem str64_feature_error (boundaries : Boundaries) (state afterFeature : State)
    (error : Sail.Error exception)
    (prefixRun : (featurePrefix boundaries).run state = .error error afterFeature)
    (rn : Fin 31) (rt : Fin 32) (offset : BitVec 64) :
    (memory_single_general_immediate_signed_postidx boundaries .AccType_NORMAL 64
      .MemOp_STORE rn.val offset false 64 false rt.val false).run state =
      .error error afterFeature := by
  rw [str64_factorization]
  simp only [EStateM.run, Bind.bind, EStateM.bind] at prefixRun ⊢
  rw [prefixRun]

theorem str64_high_el (boundaries : Boundaries) (state afterFeature : State)
    (prefixRun : (featurePrefix boundaries).run state = .ok () afterFeature)
    (bank : Bank) (pstate : ProcState) (rn : Fin 31) (rt : Fin 32) (offset : BitVec 64)
    (bankInitialized : afterFeature.regs.get? Register._R = some bank)
    (pstateInitialized : afterFeature.regs.get? Register.PSTATE = some pstate)
    (high : pstate.EL = 2#2 ∨ pstate.EL = 3#2) :
    (memory_single_general_immediate_signed_postidx boundaries .AccType_NORMAL 64
      .MemOp_STORE rn.val offset false 64 false rt.val false).run state =
      (boundaries.aset_Mem (bank[rn.val] + offset) 8 .AccType_NORMAL
        (xValue bank rt)).run afterFeature := by
  rw [str64_run boundaries state afterFeature prefixRun bank pstate rn rt offset
    bankInitialized pstateInitialized]
  rcases high with high | high <;> simp [syndromeState, high]

/-- Concrete entry-domain check; the generalized callback record alone does
not assert this relation for arbitrary widths and counts. -/
theorem str64_request_width : 64 = 8 * 8 := by decide

theorem feature_true (boundaries : Boundaries) (state afterQuery : State)
    (query : (boundaries.HaveMTEExt ()).run state = .ok true afterQuery) :
    (featurePrefix boundaries).run state =
      (boundaries.SetNotTagCheckedInstruction false).run afterQuery := by
  unfold featurePrefix
  simp only [EStateM.run, Bind.bind, EStateM.bind] at query ⊢
  rw [query]
  rfl

theorem feature_false (boundaries : Boundaries) (state afterQuery : State)
    (query : (boundaries.HaveMTEExt ()).run state = .ok false afterQuery) :
    (featurePrefix boundaries).run state = .ok () afterQuery := by
  unfold featurePrefix
  simp only [EStateM.run, Bind.bind, EStateM.bind] at query ⊢
  rw [query]
  rfl

theorem feature_query_error (boundaries : Boundaries) (state afterQuery : State)
    (error : Sail.Error exception)
    (query : (boundaries.HaveMTEExt ()).run state = .error error afterQuery) :
    (featurePrefix boundaries).run state = .error error afterQuery := by
  unfold featurePrefix
  simp only [EStateM.run, Bind.bind, EStateM.bind] at query ⊢
  rw [query]

theorem str64_missing_bank (boundaries : Boundaries) (state afterFeature : State)
    (prefixRun : (featurePrefix boundaries).run state = .ok () afterFeature)
    (missing : afterFeature.regs.get? Register._R = none)
    (rn : Fin 31) (rt : Fin 32) (offset : BitVec 64) :
    (memory_single_general_immediate_signed_postidx boundaries .AccType_NORMAL 64
      .MemOp_STORE rn.val offset false 64 false rt.val false).run state =
      .error .Unreachable afterFeature := by
  rw [str64_factorization]
  have base := read64_missing afterFeature rn missing
  unfold storeTail
  simp only [EStateM.run, Bind.bind, EStateM.bind] at prefixRun base ⊢
  rw [prefixRun]
  dsimp only
  rw [base]

theorem str64_missing_pstate (boundaries : Boundaries) (state afterFeature : State)
    (prefixRun : (featurePrefix boundaries).run state = .ok () afterFeature)
    (bank : Bank) (bankInitialized : afterFeature.regs.get? Register._R = some bank)
    (missing : afterFeature.regs.get? Register.PSTATE = none)
    (rn : Fin 31) (rt : Fin 32) (offset : BitVec 64) :
    (memory_single_general_immediate_signed_postidx boundaries .AccType_NORMAL 64
      .MemOp_STORE rn.val offset false 64 false rt.val false).run state =
      .error .Unreachable afterFeature := by
  rw [str64_factorization]
  have base := read64_initialized afterFeature bank
    ⟨rn.val, by have := rn.isLt; omega⟩ bankInitialized
  have value := read64_initialized afterFeature bank rt bankInitialized
  have syndrome := set64_missing afterFeature rt missing
  unfold storeTail
  simp only [EStateM.run, Bind.bind, EStateM.bind] at prefixRun base value syndrome ⊢
  rw [prefixRun]
  dsimp only
  rw [base]
  dsimp only
  rw [value]
  dsimp only
  rw [syndrome]

namespace Examples

-- Poison callbacks are only test fixtures. They do not implement Arm callees.
private def poison {α : Type} : SailM α := fun state => .error .Unreachable state

private def poisoned : Boundaries :=
  { HaveMTEExt := fun _ => poison
    SetNotTagCheckedInstruction := fun _ => poison
    ConstrainUnpredictable := fun _ => poison
    EndOfInstruction := fun _ => poison
    CheckSPAlignment := fun _ => poison
    aget_SP := poison
    aset_SP := fun _ => poison
    aset_X := fun _ _ => poison
    aset_Mem := fun _ _ _ _ => poison
    aget_Mem := fun _ _ _ => poison
    Prefetch := fun _ _ => poison
    SignExtend__0 := fun _ _ => poison
    ZeroExtend__0 := fun _ _ => poison }

private def initial : State :=
  { regs := ∅, choiceState := (), mem := ∅, tags := (), cycleCount := 3,
    sailOutput := #["preserved"] }

private def bank (address value : BitVec 64) : Bank :=
  Vector.ofFn fun i => if i.val = 0 then address else if i.val = 2 then value else 0#64

private def ps (el : BitVec 2) : ProcState := { (default : ProcState) with EL := el }

private def install (state : State) (address value : BitVec 64) (el : BitVec 2) : State :=
  { state with
    regs := (state.regs.insert Register._R (bank address value)).insert Register.PSTATE (ps el)
    cycleCount := state.cycleCount + 1 }

private def queried := install initial (0x1000#64) (0x42#64) (0#2)
private def checked := install queried (0x2000#64) (0xab#64) (1#2)

private def writeThenFail {width : Nat} (address : BitVec 64) (_ : Nat) (_ : AccType)
    (value : BitVec width) : SailM Unit := fun state =>
  .error (.User (.Error_SError true))
    { state with
      mem := state.mem.insert address.toNat (value.extractLsb' 0 8)
      cycleCount := state.cycleCount + 10 }

private def effectful : Boundaries :=
  { poisoned with
    HaveMTEExt := fun _ state => .ok true
      (install state (0x1000#64) (0x42#64) (0#2))
    SetNotTagCheckedInstruction := fun unchecked state =>
      if unchecked then .error .Unreachable state
      else .ok () (install state (0x2000#64) (0xab#64) (1#2))
    aset_Mem := writeThenFail }

private def x0 : Fin 31 := ⟨0, by decide⟩
private def x2 : Fin 32 := ⟨2, by decide⟩

/-- Both feature callbacks change the registers/PSTATE before the real reads.
The Mem callback then writes and fails; all effects and its exception survive.
All SP/load/writeback/unused callbacks are poison and cannot be used here. -/
theorem changed_registers_and_mem_error :
    (memory_single_general_immediate_signed_postidx effectful .AccType_NORMAL 64
      .MemOp_STORE 0 (8#64) false 64 false 2 false).run initial =
    .error (.User (.Error_SError true))
      { (syndromeState checked (ps (1#2)) x2) with
        mem := checked.mem.insert 0x2008 (0xab#8), cycleCount := checked.cycleCount + 10 } := by
  have h := str64_run effectful initial checked (by rfl)
    (bank (0x2000#64) (0xab#64)) (ps (1#2)) x0 x2 (8#64)
    (by simp [checked, install, Std.ExtDHashMap.get?_insert]) (by simp [checked, install])
  simp only [x0, x2] at h
  rw [h]
  rfl

private def setterFailure : Boundaries :=
  { poisoned with
    HaveMTEExt := fun _ state => .ok true { state with cycleCount := state.cycleCount + 1 }
    SetNotTagCheckedInstruction := fun unchecked state =>
      if unchecked then .ok () state
      else .error (.User (.Error_Undefined ())) { state with cycleCount := state.cycleCount + 2 } }

/-- MTE=true still executes the false setter argument; its failure prevents
all register accesses and preserves its partially modified state. -/
theorem false_setter_can_fail :
    (memory_single_general_immediate_signed_postidx setterFailure .AccType_NORMAL 64
      .MemOp_STORE 0 (0#64) false 64 false 2 false).run initial =
    .error (.User (.Error_Undefined ())) { initial with cycleCount := 6 } := by
  exact str64_feature_error setterFailure initial { initial with cycleCount := 6 }
    (.User (.Error_Undefined ())) (by rfl) x0 x2 (0#64)

private def noMTE : Boundaries :=
  { poisoned with
    HaveMTEExt := fun _ state => .ok false { state with cycleCount := state.cycleCount + 1 } }

/-- MTE=false does not call the poisoned setter, but the feature query's
state change remains visible when the absent actual bank read fails. -/
theorem missing_bank_after_feature :
    (memory_single_general_immediate_signed_postidx noMTE .AccType_NORMAL 64
      .MemOp_STORE 0 (0#64) false 64 false 31 false).run initial =
      .error .Unreachable { initial with cycleCount := 4 } := by
  exact str64_missing_bank noMTE initial { initial with cycleCount := 4 }
    (by rfl) (by simp [initial]) x0 ⟨31, by decide⟩ (0#64)

private def bankOnly : State :=
  { initial with regs := initial.regs.insert Register._R (bank (0x1000#64) (0x42#64)) }

theorem missing_pstate_after_reads :
    (memory_single_general_immediate_signed_postidx noMTE .AccType_NORMAL 64
      .MemOp_STORE 0 (0#64) false 64 false 2 false).run bankOnly =
      .error .Unreachable { bankOnly with cycleCount := 4 } := by
  exact str64_missing_pstate noMTE bankOnly { bankOnly with cycleCount := 4 }
    (by rfl) (bank (0x1000#64) (0x42#64)) (by simp [bankOnly])
    (by simp [bankOnly, initial, Std.ExtDHashMap.get?_insert]) x0 x2 (0#64)

theorem high_el_preserves_syndrome (state : State) (rt : Fin 32) :
    syndromeState state (ps (2#2)) rt = state ∧
      syndromeState state (ps (3#2)) rt = state := by
  simp [syndromeState, ps]

end Examples

/-- info: 'STRExecution.Bridge.str64_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms str64_factorization
/-- info: 'STRExecution.Bridge.str64_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms str64_run
/-- info: 'STRExecution.Bridge.str64_feature_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms str64_feature_error
/-- info: 'STRExecution.Bridge.str64_missing_bank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms str64_missing_bank
/-- info: 'STRExecution.Bridge.str64_missing_pstate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms str64_missing_pstate
/-- info: 'STRExecution.Bridge.Examples.changed_registers_and_mem_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.changed_registers_and_mem_error
/-- info: 'STRExecution.Bridge.Examples.false_setter_can_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.false_setter_can_fail

end STRExecution.Bridge
