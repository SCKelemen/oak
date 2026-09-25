import STRExecutionBridge

/-!
The original aset_Mem body, in the same generated state as STR. These
theorems retain the order and effects of arbitrary endian/alignment/callee
callbacks; they do not prove the callbacks implement Arm translation or RAM.
The normal aligned size-eight domain still performs the generated SCTLR_EL2
read before its endian query; Boolean simplification does not erase effects.
This is a fact about the adapted export, not a cross-backend Boolean/effect
refinement. Some originally pure callees are explicit impure cuts here.
-/

namespace STRExecution.MemoryBridge

open PreSail Functions Bridge

private theorem undefined_bool_eq :
    (PreSail.undefined_bool () : SailM Bool) = pure false := by
  funext state
  have hc : state.choiceState = () := by
    change (state.choiceState : Unit) = ()
    exact Subsingleton.elim (α := Unit) _ _
  change EStateM.Result.ok false { state with choiceState := () } = .ok _ state
  rw [← hc]

private theorem undefined_constraint_eq :
    undefined_Constraint () = (pure .Constraint_NONE : SailM Constraint) := by
  funext state
  have hc : state.choiceState = () := by
    change (state.choiceState : Unit) = ()
    exact Subsingleton.elim (α := Unit) _ _
  change EStateM.Result.ok Constraint.Constraint_NONE { state with choiceState := () } = .ok _ state
  rw [← hc]

/-- The endian decision's actual callback result, not an assumed byte swap. -/
def endianStep (memory : MemoryBoundaries) (big : Bool) (data : BitVec 64) : SailM (BitVec 64) :=
  if big then memory.BigEndianReverse data else pure data

/-- Feature, endian, conversion, and alignment states are kept distinct.
SCTLR_EL2 must be initialized after the feature query. No callback purity or
store-success premise is used. -/
theorem aligned64_run (boundaries : Boundaries) (memory : MemoryBoundaries)
    (state afterNV afterEndian afterConversion afterAlignment : State)
    (address data converted sctlr : BitVec 64) (nv big : Bool)
    (nvRun : (memory.HaveNV2Ext ()).run state = .ok nv afterNV)
    (registerPresent : afterNV.regs.get? Register.SCTLR_EL2 = some sctlr)
    (endianRun : (memory.BigEndian ()).run afterNV = .ok big afterEndian)
    (conversionRun : (endianStep memory big data).run afterEndian = .ok converted afterConversion)
    (alignmentRun : (memory.AArch64_CheckAlignment address 8 .AccType_NORMAL true).run
      afterConversion = .ok true afterAlignment) :
    (aset_Mem boundaries memory address 8 .AccType_NORMAL data).run state =
      (memory.AArch64_aset_MemSingle address 8 .AccType_NORMAL true converted).run afterAlignment := by
  have normal : (AccType.AccType_NORMAL == AccType.AccType_NV2REGISTER) = false := rfl
  cases nv <;> cases big <;>
    simp_all [aset_Mem, endianStep, undefined_bool_eq, undefined_constraint_eq,
      readReg, EStateM.run, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      MonadState.get, getThe, MonadStateOf.get, EStateM.get]

theorem normal64_nv_error (boundaries : Boundaries) (memory : MemoryBoundaries)
    (state afterNV : State) (address data : BitVec 64) (error : Sail.Error exception)
    (nvRun : (memory.HaveNV2Ext ()).run state = .error error afterNV) :
    (aset_Mem boundaries memory address 8 .AccType_NORMAL data).run state =
      .error error afterNV := by
  simp_all [aset_Mem, EStateM.run, Bind.bind, EStateM.bind]

/-- The generated read is eager even when NV2 is false and the access is
normal. Failure precedes BigEndian and all later callbacks. -/
theorem normal64_missing_sctlr (boundaries : Boundaries) (memory : MemoryBoundaries)
    (state afterNV : State) (address data : BitVec 64) (nv : Bool)
    (nvRun : (memory.HaveNV2Ext ()).run state = .ok nv afterNV)
    (missing : afterNV.regs.get? Register.SCTLR_EL2 = none) :
    (aset_Mem boundaries memory address 8 .AccType_NORMAL data).run state =
      .error .Unreachable afterNV := by
  simp_all [aset_Mem, readReg, EStateM.run, Bind.bind, EStateM.bind,
    MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    MonadExcept.throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem normal64_endian_error (boundaries : Boundaries) (memory : MemoryBoundaries)
    (state afterNV afterEndian : State) (address data sctlr : BitVec 64) (nv : Bool)
    (error : Sail.Error exception)
    (nvRun : (memory.HaveNV2Ext ()).run state = .ok nv afterNV)
    (registerPresent : afterNV.regs.get? Register.SCTLR_EL2 = some sctlr)
    (endianRun : (memory.BigEndian ()).run afterNV = .error error afterEndian) :
    (aset_Mem boundaries memory address 8 .AccType_NORMAL data).run state =
      .error error afterEndian := by
  simp_all [aset_Mem, readReg, EStateM.run, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, MonadState.get, getThe, MonadStateOf.get, EStateM.get]

theorem normal64_conversion_error (boundaries : Boundaries) (memory : MemoryBoundaries)
    (state afterNV afterEndian afterConversion : State)
    (address data sctlr : BitVec 64) (nv : Bool) (error : Sail.Error exception)
    (nvRun : (memory.HaveNV2Ext ()).run state = .ok nv afterNV)
    (registerPresent : afterNV.regs.get? Register.SCTLR_EL2 = some sctlr)
    (endianRun : (memory.BigEndian ()).run afterNV = .ok true afterEndian)
    (conversionRun : (memory.BigEndianReverse data).run afterEndian = .error error afterConversion) :
    (aset_Mem boundaries memory address 8 .AccType_NORMAL data).run state =
      .error error afterConversion := by
  simp_all [aset_Mem, readReg, EStateM.run, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, MonadState.get, getThe, MonadStateOf.get, EStateM.get]

theorem normal64_alignment_error (boundaries : Boundaries) (memory : MemoryBoundaries)
    (state afterNV afterEndian afterConversion afterAlignment : State)
    (address data converted sctlr : BitVec 64) (nv big : Bool) (error : Sail.Error exception)
    (nvRun : (memory.HaveNV2Ext ()).run state = .ok nv afterNV)
    (registerPresent : afterNV.regs.get? Register.SCTLR_EL2 = some sctlr)
    (endianRun : (memory.BigEndian ()).run afterNV = .ok big afterEndian)
    (conversionRun : (endianStep memory big data).run afterEndian = .ok converted afterConversion)
    (alignmentRun : (memory.AArch64_CheckAlignment address 8 .AccType_NORMAL true).run
      afterConversion = .error error afterAlignment) :
    (aset_Mem boundaries memory address 8 .AccType_NORMAL data).run state =
      .error error afterAlignment := by
  have normal : (AccType.AccType_NORMAL == AccType.AccType_NV2REGISTER) = false := rfl
  cases nv <;> cases big <;>
    simp_all [aset_Mem, endianStep, undefined_bool_eq, readReg,
      EStateM.run, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      MonadState.get, getThe, MonadStateOf.get, EStateM.get]

/-- An unaligned path can perform a byte write and then fail. No later
byte, constraint query, or whole-value replacement is licensed by this result. -/
theorem unaligned64_first_error (boundaries : Boundaries) (memory : MemoryBoundaries)
    (state afterNV afterEndian afterConversion afterAlignment afterByte : State)
    (address data converted sctlr : BitVec 64) (nv big : Bool) (error : Sail.Error exception)
    (nvRun : (memory.HaveNV2Ext ()).run state = .ok nv afterNV)
    (registerPresent : afterNV.regs.get? Register.SCTLR_EL2 = some sctlr)
    (endianRun : (memory.BigEndian ()).run afterNV = .ok big afterEndian)
    (conversionRun : (endianStep memory big data).run afterEndian = .ok converted afterConversion)
    (alignmentRun : (memory.AArch64_CheckAlignment address 8 .AccType_NORMAL true).run
      afterConversion = .ok false afterAlignment)
    (byteRun : (memory.AArch64_aset_MemSingle address 1 .AccType_NORMAL false
      (Sail.BitVec.slice converted 0 8)).run afterAlignment = .error error afterByte) :
    (aset_Mem boundaries memory address 8 .AccType_NORMAL data).run state =
      .error error afterByte := by
  have normal : (AccType.AccType_NORMAL == AccType.AccType_NV2REGISTER) = false := rfl
  cases nv <;> cases big <;>
    simp_all [aset_Mem, endianStep, undefined_bool_eq, undefined_constraint_eq,
      readReg, PreSail.assert, EStateM.run, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      MonadState.get, getThe, MonadStateOf.get, EStateM.get]

/-- Install the original callee in the instruction's explicit cut. The check
rejects widths outside the erased source relation; it is not a claim that the
generic Lean entry implements all Sail domains. It does not check the source's
size-set restriction. The proved STR64 entry fixes size=8 and discharges width. -/
def bindMemory (boundaries : Boundaries) (memory : MemoryBoundaries) : Boundaries :=
  { boundaries with
    aset_Mem := fun {width} address size acctype data =>
      dite (width = 8 * size)
        (fun h => Functions.aset_Mem boundaries memory address size acctype (h ▸ data))
        (fun _ state => .error .Unreachable state) }

theorem bindMemory64 (boundaries : Boundaries) (memory : MemoryBoundaries)
    (address data : BitVec 64) (acctype : AccType) :
    (bindMemory boundaries memory).aset_Mem address 8 acctype data =
      aset_Mem boundaries memory address 8 acctype data := by
  simp [bindMemory]

/-- Original STR and original aset_Mem now compose in one generated state.
Registers are read before memory callbacks, while the memory prefix starts
after the actual syndrome update. The final callback result remains arbitrary. -/
theorem str64_aligned_run (boundaries : Boundaries) (memory : MemoryBoundaries)
    (state afterFeature afterNV afterEndian afterConversion afterAlignment : State)
    (bank : Bank) (pstate : ProcState) (rn : Fin 31) (rt : Fin 32)
    (offset converted sctlr : BitVec 64) (nv big : Bool)
    (featureRun : (featurePrefix boundaries).run state = .ok () afterFeature)
    (bankPresent : afterFeature.regs.get? Register._R = some bank)
    (pstatePresent : afterFeature.regs.get? Register.PSTATE = some pstate)
    (nvRun : (memory.HaveNV2Ext ()).run (syndromeState afterFeature pstate rt) = .ok nv afterNV)
    (registerPresent : afterNV.regs.get? Register.SCTLR_EL2 = some sctlr)
    (endianRun : (memory.BigEndian ()).run afterNV = .ok big afterEndian)
    (conversionRun : (endianStep memory big (xValue bank rt)).run afterEndian = .ok converted afterConversion)
    (alignmentRun : (memory.AArch64_CheckAlignment (bank[rn.val] + offset) 8 .AccType_NORMAL true).run
      afterConversion = .ok true afterAlignment) :
    (memory_single_general_immediate_signed_postidx (bindMemory boundaries memory) .AccType_NORMAL 64
      .MemOp_STORE rn.val offset false 64 false rt.val false).run state =
      (memory.AArch64_aset_MemSingle (bank[rn.val] + offset) 8 .AccType_NORMAL true converted).run
        afterAlignment := by
  rw [str64_run (bindMemory boundaries memory) state afterFeature featureRun bank pstate rn rt
    offset bankPresent pstatePresent, bindMemory64]
  exact aligned64_run boundaries memory (syndromeState afterFeature pstate rt)
    afterNV afterEndian afterConversion afterAlignment (bank[rn.val] + offset)
    (xValue bank rt) converted sctlr nv big nvRun registerPresent endianRun conversionRun alignmentRun

namespace Examples

-- Deliberately nonarchitectural fixtures: unused callbacks are poison, and
-- the conversion adds one instead of assuming a correct Arm endian swap.
private def poison {α : Type} : SailM α := fun state => .error .Unreachable state

private def poisoned : MemoryBoundaries :=
  { HaveNV2Ext := fun _ => poison
    BigEndian := fun _ => poison
    BigEndianReverse := fun _ => poison
    AArch64_CheckAlignment := fun _ _ _ _ => poison
    Align__1 := fun _ _ => poison
    AArch64_aset_MemSingle := fun _ _ _ _ _ => poison }

private def empty : State :=
  { regs := ∅, choiceState := (), mem := ∅, tags := (), cycleCount := 0,
    sailOutput := #["preserved"] }

private def initial : State :=
  { empty with regs := empty.regs.insert Register.SCTLR_EL2 (0#64) }

private def bump (state : State) (n : Nat) : State :=
  { state with cycleCount := state.cycleCount + n }

private def nvOnly : MemoryBoundaries :=
  { poisoned with
    HaveNV2Ext := fun _ state => .ok false (bump state 1) }

/-- Even NV2=false cannot hide the missing register read. The poisoned
BigEndian callback is never reached, and the feature query's effect survives. -/
theorem missing_register_after_query (boundaries : Boundaries) :
    (aset_Mem boundaries nvOnly (0x1000#64) 8 .AccType_NORMAL (0x42#64)).run empty =
      .error .Unreachable (bump empty 1) := by
  exact normal64_missing_sctlr boundaries nvOnly empty (bump empty 1)
    (0x1000#64) (0x42#64) false (by rfl) (by simp [bump, empty])

private def removesRegister : MemoryBoundaries :=
  { poisoned with
    HaveNV2Ext := fun _ state => .ok true { (bump state 1) with regs := ∅ } }

/-- Initial register presence is not enough: the feature callback can erase
it before the generated read. The error retains the callback's modified state. -/
theorem query_erases_initialized_register (boundaries : Boundaries) :
    (aset_Mem boundaries removesRegister (0x1000#64) 8 .AccType_NORMAL (0x42#64)).run initial =
      .error .Unreachable (bump empty 1) := by
  exact normal64_missing_sctlr boundaries removesRegister initial (bump empty 1)
    (0x1000#64) (0x42#64) true (by rfl) (by simp [bump, empty])

private def writeThenFail {width : Nat} (address : BitVec 64) (size : Nat)
    (acctype : AccType) (aligned : Bool) (value : BitVec width) : SailM Unit := fun state =>
  if acctype == .AccType_NORMAL && ((size == 8 && aligned) || (size == 1 && !aligned)) then
    .error (.User (.Error_SError false))
      { state with mem := state.mem.insert address.toNat (value.extractLsb' 0 8) }
  else .error .Unreachable state

private def effectful (big aligned : Bool) : MemoryBoundaries :=
  { nvOnly with
    BigEndian := fun _ state => .ok big (bump state 2)
    BigEndianReverse := fun value state => .ok (value + 1) (bump state 4)
    AArch64_CheckAlignment := fun _ size acctype iswrite state =>
      if size == 8 && acctype == .AccType_NORMAL && iswrite then
        .ok aligned (bump state 8)
      else .error .Unreachable state
    AArch64_aset_MemSingle := writeThenFail }

/-- Conversion and alignment effects are visible to the final callback;
its byte mutation survives an SError result. This is a test callback's
effect, not a claim about Arm RAM or architectural exception handling. -/
theorem converted_store_partial_failure (boundaries : Boundaries) :
    (aset_Mem boundaries (effectful true true) (0x1000#64) 8 .AccType_NORMAL (0x42#64)).run initial =
      .error (.User (.Error_SError false))
        { (bump initial 15) with mem := initial.mem.insert 0x1000 (0x43#8) } := by
  rw [aligned64_run boundaries (effectful true true) initial (bump initial 1)
    (bump initial 3) (bump initial 7) (bump initial 15)
    (0x1000#64) (0x42#64) (0x43#64) (0#64) false true
    (by rfl) (by simp [bump, initial]) (by rfl) (by rfl) (by rfl)]
  rfl

private def installsRegister : MemoryBoundaries :=
  { (effectful false true) with
    HaveNV2Ext := fun _ state => .ok false
      { (bump state 1) with regs := state.regs.insert Register.SCTLR_EL2 (0#64) } }

/-- Conversely, an initially absent entry can be installed by the query.
Only its post-state must satisfy the initialization premise. -/
theorem query_installs_missing_register (boundaries : Boundaries) :
    (aset_Mem boundaries installsRegister (0x1000#64) 8 .AccType_NORMAL (0x42#64)).run empty =
      .error (.User (.Error_SError false))
        { (bump initial 11) with mem := initial.mem.insert 0x1000 (0x42#8) } := by
  rw [aligned64_run boundaries installsRegister empty (bump initial 1)
    (bump initial 3) (bump initial 3) (bump initial 11)
    (0x1000#64) (0x42#64) (0x42#64) (0#64) false false
    (by rfl) (by simp [bump, initial]) (by rfl) (by rfl) (by rfl)]
  rfl

/-- The unaligned first byte fails before ConstrainUnpredictable, for
arbitrary instruction boundaries. In particular no whole-value store occurs. -/
theorem unaligned_partial_failure (boundaries : Boundaries) :
    (aset_Mem boundaries (effectful false false) (0x1001#64) 8 .AccType_NORMAL (0x42#64)).run initial =
      .error (.User (.Error_SError false))
        { (bump initial 11) with mem := initial.mem.insert 0x1001 (0x42#8) } := by
  apply unaligned64_first_error boundaries (effectful false false) initial (bump initial 1)
    (bump initial 3) (bump initial 3) (bump initial 11)
    { (bump initial 11) with mem := initial.mem.insert 0x1001 (0x42#8) }
    (0x1001#64) (0x42#64) (0x42#64) (0#64) false false (.User (.Error_SError false))
  · rfl
  · simp [bump, initial]
  all_goals rfl

private def alignmentFailure : MemoryBoundaries :=
  { (effectful false true) with
    AArch64_CheckAlignment := fun _ _ _ _ state =>
      .error (.User (.Error_ExceptionTaken ())) (bump state 8)
    AArch64_aset_MemSingle := fun _ _ _ _ _ => poison }

theorem alignment_failure_before_store (boundaries : Boundaries) :
    (aset_Mem boundaries alignmentFailure (0x1001#64) 8 .AccType_NORMAL (0x42#64)).run initial =
      .error (.User (.Error_ExceptionTaken ())) (bump initial 11) := by
  apply normal64_alignment_error boundaries alignmentFailure initial (bump initial 1)
    (bump initial 3) (bump initial 3) (bump initial 11)
    (0x1001#64) (0x42#64) (0x42#64) (0#64) false false (.User (.Error_ExceptionTaken ()))
  · rfl
  · simp [bump, initial]
  all_goals rfl

theorem erased_width_mismatch_rejected (boundaries : Boundaries) (memory : MemoryBoundaries)
    (state : State) :
    ((bindMemory boundaries memory).aset_Mem (0x1000#64) 8 .AccType_NORMAL (0x42#32)).run state =
      .error .Unreachable state := by
  rfl

end Examples

/-- info: 'STRExecution.MemoryBridge.aligned64_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aligned64_run
/-- info: 'STRExecution.MemoryBridge.normal64_missing_sctlr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normal64_missing_sctlr
/-- info: 'STRExecution.MemoryBridge.normal64_alignment_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normal64_alignment_error
/-- info: 'STRExecution.MemoryBridge.unaligned64_first_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unaligned64_first_error
/-- info: 'STRExecution.MemoryBridge.bindMemory64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bindMemory64
/-- info: 'STRExecution.MemoryBridge.str64_aligned_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms str64_aligned_run
/-- info: 'STRExecution.MemoryBridge.Examples.converted_store_partial_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.converted_store_partial_failure
/-- info: 'STRExecution.MemoryBridge.Examples.unaligned_partial_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.unaligned_partial_failure

end STRExecution.MemoryBridge
