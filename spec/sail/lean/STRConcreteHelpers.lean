import STRMemSingleBridge

/-!
Two actual helper bodies in the shared adapted-export state. Configuration
declarations become registers in Sail 0.20.2's Lean export; the selected flag
must be initialized at the query, and no hardware capability is inferred.
The bindings do not run the global model initializer or change other cuts.
-/

namespace STRExecution.ConcreteHelpers

open PreSail Functions Bridge MemoryBridge MemSingleBridge

/-- The base architecture version does not inspect configuration registers. -/
theorem base_version (state : State) :
    (HasArchVersion .ARMv8p0).run state = .ok true state := by
  rfl

private theorem bool_tail_identity (action : SailM Bool) (next : Bool → SailM Bool)
    (identity : ∀ value, next value = pure value) : (action >>= next) = action := by
  have h : next = pure := funext identity
  rw [h, bind_pure]

/-- Each version selects its own flag; short-circuiting never demands an
unrelated configuration entry, even if the selected entry is false/missing. -/
theorem version_action (version : ArchVersion) :
    HasArchVersion version = (match version with
      | .ARMv8p0 => pure true
      | .ARMv8p1 => readReg Register.__v81_implemented
      | .ARMv8p2 => readReg Register.__v82_implemented
      | .ARMv8p3 => readReg Register.__v83_implemented
      | .ARMv8p4 => readReg Register.__v84_implemented
      | .ARMv8p5 => readReg Register.__v85_implemented) := by
  cases version
  · rfl
  all_goals
    dsimp only [HasArchVersion]
    simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
    first
    | rfl
    | apply bool_tail_identity
      intro value
      cases value <;> rfl

theorem nv_action : HaveNV2Ext () = readReg Register.__v84_implemented := by
  change ((readReg Register.__v84_implemented : SailM Bool) >>= fun flag =>
    if flag then pure true else pure false) = _
  have identity : (fun flag : Bool =>
      if flag then (pure true : SailM Bool) else pure false) = pure := by
    funext flag
    cases flag <;> rfl
  rw [identity, bind_pure]

/-- Only the selected flag is required. Both Boolean values preserve all state. -/
theorem nv_run (state : State) (enabled : Bool)
    (present : state.regs.get? Register.__v84_implemented = some enabled) :
    (HaveNV2Ext ()).run state = .ok enabled state := by
  rw [nv_action]
  simp [present, readReg, EStateM.run, Bind.bind,
      EStateM.bind, Pure.pure, EStateM.pure, MonadState.get, getThe,
      MonadStateOf.get, EStateM.get]

theorem nv_missing (state : State)
    (missing : state.regs.get? Register.__v84_implemented = none) :
    (HaveNV2Ext ()).run state = .error .Unreachable state := by
  rw [nv_action]
  simp [missing, readReg, EStateM.run, Bind.bind,
    EStateM.bind, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    MonadExcept.throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Full VA identity, not truncation to a physical-address width. -/
theorem zeroExtend64 (address : BitVec 64) :
    ZeroExtend__0 address 64 = (pure address : SailM (BitVec 64)) := by
  change (pure ((0#0) ++ address) : SailM (BitVec 64)) = pure address
  congr 1
  exact BitVec.append_of_zero_width _ _ rfl

theorem zeroExtend64_run (address : BitVec 64) (state : State) :
    (ZeroExtend__0 address 64).run state = .ok address state := by
  rw [zeroExtend64]
  rfl

/-- Shrinking, including negative requested sizes, fails before producing a
coerced-width result and preserves the complete failing state. -/
theorem zeroExtend_reject {width : Nat} (value : BitVec width) (size : Int)
    (state : State) (tooSmall : size < (width : Int)) :
    ∃ message, (ZeroExtend__0 value size).run state =
      .error (.Assertion message) state := by
  have rejected : ¬ (width : Int) ≤ size := by omega
  simp [ZeroExtend__0, PreSail.assert, Sail.BitVec.length, rejected,
    EStateM.run, Bind.bind, EStateM.bind, MonadExcept.throw, throwThe,
    MonadExceptOf.throw, EStateM.throw]

/-- A positive growth example retains all input bits with zero high bits. -/
theorem zeroExtend32_to64 (value : BitVec 32) :
    ZeroExtend__0 value 64 = (pure (value.setWidth 64) : SailM (BitVec 64)) := by
  change (pure ((0#32) ++ value) : SailM (BitVec 64)) = pure (value.setWidth 64)
  congr 1
  exact (BitVec.setWidth_eq_append (by decide : 32 ≤ 64)).symm

/-- Install only the actual zero-extension helper, retaining every other cut. -/
def bindZeroExtend (boundaries : Boundaries) : Boundaries :=
  { boundaries with ZeroExtend__0 := fun value size => Functions.ZeroExtend__0 value size }

/-- Install the actual configured feature query, without initializing state. -/
def bindNV (memory : MemoryBoundaries) : MemoryBoundaries :=
  { memory with HaveNV2Ext := Functions.HaveNV2Ext }

/-- The remaining tag callbacks still run in order and may fail or mutate
state. Repeated original zero-extension calls now deliver this same full VA. -/
def concreteTagStep (boundaries : Boundaries) (single : MemSingleBoundaries)
    (address : BitVec 64) (desc : AddressDescriptor) : SailM Unit := do
  if ← boundaries.HaveMTEExt () then
    if ← single.AccessIsTagChecked address .AccType_NORMAL then
      let tag ← single.TransformTag address
      if !(← single.CheckTag desc tag true) then
        single.TagCheckFail address true

theorem tagStep_concrete (boundaries : Boundaries) (single : MemSingleBoundaries)
    (address : BitVec 64) (desc : AddressDescriptor) :
    tagStep (bindZeroExtend boundaries) single address desc =
      concreteTagStep boundaries single address desc := by
  simp [tagStep, bindZeroExtend, zeroExtend64, concreteTagStep]

/-- No successful tag-failure return is assumed: its complete result,
including an error after state changes, survives the three identity calls. -/
theorem concrete_tag_failure (boundaries : Boundaries) (single : MemSingleBoundaries)
    (state afterFeature afterAccess afterTransform afterCheck : State)
    (address : BitVec 64) (desc : AddressDescriptor) (tag : BitVec 4)
    (featureRun : (boundaries.HaveMTEExt ()).run state = .ok true afterFeature)
    (accessRun : (single.AccessIsTagChecked address .AccType_NORMAL).run afterFeature =
      .ok true afterAccess)
    (transformRun : (single.TransformTag address).run afterAccess = .ok tag afterTransform)
    (checkRun : (single.CheckTag desc tag true).run afterTransform = .ok false afterCheck) :
    (tagStep (bindZeroExtend boundaries) single address desc).run state =
      (single.TagCheckFail address true).run afterCheck := by
  rw [tagStep_concrete]
  simp_all [concreteTagStep, EStateM.run, Bind.bind, EStateM.bind]

/-- End-to-end conditional composition with two actual helper bindings.
Configuration is required at the real query point, after arbitrary feature
effects and syndrome update. All other callees and the final _Mem result
remain explicit; there is no physical-memory or full-model refinement claim. -/
theorem str64_concrete_helpers_run (boundaries : Boundaries) (memory : MemoryBoundaries)
    (single : MemSingleBoundaries)
    (state afterFeature afterEndian afterConversion afterAlignment afterAlign
      afterTranslate afterFault afterShared afterAccess afterTag : State)
    (bank : Bank) (pstate : ProcState) (rn : Fin 31) (rt : Fin 32)
    (offset converted : BitVec 64) (nv big : Bool)
    (desc : AddressDescriptor) (access : AccessDescriptor)
    (featureRun : (featurePrefix boundaries).run state = .ok () afterFeature)
    (bankPresent : afterFeature.regs.get? Register._R = some bank)
    (pstatePresent : afterFeature.regs.get? Register.PSTATE = some pstate)
    (configured : (syndromeState afterFeature pstate rt).regs.get?
      Register.__v84_implemented = some nv)
    (endianRun : (memory.BigEndian ()).run (syndromeState afterFeature pstate rt) =
      .ok big afterEndian)
    (conversionRun : (endianStep memory big (xValue bank rt)).run afterEndian =
      .ok converted afterConversion)
    (alignmentRun : (memory.AArch64_CheckAlignment (bank[rn.val] + offset) 8
      .AccType_NORMAL true).run afterConversion = .ok true afterAlignment)
    (alignRun : (memory.Align__1 (bank[rn.val] + offset) 8).run afterAlignment =
      .ok (bank[rn.val] + offset) afterAlign)
    (translationRun : (single.AArch64_TranslateAddress (bank[rn.val] + offset)
      .AccType_NORMAL true true 8).run afterAlign = .ok desc afterTranslate)
    (faultRun : (faultStep single (bank[rn.val] + offset) desc).run afterTranslate =
      .ok () afterFault)
    (sharedRun : (sharedStep single desc).run afterFault = .ok () afterShared)
    (accessRun : (single.CreateAccessDescriptor .AccType_NORMAL).run afterShared =
      .ok access afterAccess)
    (tagRun : (concreteTagStep boundaries single (bank[rn.val] + offset) desc).run
      afterAccess = .ok () afterTag) :
    (memory_single_general_immediate_signed_postidx
      (bindMemory (bindZeroExtend boundaries)
        (bindMemSingle (bindZeroExtend boundaries) (bindNV memory) single))
      .AccType_NORMAL 64 .MemOp_STORE rn.val offset false 64 false rt.val false).run state =
      (single.aset__Mem desc 8 access converted).run afterTag := by
  exact str64_to_mem_run (bindZeroExtend boundaries) (bindNV memory) single
    state afterFeature (syndromeState afterFeature pstate rt) afterEndian afterConversion
    afterAlignment afterAlign afterTranslate afterFault afterShared afterAccess afterTag
    bank pstate rn rt offset converted nv big desc access featureRun bankPresent pstatePresent
    (nv_run _ nv configured) endianRun conversionRun alignmentRun alignRun translationRun
    faultRun sharedRun accessRun (by simpa only [tagStep_concrete] using tagRun)

namespace Examples

private def empty : State :=
  { regs := ∅, choiceState := (), mem := ∅, tags := (), cycleCount := 0, sailOutput := #[] }

private def sparse (enabled : Bool) : State :=
  { empty with regs := empty.regs.insert Register.__v84_implemented enabled }

theorem sparse_nv (enabled : Bool) :
    (HaveNV2Ext ()).run (sparse enabled) = .ok enabled (sparse enabled) := by
  apply nv_run
  simp [sparse]

theorem missing_nv : (HaveNV2Ext ()).run empty = .error .Unreachable empty := by
  apply nv_missing
  simp [empty]

theorem base_without_flags : (HasArchVersion .ARMv8p0).run empty = .ok true empty :=
  base_version empty

theorem high_va_identity :
    (ZeroExtend__0 (0xffff000000001000#64) 64).run empty =
      .ok (0xffff000000001000#64) empty := zeroExtend64_run _ _

theorem shrink_rejected (value : BitVec 64) :
    ∃ message, (ZeroExtend__0 value 63).run empty = .error (.Assertion message) empty :=
  zeroExtend_reject value 63 empty (by decide)

theorem negative_rejected (value : BitVec 64) :
    ∃ message, (ZeroExtend__0 value (-1)).run empty = .error (.Assertion message) empty :=
  zeroExtend_reject value (-1) empty (by decide)

end Examples

/-- info: 'STRExecution.ConcreteHelpers.version_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms version_action
/-- info: 'STRExecution.ConcreteHelpers.nv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nv_run
/-- info: 'STRExecution.ConcreteHelpers.nv_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nv_missing
/-- info: 'STRExecution.ConcreteHelpers.zeroExtend64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroExtend64
/-- info: 'STRExecution.ConcreteHelpers.zeroExtend_reject' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroExtend_reject
/-- info: 'STRExecution.ConcreteHelpers.zeroExtend32_to64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroExtend32_to64
/-- info: 'STRExecution.ConcreteHelpers.tagStep_concrete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tagStep_concrete
/-- info: 'STRExecution.ConcreteHelpers.concrete_tag_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_tag_failure
/-- info: 'STRExecution.ConcreteHelpers.str64_concrete_helpers_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms str64_concrete_helpers_run
/-- info: 'STRExecution.ConcreteHelpers.Examples.sparse_nv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.sparse_nv
/-- info: 'STRExecution.ConcreteHelpers.Examples.missing_nv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.missing_nv
/-- info: 'STRExecution.ConcreteHelpers.Examples.shrink_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.shrink_rejected
/-- info: 'STRExecution.ConcreteHelpers.Examples.negative_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.negative_rejected

end STRExecution.ConcreteHelpers
