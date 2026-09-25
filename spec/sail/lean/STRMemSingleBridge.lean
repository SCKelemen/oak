import STRMemoryBridge

/-!
# Conditional execution of the original AArch64_aset_MemSingle body

The generated callee retains full descriptors and its original assertions and
control flow. Deeper callees remain arbitrary explicit actions in this model's
state: this is not real translation, physical RAM, CAT ordering, or a proof of
Arm's full-state refinement. In particular an Abort/TagCheckFail callback that
returns normally does not stop the original body's later write. Undefined
locals are interpreted by the existing trivial choice source.
-/

namespace STRExecution.MemSingleBridge

open PreSail Functions Bridge MemoryBridge

private theorem undefined_address_discard {α : Type} (next : SailM α) :
    (do let _ ← undefined_AddressDescriptor (); next) = next := by
  funext state
  have hc : state.choiceState = () := by
    change (state.choiceState : Unit) = ()
    exact Subsingleton.elim (α := Unit) _ _
  change next { state with choiceState := () } = next state
  rw [← hc]

private theorem bind_if {α β : Type} (p : Prop) [Decidable p]
    (yes no : SailM α) (next : α → SailM β) :
    ((if p then yes else no) >>= next) =
      (if p then yes >>= next else no >>= next) := by
  by_cases h : p <;> simp [h]

/-- No non-return assumption is attached to the arbitrary abort callback. -/
def faultStep (single : MemSingleBoundaries) (address : BitVec 64)
    (desc : AddressDescriptor) : SailM Unit := do
  if IsFault desc then single.AArch64_Abort address desc.fault

/-- Preserve both components of FullAddress, including NS, and obtain the
processor identifier before invoking the exclusive-clear action. -/
def sharedStep (single : MemSingleBoundaries) (desc : AddressDescriptor) : SailM Unit := do
  if desc.memattrs.shareable then
    let processor ← single.ProcessorID ()
    single.ClearExclusiveByAddress desc.paddress processor 8

/-- The three ZeroExtend calls are deliberately distinct arbitrary actions.
Their results and states may differ. A returning tag-failure action permits
the outer original body to continue. -/
def tagStep (boundaries : Boundaries) (single : MemSingleBoundaries)
    (address : BitVec 64) (desc : AddressDescriptor) : SailM Unit := do
  if ← boundaries.HaveMTEExt () then
    let accessAddress ← boundaries.ZeroExtend__0 address 64
    if ← single.AccessIsTagChecked accessAddress .AccType_NORMAL then
      let tagAddress ← boundaries.ZeroExtend__0 address 64
      let tag ← single.TransformTag tagAddress
      if !(← single.CheckTag desc tag true) then
        let faultAddress ← boundaries.ZeroExtend__0 address 64
        single.TagCheckFail faultAddress true

def afterTranslation (boundaries : Boundaries) (single : MemSingleBoundaries)
    (address data : BitVec 64) (desc : AddressDescriptor) : SailM Unit := do
  faultStep single address desc
  sharedStep single desc
  let access ← single.CreateAccessDescriptor .AccType_NORMAL
  tagStep boundaries single address desc
  single.aset__Mem desc 8 access data

/-- Conditional factorization of the complete generated body. Alignment is a
stateful call whose actual return value must equal the original full VA.
Translation is not assumed to succeed or return a fault-free descriptor. -/
theorem aligned64_factorization (boundaries : Boundaries) (memory : MemoryBoundaries)
    (single : MemSingleBoundaries) (state afterAlignment : State)
    (address data : BitVec 64) (wasaligned : Bool)
    (alignmentRun : (memory.Align__1 address 8).run state = .ok address afterAlignment) :
    (AArch64_aset_MemSingle boundaries memory single address 8 .AccType_NORMAL wasaligned data).run state =
      (do
        let desc ← single.AArch64_TranslateAddress address .AccType_NORMAL true wasaligned 8
        afterTranslation boundaries single address data desc).run afterAlignment := by
  simp only [EStateM.run] at alignmentRun
  simp only [AArch64_aset_MemSingle, afterTranslation, faultStep, sharedStep, tagStep,
    bind_assoc, bind_if, pure_bind, undefined_address_discard]
  simp [PreSail.assert, EStateM.run, Bind.bind, EStateM.bind, Pure.pure,
    EStateM.pure, alignmentRun]

/-- Each successful prefix premise names its actual post-state. The final
memory action is not assumed successful and retains its entire result. -/
theorem afterTranslation_run (boundaries : Boundaries) (single : MemSingleBoundaries)
    (state afterFault afterShared afterAccess afterTag : State)
    (address data : BitVec 64) (desc : AddressDescriptor) (access : AccessDescriptor)
    (faultRun : (faultStep single address desc).run state = .ok () afterFault)
    (sharedRun : (sharedStep single desc).run afterFault = .ok () afterShared)
    (accessRun : (single.CreateAccessDescriptor .AccType_NORMAL).run afterShared = .ok access afterAccess)
    (tagRun : (tagStep boundaries single address desc).run afterAccess = .ok () afterTag) :
    (afterTranslation boundaries single address data desc).run state =
      (single.aset__Mem desc 8 access data).run afterTag := by
  unfold afterTranslation
  simp only [EStateM.run, Bind.bind, EStateM.bind] at faultRun sharedRun accessRun tagRun ⊢
  rw [faultRun]
  dsimp only
  rw [sharedRun]
  dsimp only
  rw [accessRun]
  dsimp only
  rw [tagRun]

theorem aligned64_run (boundaries : Boundaries) (memory : MemoryBoundaries)
    (single : MemSingleBoundaries)
    (state afterAlignment afterTranslate afterFault afterShared afterAccess afterTag : State)
    (address data : BitVec 64) (wasaligned : Bool)
    (desc : AddressDescriptor) (access : AccessDescriptor)
    (alignmentRun : (memory.Align__1 address 8).run state = .ok address afterAlignment)
    (translationRun : (single.AArch64_TranslateAddress address .AccType_NORMAL true wasaligned 8).run
      afterAlignment = .ok desc afterTranslate)
    (faultRun : (faultStep single address desc).run afterTranslate = .ok () afterFault)
    (sharedRun : (sharedStep single desc).run afterFault = .ok () afterShared)
    (accessRun : (single.CreateAccessDescriptor .AccType_NORMAL).run afterShared = .ok access afterAccess)
    (tagRun : (tagStep boundaries single address desc).run afterAccess = .ok () afterTag) :
    (AArch64_aset_MemSingle boundaries memory single address 8 .AccType_NORMAL wasaligned data).run state =
      (single.aset__Mem desc 8 access data).run afterTag := by
  rw [aligned64_factorization boundaries memory single state afterAlignment address data wasaligned alignmentRun]
  simp only [EStateM.run, Bind.bind, EStateM.bind] at translationRun ⊢
  rw [translationRun]
  exact afterTranslation_run boundaries single afterTranslate afterFault afterShared afterAccess afterTag
    address data desc access faultRun sharedRun accessRun tagRun

theorem alignment_error (boundaries : Boundaries) (memory : MemoryBoundaries)
    (single : MemSingleBoundaries) (state afterAlignment : State)
    (address data : BitVec 64) (wasaligned : Bool) (error : Sail.Error exception)
    (alignmentRun : (memory.Align__1 address 8).run state = .error error afterAlignment) :
    (AArch64_aset_MemSingle boundaries memory single address 8 .AccType_NORMAL wasaligned data).run state =
      .error error afterAlignment := by
  simp only [EStateM.run] at alignmentRun
  simp [AArch64_aset_MemSingle, PreSail.assert, EStateM.run, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, alignmentRun]

theorem alignment_assertion (boundaries : Boundaries) (memory : MemoryBoundaries)
    (single : MemSingleBoundaries) (state afterAlignment : State)
    (address aligned data : BitVec 64) (wasaligned : Bool)
    (alignmentRun : (memory.Align__1 address 8).run state = .ok aligned afterAlignment)
    (different : address ≠ aligned) :
    ∃ message, (AArch64_aset_MemSingle boundaries memory single address 8 .AccType_NORMAL wasaligned data).run state =
      .error (.Assertion message) afterAlignment := by
  simp only [EStateM.run] at alignmentRun
  simp [AArch64_aset_MemSingle, PreSail.assert, EStateM.run, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, alignmentRun, different,
    MonadExcept.throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem translation_error (boundaries : Boundaries) (memory : MemoryBoundaries)
    (single : MemSingleBoundaries) (state afterAlignment afterTranslate : State)
    (address data : BitVec 64) (wasaligned : Bool) (error : Sail.Error exception)
    (alignmentRun : (memory.Align__1 address 8).run state = .ok address afterAlignment)
    (translationRun : (single.AArch64_TranslateAddress address .AccType_NORMAL true wasaligned 8).run
      afterAlignment = .error error afterTranslate) :
    (AArch64_aset_MemSingle boundaries memory single address 8 .AccType_NORMAL wasaligned data).run state =
      .error error afterTranslate := by
  rw [aligned64_factorization boundaries memory single state afterAlignment address data wasaligned alignmentRun]
  simp only [EStateM.run, Bind.bind, EStateM.bind] at translationRun ⊢
  rw [translationRun]

theorem fault_error (boundaries : Boundaries) (single : MemSingleBoundaries)
    (state afterAbort : State) (address data : BitVec 64) (desc : AddressDescriptor)
    (error : Sail.Error exception) (fault : IsFault desc = true)
    (abortRun : (single.AArch64_Abort address desc.fault).run state = .error error afterAbort) :
    (afterTranslation boundaries single address data desc).run state = .error error afterAbort := by
  simp only [EStateM.run] at abortRun
  simp [afterTranslation, faultStep, fault, EStateM.run, Bind.bind, EStateM.bind, abortRun]

theorem shared_run (single : MemSingleBoundaries) (state afterProcessor : State)
    (desc : AddressDescriptor) (processor : Int) (shared : desc.memattrs.shareable = true)
    (processorRun : (single.ProcessorID ()).run state = .ok processor afterProcessor) :
    (sharedStep single desc).run state =
      (single.ClearExclusiveByAddress desc.paddress processor 8).run afterProcessor := by
  simp only [EStateM.run] at processorRun
  simp [sharedStep, shared, EStateM.run, Bind.bind, EStateM.bind, processorRun]

theorem not_shared (single : MemSingleBoundaries) (state : State)
    (desc : AddressDescriptor) (shared : desc.memattrs.shareable = false) :
    (sharedStep single desc).run state = .ok () state := by
  simp [sharedStep, shared, EStateM.run, Pure.pure, EStateM.pure]

theorem tag_disabled (boundaries : Boundaries) (single : MemSingleBoundaries)
    (state afterFeature : State) (address : BitVec 64) (desc : AddressDescriptor)
    (featureRun : (boundaries.HaveMTEExt ()).run state = .ok false afterFeature) :
    (tagStep boundaries single address desc).run state = .ok () afterFeature := by
  simp only [EStateM.run] at featureRun
  simp [tagStep, EStateM.run, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, featureRun]

theorem tag_not_checked (boundaries : Boundaries) (single : MemSingleBoundaries)
    (state afterFeature afterExtend afterAccessCheck : State)
    (address accessAddress : BitVec 64) (desc : AddressDescriptor)
    (featureRun : (boundaries.HaveMTEExt ()).run state = .ok true afterFeature)
    (extendRun : (boundaries.ZeroExtend__0 address 64).run afterFeature = .ok accessAddress afterExtend)
    (accessRun : (single.AccessIsTagChecked accessAddress .AccType_NORMAL).run afterExtend =
      .ok false afterAccessCheck) :
    (tagStep boundaries single address desc).run state = .ok () afterAccessCheck := by
  simp only [EStateM.run] at featureRun extendRun accessRun
  simp [tagStep, EStateM.run, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    featureRun, extendRun, accessRun]

def tagFailureStep (boundaries : Boundaries) (single : MemSingleBoundaries)
    (address : BitVec 64) (tagMatches : Bool) : SailM Unit := do
  if !tagMatches then
    let faultAddress ← boundaries.ZeroExtend__0 address 64
    single.TagCheckFail faultAddress true

theorem tag_checked_run (boundaries : Boundaries) (single : MemSingleBoundaries)
    (state afterFeature afterExtend1 afterAccessCheck afterExtend2 afterTransform afterCheck : State)
    (address accessAddress tagAddress : BitVec 64) (desc : AddressDescriptor)
    (tag : BitVec 4) (tagMatches : Bool)
    (featureRun : (boundaries.HaveMTEExt ()).run state = .ok true afterFeature)
    (extend1Run : (boundaries.ZeroExtend__0 address 64).run afterFeature = .ok accessAddress afterExtend1)
    (accessRun : (single.AccessIsTagChecked accessAddress .AccType_NORMAL).run afterExtend1 =
      .ok true afterAccessCheck)
    (extend2Run : (boundaries.ZeroExtend__0 address 64).run afterAccessCheck = .ok tagAddress afterExtend2)
    (transformRun : (single.TransformTag tagAddress).run afterExtend2 = .ok tag afterTransform)
    (checkRun : (single.CheckTag desc tag true).run afterTransform = .ok tagMatches afterCheck) :
    (tagStep boundaries single address desc).run state =
      (tagFailureStep boundaries single address tagMatches).run afterCheck := by
  simp only [EStateM.run] at featureRun extend1Run accessRun extend2Run transformRun checkRun
  simp [tagStep, tagFailureStep, EStateM.run, Bind.bind, EStateM.bind, Pure.pure,
    featureRun, extend1Run, accessRun, extend2Run, transformRun, checkRun]

/-- Install the actual generated MemSingle callee only when the erased
width/count relation is satisfied; unsupported widths fail explicitly.
The size set still requires the generated callee's original assertion. -/
def bindMemSingle (boundaries : Boundaries) (memory : MemoryBoundaries)
    (single : MemSingleBoundaries) : MemoryBoundaries :=
  { memory with
    AArch64_aset_MemSingle := fun {width} address size acctype wasaligned data =>
      dite (width = 8 * size)
        (fun h => Functions.AArch64_aset_MemSingle boundaries memory single address size acctype wasaligned (h ▸ data))
        (fun _ state => .error .Unreachable state) }

theorem bindMemSingle64 (boundaries : Boundaries) (memory : MemoryBoundaries)
    (single : MemSingleBoundaries) (address data : BitVec 64) (wasaligned : Bool) :
    (bindMemSingle boundaries memory single).AArch64_aset_MemSingle address 8 .AccType_NORMAL wasaligned data =
      AArch64_aset_MemSingle boundaries memory single address 8 .AccType_NORMAL wasaligned data := by
  simp [bindMemSingle]

/-- The three retained original bodies compose in this one generated state.
The result is still exactly the arbitrary final _Mem action's result, not a
claimed physical write. Every prefix action must establish its actual supplied
post-state. Normal accesses require no SCTLR_EL2 initialization. -/
theorem str64_to_mem_run (boundaries : Boundaries) (memory : MemoryBoundaries)
    (single : MemSingleBoundaries)
    (state afterFeature afterNV afterEndian afterConversion afterAlignment
      afterAlign afterTranslate afterFault afterShared afterAccess afterTag : State)
    (bank : Bank) (pstate : ProcState) (rn : Fin 31) (rt : Fin 32)
    (offset converted : BitVec 64) (nv big : Bool)
    (desc : AddressDescriptor) (access : AccessDescriptor)
    (featureRun : (featurePrefix boundaries).run state = .ok () afterFeature)
    (bankPresent : afterFeature.regs.get? Register._R = some bank)
    (pstatePresent : afterFeature.regs.get? Register.PSTATE = some pstate)
    (nvRun : (memory.HaveNV2Ext ()).run (syndromeState afterFeature pstate rt) = .ok nv afterNV)
    (endianRun : (memory.BigEndian ()).run afterNV = .ok big afterEndian)
    (conversionRun : (endianStep memory big (xValue bank rt)).run afterEndian = .ok converted afterConversion)
    (alignmentRun : (memory.AArch64_CheckAlignment (bank[rn.val] + offset) 8 .AccType_NORMAL true).run
      afterConversion = .ok true afterAlignment)
    (alignRun : (memory.Align__1 (bank[rn.val] + offset) 8).run afterAlignment =
      .ok (bank[rn.val] + offset) afterAlign)
    (translationRun : (single.AArch64_TranslateAddress (bank[rn.val] + offset) .AccType_NORMAL true true 8).run
      afterAlign = .ok desc afterTranslate)
    (faultRun : (faultStep single (bank[rn.val] + offset) desc).run afterTranslate = .ok () afterFault)
    (sharedRun : (sharedStep single desc).run afterFault = .ok () afterShared)
    (accessRun : (single.CreateAccessDescriptor .AccType_NORMAL).run afterShared = .ok access afterAccess)
    (tagRun : (tagStep boundaries single (bank[rn.val] + offset) desc).run afterAccess = .ok () afterTag) :
    (memory_single_general_immediate_signed_postidx
      (bindMemory boundaries (bindMemSingle boundaries memory single)) .AccType_NORMAL 64
      .MemOp_STORE rn.val offset false 64 false rt.val false).run state =
      (single.aset__Mem desc 8 access converted).run afterTag := by
  rw [MemoryBridge.str64_aligned_run boundaries (bindMemSingle boundaries memory single)
    state afterFeature afterNV afterEndian afterConversion afterAlignment bank pstate rn rt
    offset converted nv big featureRun bankPresent pstatePresent nvRun endianRun conversionRun alignmentRun,
    bindMemSingle64]
  exact aligned64_run boundaries memory single afterAlignment afterAlign afterTranslate
    afterFault afterShared afterAccess afterTag (bank[rn.val] + offset) converted true desc access
    alignRun translationRun faultRun sharedRun accessRun tagRun

namespace Examples

-- Nonarchitectural test callbacks: never used as implementations of Arm.
private def poison {α : Type} : SailM α := fun state => .error .Unreachable state

private def mark (state : State) (label : String) : State :=
  { state with sailOutput := state.sailOutput.push label }

private def empty : State :=
  { regs := ∅, choiceState := (), mem := ∅, tags := (), cycleCount := 0, sailOutput := #[] }

private def va : BitVec 64 := 0xffff000000001000#64

private def desc : AddressDescriptor :=
  { fault := { (default : FaultRecord) with
      typ := .Fault_Permission
      level := -1
      ipaddress := { address := 0x9876#52, NS := 1#1 } }
    memattrs := { (default : MemoryAttributes) with shareable := true, tagged := true, outershareable := true }
    paddress := { address := 0x5000#52, NS := 1#1 }
    vaddress := va }

private def access : AccessDescriptor :=
  { (default : AccessDescriptor) with
    mpam := { mpam_ns := 1#1, partid := 0xbeef#16, pmg := 0x42#8 }
    page_table_walk := true
    secondstage := true
    s2fs1walk := true
    level := 2 }

private def boundaries : Boundaries :=
  { HaveMTEExt := fun _ state => .ok true (mark state "mte")
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
    ZeroExtend__0 := fun {width} value size state =>
      if value == va.setWidth width && size == 64 then
        .ok (BitVec.ofNat size.toNat state.cycleCount)
          { (mark state "extend") with cycleCount := state.cycleCount + 1 }
      else .error .Unreachable state }

private def memory : MemoryBoundaries :=
  { HaveNV2Ext := fun _ => poison
    BigEndian := fun _ => poison
    BigEndianReverse := fun _ => poison
    AArch64_CheckAlignment := fun _ _ _ _ => poison
    Align__1 := fun value _ state => .ok value (mark state "align")
    AArch64_aset_MemSingle := fun _ _ _ _ _ => poison }

private def single : MemSingleBoundaries :=
  { AArch64_TranslateAddress := fun address acctype iswrite wasaligned size state =>
      if address == va && acctype == .AccType_NORMAL && iswrite && wasaligned && size == 8 then
        .ok desc (mark state "translate") else .error .Unreachable state
    AArch64_Abort := fun address fault state =>
      if address == va && fault == desc.fault then .ok () (mark state "abort")
      else .error .Unreachable state
    ProcessorID := fun _ state => .ok 7 (mark state "pid")
    ClearExclusiveByAddress := fun paddress processor size state =>
      if paddress == desc.paddress && processor == 7 && size == 8 then
        .ok () (mark state "clear") else .error .Unreachable state
    CreateAccessDescriptor := fun acctype state =>
      if acctype == .AccType_NORMAL then .ok access (mark state "access")
      else .error .Unreachable state
    AccessIsTagChecked := fun address acctype state =>
      if address == 0#64 && acctype == .AccType_NORMAL then
        .ok true (mark state "tag_access") else .error .Unreachable state
    TransformTag := fun address state =>
      if address == 1#64 then .ok (0xa#4) (mark state "transform")
      else .error .Unreachable state
    CheckTag := fun descriptor tag iswrite state =>
      if descriptor == desc && tag == 0xa#4 && iswrite then
        .ok false (mark state "check") else .error .Unreachable state
    TagCheckFail := fun address iswrite state =>
      if address == 2#64 && iswrite then .ok () (mark state "tag_fail")
      else .error .Unreachable state
    aset__Mem := fun descriptor size acc data state =>
      if descriptor == desc && size == 8 && acc == access && data == BitVec.ofNat (8 * size) 0x1234 then
        .error (.User (.Error_SError true))
          { (mark state "mem") with mem := state.mem.insert descriptor.paddress.address.toNat (0x34#8) }
      else .error .Unreachable state }

/-- Non-return must be proved, not inferred from a fault flag: both Abort and
TagCheckFail return here, so the original body reaches _Mem. NS and all supplied
descriptor fields survive; three extension calls produce different addresses;
the final write-then-error preserves its entire resulting state. -/
theorem returning_faults_reach_memory :
    (AArch64_aset_MemSingle boundaries memory single va 8 .AccType_NORMAL true (0x1234#64)).run empty =
      .error (.User (.Error_SError true))
        { empty with
          mem := empty.mem.insert 0x5000 (0x34#8)
          cycleCount := 3
          sailOutput := #["align", "translate", "abort", "pid", "clear", "access", "mte",
            "extend", "tag_access", "extend", "transform", "check", "extend", "tag_fail", "mem"] } := by
  rfl

private def aborting : MemSingleBoundaries :=
  { single with
    AArch64_Abort := fun _ _ state =>
      .error (.User (.Error_ExceptionTaken ())) (mark state "abort_error") }

theorem abort_error_stops_before_exclusives :
    (AArch64_aset_MemSingle boundaries memory aborting va 8 .AccType_NORMAL true (0x1234#64)).run empty =
      .error (.User (.Error_ExceptionTaken ()))
        { empty with sailOutput := #["align", "translate", "abort_error"] } := by
  rfl

private def tagFailing : MemSingleBoundaries :=
  { single with
    TagCheckFail := fun _ _ state =>
      .error (.User (.Error_ExceptionTaken ())) (mark state "tag_error") }

theorem tag_error_stops_before_memory :
    (AArch64_aset_MemSingle boundaries memory tagFailing va 8 .AccType_NORMAL true (0x1234#64)).run empty =
      .error (.User (.Error_ExceptionTaken ()))
        { empty with
          cycleCount := 3
          sailOutput := #["align", "translate", "abort", "pid", "clear", "access", "mte",
            "extend", "tag_access", "extend", "transform", "check", "extend", "tag_error"] } := by
  rfl

end Examples

/-- info: 'STRExecution.MemSingleBridge.aligned64_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aligned64_factorization
/-- info: 'STRExecution.MemSingleBridge.aligned64_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aligned64_run
/-- info: 'STRExecution.MemSingleBridge.alignment_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignment_assertion
/-- info: 'STRExecution.MemSingleBridge.tag_checked_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tag_checked_run
/-- info: 'STRExecution.MemSingleBridge.Examples.returning_faults_reach_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.returning_faults_reach_memory
/-- info: 'STRExecution.MemSingleBridge.Examples.abort_error_stops_before_exclusives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.abort_error_stops_before_exclusives
/-- info: 'STRExecution.MemSingleBridge.Examples.tag_error_stops_before_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.tag_error_stops_before_memory
/-- info: 'STRExecution.MemSingleBridge.str64_to_mem_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms str64_to_mem_run

end STRExecution.MemSingleBridge
