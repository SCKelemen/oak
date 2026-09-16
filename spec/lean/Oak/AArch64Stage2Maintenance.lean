import Oak.AArch64Barrier

/-!
# AArch64 stage-2 maintenance projection

This module states a deliberately restricted, per-old-event BBM-shaped local
projection corresponding to the Arm CAT model's `BBM` relation. It proves the
shape contributed by DSB ISH-classified occurrences around a TLBI occurrence.
Event classification, `ca`,
`inv-scope`, architectural completion, and the decision that an update requires
break-before-make remain inputs from the architecture refinement.
-/

namespace Oak.AArch64Stage2Maintenance

open Oak.AArch64Barrier
open Oak.AArch64Encoding

/-- The two translation-table-descriptor event classes used by CAT's `BBM`
    definition. This is an event classification, not a descriptor decoder. -/
inductive TTDClass where
  | tlbCacheable
  | tlbUncacheable
  deriving DecidableEq, Repr

/-- CAT may classify the old cacheable TTD through an implicit table walk; the
    break and make occurrences in Oak's maintenance sequence are explicit
    descriptor writes. -/
inductive DescriptorAccess where
  | implicitRead
  | explicitWrite
  deriving DecidableEq, Repr

/-- The event vocabulary needed by the restricted stage-2 projection. `Target`
    remains abstract because IPA, VMID, regime, and shareability matching have
    not yet been refined from Oak values into Arm invalidation semantics. -/
inductive Action (Target : Type) where
  | descriptor (slot : Nat) (access : DescriptorAccess) (ttdClass : TTDClass)
  | barrier (decode : BarrierDecode)
  | tlbi (target : Target)

/-- Primitive event facts supplied by an occurrence-indexed Arm execution.
    `coherenceAfter` and `invScope` are assumed projections of CAT's `ca` and
    `inv-scope` relations, respectively. -/
structure Trace (Occurrence Target : Type) where
  action : Occurrence → Action Target
  po : Occurrence → Occurrence → Prop
  coherenceAfter : Occurrence → Occurrence → Prop
  invScope : Occurrence → Occurrence → Prop

/-- A decoded full DSB occurrence between two events in program order. The
    name says ordering only: this structure does not assert architectural
    completion. -/
structure FullDsbOrderingBetween {Occurrence Target : Type}
    (trace : Trace Occurrence Target) (decode : BarrierDecode)
    (before dsb after : Occurrence) : Prop where
  ordersBefore : decodeDsbOrdersBefore decode
  barrierIsExact : trace.action dsb = .barrier decode
  beforeDsb : trace.po before dsb
  dsbAfter : trace.po dsb after

/-- The least local ordered-before fragment needed for the projected stage-2
    BBM skeleton. The direct constructors correspond to the relevant
    descriptor/TLBI instances of CAT's full `DSB-ob` arm; transitivity
    corresponds to the `ob; ob` arm. A separate refinement must connect these
    constructors to an actual CAT execution. -/
inductive ProjectedOrderedBefore {Occurrence Target : Type}
    (trace : Trace Occurrence Target) : Occurrence → Occurrence → Prop where
  | descriptorWriteBeforeTlbi
      {before dsb after : Occurrence} {slot : Nat} {ttdClass : TTDClass}
      {target : Target} {decode : BarrierDecode}
      (beforeIsWrite : trace.action before =
        .descriptor slot .explicitWrite ttdClass)
      (afterIsTlbi : trace.action after = .tlbi target)
      (barrier : FullDsbOrderingBetween trace decode before dsb after) :
      ProjectedOrderedBefore trace before after
  | tlbiBeforeDescriptorWrite
      {before dsb after : Occurrence} {slot : Nat} {ttdClass : TTDClass}
      {target : Target} {decode : BarrierDecode}
      (beforeIsTlbi : trace.action before = .tlbi target)
      (afterIsWrite : trace.action after =
        .descriptor slot .explicitWrite ttdClass)
      (barrier : FullDsbOrderingBetween trace decode before dsb after) :
      ProjectedOrderedBefore trace before after
  | trans {a b c : Occurrence}
      (ab : ProjectedOrderedBefore trace a b)
      (bc : ProjectedOrderedBefore trace b c) :
      ProjectedOrderedBefore trace a c

/-- The seven operands of the pinned CAT definition

`[TLBCacheableTTD]; ca; [TLBUncacheableTTD]; ob; [TLBI];
 (ob & inv-scope); [TLBCacheableTTD]`

for one old descriptor event and one make event. -/
structure ProjectedBBMWitness {Occurrence Target : Type}
    (trace : Trace Occurrence Target) (old make : Occurrence)
    (slot : Nat) (oldAccess : DescriptorAccess) (target : Target)
    (breakEvent tlbiEvent : Occurrence) : Prop where
  oldIsCacheableTTD : trace.action old =
    .descriptor slot oldAccess .tlbCacheable
  oldCoherenceBeforeBreak : trace.coherenceAfter old breakEvent
  breakIsUncacheableTTD : trace.action breakEvent =
    .descriptor slot .explicitWrite .tlbUncacheable
  breakBeforeTlbi : ProjectedOrderedBefore trace breakEvent tlbiEvent
  tlbiHasTarget : trace.action tlbiEvent = .tlbi target
  tlbiBeforeMake : ProjectedOrderedBefore trace tlbiEvent make
  tlbiInScopeForMake : trace.invScope tlbiEvent make
  makeIsCacheableTTD : trace.action make =
    .descriptor slot .explicitWrite .tlbCacheable

def ProjectedBBM {Occurrence Target : Type}
    (trace : Trace Occurrence Target) (old make : Occurrence) : Prop :=
  ∃ (slot : Nat) (oldAccess : DescriptorAccess) (target : Target)
    (breakEvent tlbiEvent : Occurrence),
    ProjectedBBMWitness trace old make slot oldAccess target breakEvent tlbiEvent

/-- Concrete occurrence witnesses for Oak's restricted DSB-ISH/TLBI/DSB-ISH
    sequence. No field is a completion or visibility assertion. -/
structure DsbIshBbmSequenceWitness {Occurrence Target : Type}
    (trace : Trace Occurrence Target) (old make : Occurrence)
    (slot : Nat) (oldAccess : DescriptorAccess) (target : Target)
    (breakEvent preTlbiDsb tlbiEvent postTlbiDsb : Occurrence) : Prop where
  oldIsCacheableTTD : trace.action old =
    .descriptor slot oldAccess .tlbCacheable
  oldCoherenceBeforeBreak : trace.coherenceAfter old breakEvent
  breakIsUncacheableTTD : trace.action breakEvent =
    .descriptor slot .explicitWrite .tlbUncacheable
  preTlbiDsbIsExact : trace.action preTlbiDsb = .barrier dsbIshDecode
  tlbiHasTarget : trace.action tlbiEvent = .tlbi target
  postTlbiDsbIsExact : trace.action postTlbiDsb = .barrier dsbIshDecode
  makeIsCacheableTTD : trace.action make =
    .descriptor slot .explicitWrite .tlbCacheable
  breakBeforePreTlbiDsb : trace.po breakEvent preTlbiDsb
  preTlbiDsbBeforeTlbi : trace.po preTlbiDsb tlbiEvent
  tlbiBeforePostTlbiDsb : trace.po tlbiEvent postTlbiDsb
  postTlbiDsbBeforeMake : trace.po postTlbiDsb make
  tlbiInScopeForMake : trace.invScope tlbiEvent make

def DsbIshBbmSequence {Occurrence Target : Type}
    (trace : Trace Occurrence Target) (old make : Occurrence) : Prop :=
  ∃ (slot : Nat) (oldAccess : DescriptorAccess) (target : Target)
    (breakEvent preTlbiDsb tlbiEvent postTlbiDsb : Occurrence),
    DsbIshBbmSequenceWitness trace old make slot oldAccess target breakEvent
      preTlbiDsb tlbiEvent postTlbiDsb

/-- DSB ISH-classified occurrences on both sides of TLBI construct the two
    local edges corresponding to the `ob` operands in CAT's per-old-event
    `BBM` skeleton. -/
theorem dsb_ish_sequence_projects_bbm
    {Occurrence Target : Type} {trace : Trace Occurrence Target}
    {old make : Occurrence}
    (sequence : DsbIshBbmSequence trace old make) :
    ProjectedBBM trace old make := by
  rcases sequence with
    ⟨slot, oldAccess, target, breakEvent, preTlbiDsb, tlbiEvent,
      postTlbiDsb, sequence⟩
  have breakBeforeTlbi :
      ProjectedOrderedBefore trace breakEvent tlbiEvent :=
    .descriptorWriteBeforeTlbi
      sequence.breakIsUncacheableTTD sequence.tlbiHasTarget
      { ordersBefore := dsb_ish_decode_orders_before
        barrierIsExact := sequence.preTlbiDsbIsExact
        beforeDsb := sequence.breakBeforePreTlbiDsb
        dsbAfter := sequence.preTlbiDsbBeforeTlbi }
  have tlbiBeforeMake :
      ProjectedOrderedBefore trace tlbiEvent make :=
    .tlbiBeforeDescriptorWrite
      sequence.tlbiHasTarget sequence.makeIsCacheableTTD
      { ordersBefore := dsb_ish_decode_orders_before
        barrierIsExact := sequence.postTlbiDsbIsExact
        beforeDsb := sequence.tlbiBeforePostTlbiDsb
        dsbAfter := sequence.postTlbiDsbBeforeMake }
  exact
    ⟨slot, oldAccess, target, breakEvent, tlbiEvent,
    { oldIsCacheableTTD := sequence.oldIsCacheableTTD
      oldCoherenceBeforeBreak := sequence.oldCoherenceBeforeBreak
      breakIsUncacheableTTD := sequence.breakIsUncacheableTTD
      breakBeforeTlbi := breakBeforeTlbi
      tlbiHasTarget := sequence.tlbiHasTarget
      tlbiBeforeMake := tlbiBeforeMake
      tlbiInScopeForMake := sequence.tlbiInScopeForMake
      makeIsCacheableTTD := sequence.makeIsCacheableTTD }⟩

/-- Conditional maintenance obligation for one old event. `requiresBBM` is an
    external classification; it is not silently equated with the full CAT
    `TTD-update-needsBBM` relation. -/
def MaintainsOldEvent {Occurrence Target : Type}
    (requiresBBM : Occurrence → Occurrence → Prop)
    (trace : Trace Occurrence Target) (old : Occurrence) : Prop :=
  ∀ make, requiresBBM old make → DsbIshBbmSequence trace old make

theorem maintains_old_event_covers_projected_bbm
    {Occurrence Target : Type} {requiresBBM : Occurrence → Occurrence → Prop}
    {trace : Trace Occurrence Target} {old : Occurrence}
    (maintains : MaintainsOldEvent requiresBBM trace old) :
    ∀ make, requiresBBM old make → ProjectedBBM trace old make := by
  intro make needsBBM
  exact dsb_ish_sequence_projects_bbm (maintains make needsBBM)

end Oak.AArch64Stage2Maintenance
