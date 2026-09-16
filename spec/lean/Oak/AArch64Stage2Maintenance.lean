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
  po_irrefl : ∀ event, ¬ po event event
  po_trans : ∀ {a b c}, po a b → po b c → po a c
  coherenceAfter : Occurrence → Occurrence → Prop
  invScope : Occurrence → Occurrence → Prop

/-- External projection from an execution occurrence to the instruction word
    at that occurrence. The static object regression test does not construct
    this projection; a compiler/execution refinement must supply it. -/
structure InstructionTrace (Occurrence : Type) where
  wordAt : Occurrence → Option (BitVec 32)

/-- The same occurrence is both the exact VMALLS12E1IS word and the TLBI event
    used by the abstract maintenance trace. The action equality remains an
    explicit refinement input: an encoding alone does not determine an
    architectural target, VMID, regime, scope, or execution effect. -/
structure Vmalls12e1isOccurrence {Occurrence Target : Type}
    (code : InstructionTrace Occurrence) (trace : Trace Occurrence Target)
    (event : Occurrence) (target : Target) : Prop where
  wordIsExact : code.wordAt event = some tlbiVmalls12e1is
  actionIsTlbi : trace.action event = .tlbi target

/-- The external occurrence projection exposes the independently proved exact
    numeric word; it does not add any execution semantics. -/
theorem vmalls12e1is_occurrence_has_exact_word
    {Occurrence Target : Type} {code : InstructionTrace Occurrence}
    {trace : Trace Occurrence Target} {event : Occurrence} {target : Target}
    (occurrence : Vmalls12e1isOccurrence code trace event target) :
    code.wordAt event = some 0xd50c83df#32 := by
  simpa [tlbi_vmalls12e1is_word] using occurrence.wordIsExact

/-- The action classification is exposed unchanged from the external
    refinement field; it is not inferred from the exact word. -/
theorem vmalls12e1is_occurrence_has_tlbi_action
    {Occurrence Target : Type} {code : InstructionTrace Occurrence}
    {trace : Trace Occurrence Target} {event : Occurrence} {target : Target}
    (occurrence : Vmalls12e1isOccurrence code trace event target) :
    trace.action event = .tlbi target :=
  occurrence.actionIsTlbi

/-- The local-PE VMALLS12E1 word cannot satisfy the exact Inner Shareable
    occurrence witness. This distinguishes the words only; it does not call
    the local instruction invalid. -/
theorem plain_vmalls12e1_word_cannot_witness_vmalls12e1is
    {Occurrence Target : Type} {code : InstructionTrace Occurrence}
    {trace : Trace Occurrence Target} {event : Occurrence} {target : Target}
    (plainWordAt : code.wordAt event = some 0xd50c87df#32) :
    ¬ Vmalls12e1isOccurrence code trace event target := by
  intro occurrence
  have wordsEqual : 0xd50c87df#32 = tlbiVmalls12e1is :=
    Option.some.inj (plainWordAt.symm.trans occurrence.wordIsExact)
  have wordsDiffer : 0xd50c87df#32 ≠ tlbiVmalls12e1is := by native_decide
  exact wordsDiffer wordsEqual

/-- One barrier occurrence with independent instruction-word and abstract
    action projections. Neither projection is derived from the other. -/
structure ExactBarrierOccurrence {Occurrence Target : Type}
    (code : InstructionTrace Occurrence) (trace : Trace Occurrence Target)
    (event : Occurrence) (word : BitVec 32) (decode : BarrierDecode) : Prop where
  wordIsExact : code.wordAt event = some word
  actionIsBarrier : trace.action event = .barrier decode

/-- The exact instruction occurrences and program-order directions in Oak's
    fixed DSB ISH; VMALLS12E1IS; DSB ISH; ISB source slice. `po` does not mean
    immediate adjacency, and this structure contains no completion or context
    synchronization evidence. -/
structure Vmalls12e1isDsbIsbInstructionSequence
    {Occurrence Target : Type}
    (code : InstructionTrace Occurrence) (trace : Trace Occurrence Target)
    (target : Target)
    (preTlbiDsb tlbiEvent postTlbiDsb isbEvent : Occurrence) : Prop where
  preTlbiDsbIsExact : ExactBarrierOccurrence code trace preTlbiDsb
    dsbIsh dsbIshDecode
  tlbiIsExact : Vmalls12e1isOccurrence code trace tlbiEvent target
  postTlbiDsbIsExact : ExactBarrierOccurrence code trace postTlbiDsb
    dsbIsh dsbIshDecode
  isbIsExact : ExactBarrierOccurrence code trace isbEvent isbSy isbDecode
  preTlbiDsbBeforeTlbi : trace.po preTlbiDsb tlbiEvent
  tlbiBeforePostTlbiDsb : trace.po tlbiEvent postTlbiDsb
  postTlbiDsbBeforeIsb : trace.po postTlbiDsb isbEvent

/-- Strict, transitive program order makes the four selected occurrences
    pairwise distinct. This does not assert adjacency or exhaustiveness. -/
theorem vmalls12e1is_dsb_isb_occurrences_pairwise_distinct
    {Occurrence Target : Type}
    {code : InstructionTrace Occurrence} {trace : Trace Occurrence Target}
    {target : Target}
    {preTlbiDsb tlbiEvent postTlbiDsb isbEvent : Occurrence}
    (sequence : Vmalls12e1isDsbIsbInstructionSequence code trace target
      preTlbiDsb tlbiEvent postTlbiDsb isbEvent) :
    preTlbiDsb ≠ tlbiEvent ∧
      preTlbiDsb ≠ postTlbiDsb ∧
      preTlbiDsb ≠ isbEvent ∧
      tlbiEvent ≠ postTlbiDsb ∧
      tlbiEvent ≠ isbEvent ∧
      postTlbiDsb ≠ isbEvent := by
  have neOfPo : ∀ {a b}, trace.po a b → a ≠ b := by
    intro a b hPo hEq
    subst b
    exact trace.po_irrefl a hPo
  have preBeforePost : trace.po preTlbiDsb postTlbiDsb :=
    trace.po_trans sequence.preTlbiDsbBeforeTlbi
      sequence.tlbiBeforePostTlbiDsb
  have tlbiBeforeIsb : trace.po tlbiEvent isbEvent :=
    trace.po_trans sequence.tlbiBeforePostTlbiDsb
      sequence.postTlbiDsbBeforeIsb
  have preBeforeIsb : trace.po preTlbiDsb isbEvent :=
    trace.po_trans preBeforePost sequence.postTlbiDsbBeforeIsb
  exact ⟨neOfPo sequence.preTlbiDsbBeforeTlbi, neOfPo preBeforePost,
    neOfPo preBeforeIsb, neOfPo sequence.tlbiBeforePostTlbiDsb,
    neOfPo tlbiBeforeIsb, neOfPo sequence.postTlbiDsbBeforeIsb⟩

/-- External execution-level proposition that the selected post-DSB completes
    the selected TLBI. Decoder identity and the DSB capability Boolean do not
    construct this relation. -/
def PostDsbCompletes (Occurrence Target : Type) :=
  Trace Occurrence Target → Occurrence → Occurrence → Prop

/-- External execution-level context-synchronization proposition for this
    stage-2 trace. It is separate from the ISB decoder/capability record. -/
def Stage2ContextSync (Occurrence Target : Type) :=
  Trace Occurrence Target → Occurrence → Prop

/-- The exact ordered instruction slice plus the two external architectural
    facts needed to call it completing and context synchronizing. This is not a
    descriptor break-before-make witness. -/
structure CompletedVmalls12e1isContextSyncSequence
    {Occurrence Target : Type}
    (code : InstructionTrace Occurrence) (trace : Trace Occurrence Target)
    (postDsbCompletes : PostDsbCompletes Occurrence Target)
    (contextSync : Stage2ContextSync Occurrence Target)
    (target : Target)
    (preTlbiDsb tlbiEvent postTlbiDsb isbEvent : Occurrence) : Prop where
  instructionSequence : Vmalls12e1isDsbIsbInstructionSequence code trace
    target preTlbiDsb tlbiEvent postTlbiDsb isbEvent
  architecturalCompletion : postDsbCompletes trace tlbiEvent postTlbiDsb
  architecturalContextSync : contextSync trace isbEvent

theorem completed_vmalls12e1is_sequence_requires_completion
    {Occurrence Target : Type}
    {code : InstructionTrace Occurrence} {trace : Trace Occurrence Target}
    {postDsbCompletes : PostDsbCompletes Occurrence Target}
    {contextSync : Stage2ContextSync Occurrence Target}
    {target : Target}
    {preTlbiDsb tlbiEvent postTlbiDsb isbEvent : Occurrence}
    (sequence : CompletedVmalls12e1isContextSyncSequence code trace
      postDsbCompletes contextSync target preTlbiDsb tlbiEvent postTlbiDsb
      isbEvent) :
    postDsbCompletes trace tlbiEvent postTlbiDsb :=
  sequence.architecturalCompletion

theorem completed_vmalls12e1is_sequence_requires_context_sync
    {Occurrence Target : Type}
    {code : InstructionTrace Occurrence} {trace : Trace Occurrence Target}
    {postDsbCompletes : PostDsbCompletes Occurrence Target}
    {contextSync : Stage2ContextSync Occurrence Target}
    {target : Target}
    {preTlbiDsb tlbiEvent postTlbiDsb isbEvent : Occurrence}
    (sequence : CompletedVmalls12e1isContextSyncSequence code trace
      postDsbCompletes contextSync target preTlbiDsb tlbiEvent postTlbiDsb
      isbEvent) :
    contextSync trace isbEvent :=
  sequence.architecturalContextSync

/-- Exact words, ordering, and decoder records cannot bypass a refuted
    execution-level TLBI-completion proposition. -/
theorem no_completed_vmalls12e1is_sequence_when_completion_refuted
    {Occurrence Target : Type}
    {code : InstructionTrace Occurrence} {trace : Trace Occurrence Target}
    {postDsbCompletes : PostDsbCompletes Occurrence Target}
    {contextSync : Stage2ContextSync Occurrence Target}
    {target : Target}
    {preTlbiDsb tlbiEvent postTlbiDsb isbEvent : Occurrence}
    (refuted : ¬ postDsbCompletes trace tlbiEvent postTlbiDsb) :
    ¬ CompletedVmalls12e1isContextSyncSequence code trace postDsbCompletes
      contextSync target preTlbiDsb tlbiEvent postTlbiDsb isbEvent := by
  intro sequence
  exact refuted sequence.architecturalCompletion

/-- Exact words, ordering, and decoder records likewise cannot bypass a
    refuted execution-level context-synchronization proposition. -/
theorem no_completed_vmalls12e1is_sequence_when_context_sync_refuted
    {Occurrence Target : Type}
    {code : InstructionTrace Occurrence} {trace : Trace Occurrence Target}
    {postDsbCompletes : PostDsbCompletes Occurrence Target}
    {contextSync : Stage2ContextSync Occurrence Target}
    {target : Target}
    {preTlbiDsb tlbiEvent postTlbiDsb isbEvent : Occurrence}
    (refuted : ¬ contextSync trace isbEvent) :
    ¬ CompletedVmalls12e1isContextSyncSequence code trace postDsbCompletes
      contextSync target preTlbiDsb tlbiEvent postTlbiDsb isbEvent := by
  intro sequence
  exact refuted sequence.architecturalContextSync

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

/-- The exact TLBI, post-DSB, and ISB occurrences in Oak's restricted local
    projection corresponding to the first pinned `DSB-ob` arm. Official CAT
    set membership and the arm's destination filter remain execution-refinement
    premises, and this is ordering rather than architectural completion. -/
structure ProjectedTlbiDsbOb {Occurrence Target : Type}
    (code : InstructionTrace Occurrence) (trace : Trace Occurrence Target)
    (target : Target) (tlbiEvent postTlbiDsb isbEvent : Occurrence) : Prop where
  tlbiIsExact : Vmalls12e1isOccurrence code trace tlbiEvent target
  postTlbiDsbIsExact : ExactBarrierOccurrence code trace postTlbiDsb
    dsbIsh dsbIshDecode
  isbIsExact : ExactBarrierOccurrence code trace isbEvent isbSy isbDecode
  ordering : FullDsbOrderingBetween trace dsbIshDecode tlbiEvent postTlbiDsb
    isbEvent

/-- Oak's restricted local projection corresponding to the exact
    `DSB-ob; [IFB]; po` arm of the pinned `IFB-ob` definition. A following
    occurrence and its program-order edge are explicit inputs; official CAT
    membership remains external and the witness does not assert that ISB has
    synchronized architectural context. -/
structure ProjectedTlbiIfbOb {Occurrence Target : Type}
    (code : InstructionTrace Occurrence) (trace : Trace Occurrence Target)
    (target : Target)
    (tlbiEvent postTlbiDsb isbEvent afterEvent : Occurrence) : Prop where
  dsbOb : ProjectedTlbiDsbOb code trace target tlbiEvent postTlbiDsb isbEvent
  isbBeforeAfter : trace.po isbEvent afterEvent

/-- Oak's exact fixed instruction slice supplies the local TLBI-to-ISB
    ordering projection corresponding to `DSB-ob`, without manufacturing CAT
    event membership or completion. -/
theorem vmalls12e1is_dsb_isb_sequence_projects_dsb_ob
    {Occurrence Target : Type}
    {code : InstructionTrace Occurrence} {trace : Trace Occurrence Target}
    {target : Target}
    {preTlbiDsb tlbiEvent postTlbiDsb isbEvent : Occurrence}
    (sequence : Vmalls12e1isDsbIsbInstructionSequence code trace target
      preTlbiDsb tlbiEvent postTlbiDsb isbEvent) :
    ProjectedTlbiDsbOb code trace target tlbiEvent postTlbiDsb isbEvent :=
  { tlbiIsExact := sequence.tlbiIsExact
    postTlbiDsbIsExact := sequence.postTlbiDsbIsExact
    isbIsExact := sequence.isbIsExact
    ordering :=
      { ordersBefore := dsb_ish_decode_orders_before
        barrierIsExact := sequence.postTlbiDsbIsExact.actionIsBarrier
        beforeDsb := sequence.tlbiBeforePostTlbiDsb
        dsbAfter := sequence.postTlbiDsbBeforeIsb } }

/-- With an explicit event after the ISB, the same sequence constructs Oak's
    local projection corresponding to CAT's `DSB-ob; [IFB]; po` ordering arm. -/
theorem vmalls12e1is_dsb_isb_sequence_projects_ifb_ob
    {Occurrence Target : Type}
    {code : InstructionTrace Occurrence} {trace : Trace Occurrence Target}
    {target : Target}
    {preTlbiDsb tlbiEvent postTlbiDsb isbEvent afterEvent : Occurrence}
    (sequence : Vmalls12e1isDsbIsbInstructionSequence code trace target
      preTlbiDsb tlbiEvent postTlbiDsb isbEvent)
    (isbBeforeAfter : trace.po isbEvent afterEvent) :
    ProjectedTlbiIfbOb code trace target tlbiEvent postTlbiDsb isbEvent
      afterEvent :=
  { dsbOb := vmalls12e1is_dsb_isb_sequence_projects_dsb_ob sequence
    isbBeforeAfter := isbBeforeAfter }

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

/-- A projected BBM witness retaining the exact instruction projection for the
    same TLBI occurrence and target selected by the abstract witness. -/
def ConcreteProjectedBBM {Occurrence Target : Type}
    (code : InstructionTrace Occurrence) (trace : Trace Occurrence Target)
    (old make : Occurrence) : Prop :=
  ∃ (slot : Nat) (oldAccess : DescriptorAccess) (target : Target)
    (breakEvent tlbiEvent : Occurrence),
    ProjectedBBMWitness trace old make slot oldAccess target breakEvent tlbiEvent ∧
      Vmalls12e1isOccurrence code trace tlbiEvent target

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

/-- The four chained program-order links make the break, two barriers,
    TLBI, and make occurrences pairwise distinct. The old descriptor event is
    deliberately absent: `coherenceAfter` has no irreflexivity premise. -/
theorem dsb_ish_bbm_sequence_occurrences_pairwise_distinct
    {Occurrence Target : Type} {trace : Trace Occurrence Target}
    {old make breakEvent preTlbiDsb tlbiEvent postTlbiDsb : Occurrence}
    {slot : Nat} {oldAccess : DescriptorAccess} {target : Target}
    (sequence : DsbIshBbmSequenceWitness trace old make slot oldAccess target
      breakEvent preTlbiDsb tlbiEvent postTlbiDsb) :
    breakEvent ≠ preTlbiDsb ∧
      breakEvent ≠ tlbiEvent ∧
      breakEvent ≠ postTlbiDsb ∧
      breakEvent ≠ make ∧
      preTlbiDsb ≠ tlbiEvent ∧
      preTlbiDsb ≠ postTlbiDsb ∧
      preTlbiDsb ≠ make ∧
      tlbiEvent ≠ postTlbiDsb ∧
      tlbiEvent ≠ make ∧
      postTlbiDsb ≠ make := by
  have neOfPo : ∀ {a b}, trace.po a b → a ≠ b := by
    intro a b hPo hEq
    subst b
    exact trace.po_irrefl a hPo
  have breakBeforeTlbi : trace.po breakEvent tlbiEvent :=
    trace.po_trans sequence.breakBeforePreTlbiDsb
      sequence.preTlbiDsbBeforeTlbi
  have breakBeforePost : trace.po breakEvent postTlbiDsb :=
    trace.po_trans breakBeforeTlbi sequence.tlbiBeforePostTlbiDsb
  have breakBeforeMake : trace.po breakEvent make :=
    trace.po_trans breakBeforePost sequence.postTlbiDsbBeforeMake
  have preBeforePost : trace.po preTlbiDsb postTlbiDsb :=
    trace.po_trans sequence.preTlbiDsbBeforeTlbi
      sequence.tlbiBeforePostTlbiDsb
  have preBeforeMake : trace.po preTlbiDsb make :=
    trace.po_trans preBeforePost sequence.postTlbiDsbBeforeMake
  have tlbiBeforeMake : trace.po tlbiEvent make :=
    trace.po_trans sequence.tlbiBeforePostTlbiDsb
      sequence.postTlbiDsbBeforeMake
  exact ⟨neOfPo sequence.breakBeforePreTlbiDsb, neOfPo breakBeforeTlbi,
    neOfPo breakBeforePost, neOfPo breakBeforeMake,
    neOfPo sequence.preTlbiDsbBeforeTlbi, neOfPo preBeforePost,
    neOfPo preBeforeMake, neOfPo sequence.tlbiBeforePostTlbiDsb,
    neOfPo tlbiBeforeMake, neOfPo sequence.postTlbiDsbBeforeMake⟩

/-- The ordering witness plus exact instruction-word/action witnesses at the
    same two DSB indices and TLBI index. It still contains no completion,
    visibility, or instruction-to-action derivation. -/
structure ConcreteDsbIshBbmSequenceWitness {Occurrence Target : Type}
    (code : InstructionTrace Occurrence) (trace : Trace Occurrence Target)
    (old make : Occurrence) (slot : Nat) (oldAccess : DescriptorAccess)
    (target : Target)
    (breakEvent preTlbiDsb tlbiEvent postTlbiDsb : Occurrence) : Prop where
  ordering : DsbIshBbmSequenceWitness trace old make slot oldAccess target
    breakEvent preTlbiDsb tlbiEvent postTlbiDsb
  preTlbiDsbIsExact : ExactBarrierOccurrence code trace preTlbiDsb
    dsbIsh dsbIshDecode
  tlbiIsExact : Vmalls12e1isOccurrence code trace tlbiEvent target
  postTlbiDsbIsExact : ExactBarrierOccurrence code trace postTlbiDsb
    dsbIsh dsbIshDecode

def DsbIshBbmSequence {Occurrence Target : Type}
    (trace : Trace Occurrence Target) (old make : Occurrence) : Prop :=
  ∃ (slot : Nat) (oldAccess : DescriptorAccess) (target : Target)
    (breakEvent preTlbiDsb tlbiEvent postTlbiDsb : Occurrence),
    DsbIshBbmSequenceWitness trace old make slot oldAccess target breakEvent
      preTlbiDsb tlbiEvent postTlbiDsb

/-- The concrete sequence wrapper retains external exact-word projections for
    both DSB occurrences and the same TLBI occurrence/target as the ordering
    witness. -/
def ConcreteDsbIshBbmSequence {Occurrence Target : Type}
    (code : InstructionTrace Occurrence) (trace : Trace Occurrence Target)
    (old make : Occurrence) : Prop :=
  ∃ (slot : Nat) (oldAccess : DescriptorAccess) (target : Target)
    (breakEvent preTlbiDsb tlbiEvent postTlbiDsb : Occurrence),
    ConcreteDsbIshBbmSequenceWitness code trace old make slot oldAccess target
      breakEvent preTlbiDsb tlbiEvent postTlbiDsb

/-- The indexed sequence witness constructs the indexed projected witness
    without changing the selected TLBI occurrence or target. -/
theorem dsb_ish_sequence_witness_projects_bbm_witness
    {Occurrence Target : Type} {trace : Trace Occurrence Target}
    {old make breakEvent preTlbiDsb tlbiEvent postTlbiDsb : Occurrence}
    {slot : Nat} {oldAccess : DescriptorAccess} {target : Target}
    (sequence : DsbIshBbmSequenceWitness trace old make slot oldAccess target
      breakEvent preTlbiDsb tlbiEvent postTlbiDsb) :
    ProjectedBBMWitness trace old make slot oldAccess target breakEvent
      tlbiEvent := by
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
    { oldIsCacheableTTD := sequence.oldIsCacheableTTD
      oldCoherenceBeforeBreak := sequence.oldCoherenceBeforeBreak
      breakIsUncacheableTTD := sequence.breakIsUncacheableTTD
      breakBeforeTlbi := breakBeforeTlbi
      tlbiHasTarget := sequence.tlbiHasTarget
      tlbiBeforeMake := tlbiBeforeMake
      tlbiInScopeForMake := sequence.tlbiInScopeForMake
      makeIsCacheableTTD := sequence.makeIsCacheableTTD }

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
  exact
    ⟨slot, oldAccess, target, breakEvent, tlbiEvent,
      dsb_ish_sequence_witness_projects_bbm_witness sequence⟩

/-- The exact VMALLS12E1IS occurrence is retained at the same event and target
    while the DSB-ISH sequence is projected to the local BBM skeleton. This
    theorem derives no target suitability, invalidation scope, completion, or
    context synchronization fact. -/
theorem concrete_vmalls12e1is_sequence_projects_bbm
    {Occurrence Target : Type} {code : InstructionTrace Occurrence}
    {trace : Trace Occurrence Target} {old make : Occurrence}
    (sequence : ConcreteDsbIshBbmSequence code trace old make) :
    ConcreteProjectedBBM code trace old make := by
  rcases sequence with
    ⟨slot, oldAccess, target, breakEvent, preTlbiDsb, tlbiEvent,
      postTlbiDsb, sequence⟩
  exact
    ⟨slot, oldAccess, target, breakEvent, tlbiEvent,
      dsb_ish_sequence_witness_projects_bbm_witness sequence.ordering,
      sequence.tlbiIsExact⟩

/-- The exact two DSB ISH words and exact VMALLS12E1IS word are tied to the
    same occurrence indices as the retained BBM ordering witness. This exposes
    static occurrence projections, not barrier completion or TLBI effects. -/
theorem concrete_dsb_ish_bbm_sequence_has_exact_words
    {Occurrence Target : Type} {code : InstructionTrace Occurrence}
    {trace : Trace Occurrence Target} {old make : Occurrence}
    (sequence : ConcreteDsbIshBbmSequence code trace old make) :
    ∃ (slot : Nat) (oldAccess : DescriptorAccess) (target : Target)
      (breakEvent preTlbiDsb tlbiEvent postTlbiDsb : Occurrence),
      DsbIshBbmSequenceWitness trace old make slot oldAccess target breakEvent
          preTlbiDsb tlbiEvent postTlbiDsb ∧
        code.wordAt preTlbiDsb = some 0xd5033b9f#32 ∧
        code.wordAt tlbiEvent = some 0xd50c83df#32 ∧
        code.wordAt postTlbiDsb = some 0xd5033b9f#32 := by
  rcases sequence with
    ⟨slot, oldAccess, target, breakEvent, preTlbiDsb, tlbiEvent,
      postTlbiDsb, sequence⟩
  exact
    ⟨slot, oldAccess, target, breakEvent, preTlbiDsb, tlbiEvent,
      postTlbiDsb, sequence.ordering,
      by simpa [dsb_ish_word] using sequence.preTlbiDsbIsExact.wordIsExact,
      by simpa [tlbi_vmalls12e1is_word] using sequence.tlbiIsExact.wordIsExact,
      by simpa [dsb_ish_word] using sequence.postTlbiDsbIsExact.wordIsExact⟩

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

/-- The pair-membership shape of CAT's `Warning-BBM-expected` diagnostic:
    a descriptor update classified as needing BBM but absent from BBM. The two
    relations remain parameters because this module does not model the full
    CAT event vocabulary or establish the required refinement maps. -/
def ProjectedCATBBMWarning {Occurrence : Type}
    (catNeedsBBM catBBM : Occurrence → Occurrence → Prop) : Prop :=
  ∃ old make, catNeedsBBM old make ∧ ¬catBBM old make

/-- If every old event is maintained, CAT-needs membership is covered by the
    local requirement, and every local projected witness is sound for CAT BBM,
    then the projected shape of the official warning is empty. The premises
    are explicit refinement obligations, not consequences of this theorem;
    the official CAT construct is a flagged diagnostic, not a validity axiom. -/
theorem maintained_old_events_exclude_projected_cat_bbm_warning
    {Occurrence Target : Type}
    {catNeedsBBM catBBM localRequires : Occurrence → Occurrence → Prop}
    {trace : Trace Occurrence Target}
    (maintains : ∀ old, MaintainsOldEvent localRequires trace old)
    (needsProjects : ∀ old make, catNeedsBBM old make → localRequires old make)
    (projectedBBMSound : ∀ old make,
      ProjectedBBM trace old make → catBBM old make) :
    ¬ProjectedCATBBMWarning catNeedsBBM catBBM := by
  rintro ⟨old, make, needsBBM, lacksBBM⟩
  apply lacksBBM
  apply projectedBBMSound old make
  exact maintains_old_event_covers_projected_bbm
    (maintains old) make (needsProjects old make needsBBM)

end Oak.AArch64Stage2Maintenance
