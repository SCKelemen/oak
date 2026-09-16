import Oak.AArch64ControlTransfer
import Oak.AArch64Encoding
import Oak.AArch64EventControl
import Oak.AArch64SysReg

namespace Oak.AArch64ColdEntry

/-- Abstract stages of the cold-entry protocol. The model intentionally proves
    ordering/state progression, not the correctness of arbitrary register bit
    patterns supplied by the caller. -/
inductive Stage where
  | start
  | irqMasked
  | executionConfigured
  | stageTwoConfigured
  | timerConfigured
  | guestContextInstalled
  | synchronized
  | transferred
  deriving DecidableEq, Repr

/-- The stage graph alone. This relation proves protocol shape, but its ISB
    edge carries no architectural occurrence or synchronization evidence. -/
inductive ProtocolStep : Stage -> Stage -> Prop where
  | maskIrq : ProtocolStep .start .irqMasked
  | configureExecution : ProtocolStep .irqMasked .executionConfigured
  | configureStageTwo : ProtocolStep .executionConfigured .stageTwoConfigured
  | configureTimer : ProtocolStep .stageTwoConfigured .timerConfigured
  | installGuestContext : ProtocolStep .timerConfigured .guestContextInstalled
  | isb : ProtocolStep .guestContextInstalled .synchronized
  | eret : ProtocolStep .synchronized .transferred

/-- The eight context writes that must occur before cold-entry synchronization. -/
inductive RequiredWrite where
  | hcrEl2
  | vttbrEl2
  | vtcrEl2
  | cnthctlEl2
  | cntvoffEl2
  | spEl1
  | elrEl2
  | spsrEl2
  deriving DecidableEq, Repr

def RequiredWrite.reg : RequiredWrite -> AArch64SysReg.Reg
  | .hcrEl2 => .hcrEl2
  | .vttbrEl2 => .vttbrEl2
  | .vtcrEl2 => .vtcrEl2
  | .cnthctlEl2 => .cnthctlEl2
  | .cntvoffEl2 => .cntvoffEl2
  | .spEl1 => .spEl1
  | .elrEl2 => .elrEl2
  | .spsrEl2 => .spsrEl2

/-- The exact instruction word used by Oak for each projected cold-entry
    register write. -/
def RequiredWrite.word : RequiredWrite -> BitVec 32
  | .hcrEl2 => AArch64Encoding.msrHcrEl2X0
  | .vttbrEl2 => AArch64Encoding.msrVttbrEl2X1
  | .vtcrEl2 => AArch64Encoding.msrVtcrEl2X2
  | .cnthctlEl2 => AArch64Encoding.msrCnthctlEl2X3
  | .cntvoffEl2 => AArch64Encoding.msrCntvoffEl2X4
  | .spEl1 => AArch64Encoding.msrSpEl1X5
  | .elrEl2 => AArch64Encoding.msrElrEl2X6
  | .spsrEl2 => AArch64Encoding.msrSpsrEl2X7

/-- The source general-purpose register encoded in each exact word. -/
def RequiredWrite.rt : RequiredWrite -> BitVec 5
  | .hcrEl2 => 0#5
  | .vttbrEl2 => 1#5
  | .vtcrEl2 => 2#5
  | .cnthctlEl2 => 3#5
  | .cntvoffEl2 => 4#5
  | .spEl1 => 5#5
  | .elrEl2 => 6#5
  | .spsrEl2 => 7#5

/-- Zero-based position in the cold-entry register prefix. -/
def RequiredWrite.index : RequiredWrite -> Nat
  | .hcrEl2 => 0
  | .vttbrEl2 => 1
  | .vtcrEl2 => 2
  | .cnthctlEl2 => 3
  | .cntvoffEl2 => 4
  | .spEl1 => 5
  | .elrEl2 => 6
  | .spsrEl2 => 7

theorem RequiredWrite.index_injective : Function.Injective RequiredWrite.index := by
  intro a b h
  cases a <;> cases b <;> simp_all [RequiredWrite.index]

def registerWriteOrder : List RequiredWrite := [
  .hcrEl2, .vttbrEl2, .vtcrEl2, .cnthctlEl2,
  .cntvoffEl2, .spEl1, .elrEl2, .spsrEl2
]

def registerWriteWords : List (BitVec 32) :=
  registerWriteOrder.map RequiredWrite.word

theorem register_write_words_exact : registerWriteWords = [
    0xd51c1100#32, 0xd51c2101#32, 0xd51c2142#32, 0xd51ce103#32,
    0xd51ce064#32, 0xd51c4105#32, 0xd51c4026#32, 0xd51c4007#32
  ] := by native_decide

theorem register_write_rts_exact : registerWriteOrder.map RequiredWrite.rt = [
    0#5, 1#5, 2#5, 3#5, 4#5, 5#5, 6#5, 7#5
  ] := by native_decide

theorem register_write_indices_exact : registerWriteOrder.map RequiredWrite.index =
    [0, 1, 2, 3, 4, 5, 6, 7] := by decide

/- OAK_COLD_ENTRY_REGISTER_SEQUENCE_BEGIN -/
/-- The complete register-only native prefix starts with the IRQ-mask word and
    continues with the eight exact context-register writes. -/
def coldEntryRegisterPrefixWords : List (BitVec 32) :=
  AArch64Encoding.msrDaifSetIrq :: registerWriteWords

theorem cold_entry_register_prefix_words_exact : coldEntryRegisterPrefixWords = [
    0xd50342df#32,
    0xd51c1100#32, 0xd51c2101#32, 0xd51c2142#32, 0xd51ce103#32,
    0xd51ce064#32, 0xd51c4105#32, 0xd51c4026#32, 0xd51c4007#32
  ] := by native_decide
/- OAK_COLD_ENTRY_REGISTER_SEQUENCE_END -/

/-- The eight X-register values consumed by the projected sequence. -/
structure RegisterInputs where
  hcrEl2 : BitVec 64
  vttbrEl2 : BitVec 64
  vtcrEl2 : BitVec 64
  cnthctlEl2 : BitVec 64
  cntvoffEl2 : BitVec 64
  spEl1 : BitVec 64
  elrEl2 : BitVec 64
  spsrEl2 : BitVec 64
  deriving DecidableEq, Repr

/-- Only the architectural register components selected by the eight writes.
    This is deliberately not the complete Arm machine state. -/
structure ProjectedRegisterState where
  hcrEl2 : BitVec 64
  vttbrEl2 : BitVec 64
  vtcrEl2 : BitVec 32
  cnthctlEl2 : BitVec 32
  cntvoffEl2 : BitVec 64
  spEl1 : BitVec 64
  elrEl2 : BitVec 64
  spsrEl2 : BitVec 32
  deriving DecidableEq, Repr

/-- SCR_EL3 projections read by the official nested-virtualization predicates.
    They are semantically irrelevant at EL2 but remain explicit inputs. -/
structure RedirectInputs where
  scrNs : Bool
  scrEel2 : Bool
  deriving DecidableEq, Repr

/-- Apply one selected official component update at EL2. Predicate bits are
    derived from the current projected HCR_EL2, rather than supplied as
    unconstrained booleans. At EL2 every retained redirect predicate is false. -/
def applyRegisterWriteAtEL2 (redirect : RedirectInputs) (inputs : RegisterInputs)
    (state : ProjectedRegisterState) : RequiredWrite -> ProjectedRegisterState
  | .hcrEl2 =>
      { state with hcrEl2 :=
          (AArch64SysReg.writeHcrEl2Component .el2
            (state.hcrEl2.getLsbD 42) (state.hcrEl2.getLsbD 45)
            (state.hcrEl2.getLsbD 27) redirect.scrNs redirect.scrEel2
            state.hcrEl2 inputs.hcrEl2).value }
  | .vttbrEl2 =>
      { state with vttbrEl2 :=
          (AArch64SysReg.writeVttbrEl2Component .el2
            (state.hcrEl2.getLsbD 42) (state.hcrEl2.getLsbD 45)
            (state.hcrEl2.getLsbD 27) redirect.scrNs redirect.scrEel2
            state.vttbrEl2 inputs.vttbrEl2).value }
  | .vtcrEl2 =>
      { state with vtcrEl2 :=
          (AArch64SysReg.writeVtcrEl2Component .el2
            (state.hcrEl2.getLsbD 42) (state.hcrEl2.getLsbD 45)
            (state.hcrEl2.getLsbD 27) redirect.scrNs redirect.scrEel2
            state.vtcrEl2 inputs.vtcrEl2).value }
  | .cnthctlEl2 =>
      { state with cnthctlEl2 :=
          (AArch64SysReg.writeCnthctlEl2Component inputs.cnthctlEl2).value }
  | .cntvoffEl2 =>
      { state with cntvoffEl2 :=
          (AArch64SysReg.writeCntvoffEl2Component .el2
            (state.hcrEl2.getLsbD 42) (state.hcrEl2.getLsbD 45)
            (state.hcrEl2.getLsbD 27) redirect.scrNs redirect.scrEel2
            state.cntvoffEl2 inputs.cntvoffEl2).value }
  | .spEl1 =>
      { state with spEl1 :=
          (AArch64SysReg.writeSpEl1Component .el2
            (state.hcrEl2.getLsbD 42) (state.hcrEl2.getLsbD 45)
            (state.hcrEl2.getLsbD 27) redirect.scrNs redirect.scrEel2
            state.spEl1 inputs.spEl1).value }
  | .elrEl2 =>
      { state with elrEl2 :=
          (AArch64SysReg.writeElrEl2Component inputs.elrEl2).value }
  | .spsrEl2 =>
      { state with spsrEl2 :=
          (AArch64SysReg.writeSpsrEl2Component inputs.spsrEl2).value }

/-- Projected state plus the ordered writes that produced it. -/
structure ProjectedSequenceResult where
  state : ProjectedRegisterState
  log : List RequiredWrite
  deriving DecidableEq, Repr

def applyLoggedRegisterWriteAtEL2 (redirect : RedirectInputs)
    (inputs : RegisterInputs) (result : ProjectedSequenceResult)
    (write : RequiredWrite) : ProjectedSequenceResult :=
  { state := applyRegisterWriteAtEL2 redirect inputs result.state write
    log := result.log ++ [write] }

def installColdEntryRegistersAtEL2 (redirect : RedirectInputs)
    (inputs : RegisterInputs) (initial : ProjectedRegisterState) :
    ProjectedSequenceResult :=
  registerWriteOrder.foldl (applyLoggedRegisterWriteAtEL2 redirect inputs)
    { state := initial, log := [] }

/-- The ordered EL2 projection overwrites exactly the eight selected
    components, with the three architecturally 32-bit destinations truncated,
    and records the exact source order. -/
theorem install_cold_entry_registers_at_el2_exact
    (redirect : RedirectInputs) (inputs : RegisterInputs)
    (initial : ProjectedRegisterState) :
    installColdEntryRegistersAtEL2 redirect inputs initial = {
      state := {
        hcrEl2 := inputs.hcrEl2
        vttbrEl2 := inputs.vttbrEl2
        vtcrEl2 := inputs.vtcrEl2.setWidth 32
        cnthctlEl2 := inputs.cnthctlEl2.setWidth 32
        cntvoffEl2 := inputs.cntvoffEl2
        spEl1 := inputs.spEl1
        elrEl2 := inputs.elrEl2
        spsrEl2 := inputs.spsrEl2.setWidth 32 }
      log := registerWriteOrder } := by
  rfl

/-- The occurrence classes used by the verified cold-entry slice. A barrier is
    identified by its exact word, not by Oak's capability Boolean. -/
inductive Action where
  | pstateImmediate (op : AArch64EventControl.Operation)
      (word : BitVec 32) (operand : BitVec 4)
  | sysReg (op : AArch64SysReg.Operation) (reg : AArch64SysReg.Reg)
      (word : BitVec 32) (rt : BitVec 5)
  | barrier (word : BitVec 32)
  | controlTransfer (op : AArch64ControlTransfer.Operation) (word : BitVec 32)
  deriving DecidableEq, Repr

/-- An occurrence-indexed execution interface. The architecture refinement must
    supply the action projection and strict program order. -/
structure Trace (Occurrence : Type) where
  action : Occurrence -> Action
  po : Occurrence -> Occurrence -> Prop
  po_irrefl : ∀ e, ¬ po e e
  po_trans : ∀ {a b c}, po a b -> po b c -> po a c

/-- The external Arm execution/state proposition that certifies an occurrence
    as context synchronizing. The pure decoder and CAT ordering do not prove it. -/
def ArmContextSync (Occurrence : Type) := Trace Occurrence -> Occurrence -> Prop

/-- The exact first instruction in the evidence-bearing cold-entry path. This
    occurrence/action fact alone does not prove access admission or a runtime
    PSTATE transition. -/
structure IrqMaskWitness {Occurrence : Type} (trace : Trace Occurrence) where
  occurrence : Occurrence
  actionIsExact : trace.action occurrence =
    .pstateImmediate .daifSetIrq AArch64Encoding.msrDaifSetIrq 0b0010#4

/-- Exact cold-entry evidence: the retained IRQ-mask occurrence precedes all
    eight word/Rt/register actions, the writes are totally ordered by source
    position, every write precedes the same exact ISB word, and an external Arm
    model certifies that ISB occurrence as context synchronizing. -/
structure ContextSyncWitness {Occurrence : Type} (trace : Trace Occurrence)
    (armContextSync : ArmContextSync Occurrence) where
  irqMask : IrqMaskWitness trace
  writeOccurrence : RequiredWrite -> Occurrence
  isbOccurrence : Occurrence
  irqMaskBeforeWrites : ∀ write,
    trace.po irqMask.occurrence (writeOccurrence write)
  writesAreExact : ∀ write,
    trace.action (writeOccurrence write) =
      .sysReg .write write.reg write.word write.rt
  writesFollowRegisterOrder : ∀ a b, a.index < b.index ->
    trace.po (writeOccurrence a) (writeOccurrence b)
  writesBeforeIsb : ∀ write, trace.po (writeOccurrence write) isbOccurrence
  isbIsExact : trace.action isbOccurrence = .barrier AArch64Encoding.isbSy
  architecturalSync : armContextSync trace isbOccurrence

/-- Evidence-bearing protocol states. The synchronized state retains the whole
    witness so ERET cannot silently switch to a different ISB occurrence. -/
inductive VerifiedStage {Occurrence : Type} (trace : Trace Occurrence)
    (armContextSync : ArmContextSync Occurrence) where
  | start
  | irqMasked (irqMask : IrqMaskWitness trace)
  | executionConfigured (irqMask : IrqMaskWitness trace)
  | stageTwoConfigured (irqMask : IrqMaskWitness trace)
  | timerConfigured (irqMask : IrqMaskWitness trace)
  | guestContextInstalled (irqMask : IrqMaskWitness trace)
  | synchronized (sync : ContextSyncWitness trace armContextSync)
  | transferred

/-- The authoritative cold-entry step relation. Reaching synchronized requires
    occurrence-indexed Arm context-sync evidence; transfer requires an exact
    ERET after that same ISB occurrence. -/
inductive Step {Occurrence : Type} (trace : Trace Occurrence)
    (armContextSync : ArmContextSync Occurrence) :
    VerifiedStage trace armContextSync -> VerifiedStage trace armContextSync -> Prop where
  | maskIrq (irqMask : IrqMaskWitness trace) :
      Step trace armContextSync .start (.irqMasked irqMask)
  | configureExecution (irqMask : IrqMaskWitness trace) :
      Step trace armContextSync (.irqMasked irqMask) (.executionConfigured irqMask)
  | configureStageTwo (irqMask : IrqMaskWitness trace) :
      Step trace armContextSync (.executionConfigured irqMask) (.stageTwoConfigured irqMask)
  | configureTimer (irqMask : IrqMaskWitness trace) :
      Step trace armContextSync (.stageTwoConfigured irqMask) (.timerConfigured irqMask)
  | installGuestContext (irqMask : IrqMaskWitness trace) :
      Step trace armContextSync (.timerConfigured irqMask) (.guestContextInstalled irqMask)
  | isb (sync : ContextSyncWitness trace armContextSync) :
      Step trace armContextSync (.guestContextInstalled sync.irqMask)
        (.synchronized sync)
  | eret (sync : ContextSyncWitness trace armContextSync) (eretOccurrence : Occurrence)
      (hAction : trace.action eretOccurrence =
        .controlTransfer AArch64ControlTransfer.Operation.eret
          AArch64Encoding.eretWord)
      (hPo : trace.po sync.isbOccurrence eretOccurrence) :
      Step trace armContextSync (.synchronized sync) .transferred

/-- The reference protocol is the single explicit progression used by the Oak
    cold-entry implementation. -/
def referencePath : List Stage := [
  .start,
  .irqMasked,
  .executionConfigured,
  .stageTwoConfigured,
  .timerConfigured,
  .guestContextInstalled,
  .synchronized,
  .transferred
]

/-- ERET is admitted only after the explicit synchronization stage in this
    protocol model. -/
theorem protocol_eret_requires_synchronized {src : Stage}
    (h : ProtocolStep src .transferred) : src = .synchronized := by
  cases h
  rfl

/-- ISB is the only modeled step that reaches the synchronized state. -/
theorem protocol_synchronized_requires_guest_context {src : Stage}
    (h : ProtocolStep src .synchronized) : src = .guestContextInstalled := by
  cases h
  rfl

/-- The staged reference path has no ordinary state after architectural
    transfer; transfer is terminal in the cold-entry protocol. -/
theorem no_protocol_step_after_transfer {dst : Stage} : ¬ ProtocolStep .transferred dst := by
  intro h
  cases h

/-- Evidence-bearing ERET exposes the exact synchronization witness and the
    later exact control-transfer occurrence. -/
theorem verified_eret_requires_context_sync
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    {src : VerifiedStage trace armContextSync}
    (h : Step trace armContextSync src .transferred) :
    ∃ (sync : ContextSyncWitness trace armContextSync)
      (eretOccurrence : Occurrence),
      src = .synchronized sync ∧
      trace.action eretOccurrence =
        .controlTransfer AArch64ControlTransfer.Operation.eret
          AArch64Encoding.eretWord ∧
      trace.po sync.isbOccurrence eretOccurrence := by
  cases h with
  | eret sync eretOccurrence hAction hPo =>
      exact ⟨sync, eretOccurrence, rfl, hAction, hPo⟩

/-- Transitivity exposes the end-to-end ordering obligation: every one of the
    eight exact context writes precedes the ERET occurrence. -/
theorem verified_eret_orders_context_writes
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    {src : VerifiedStage trace armContextSync}
    (h : Step trace armContextSync src .transferred) :
    ∃ (sync : ContextSyncWitness trace armContextSync)
      (eretOccurrence : Occurrence),
      trace.action eretOccurrence =
        .controlTransfer AArch64ControlTransfer.Operation.eret
          AArch64Encoding.eretWord ∧
      ∀ write, trace.po (sync.writeOccurrence write) eretOccurrence := by
  cases h with
  | eret sync eretOccurrence hAction hPo =>
      exact ⟨sync, eretOccurrence, hAction,
        fun write => trace.po_trans (sync.writesBeforeIsb write) hPo⟩

/-- The one retained exact DAIFSet occurrence precedes every context write and
    the context-synchronizing ISB occurrence. -/
theorem irq_mask_precedes_context_and_isb
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    (sync : ContextSyncWitness trace armContextSync) :
    (∀ write, trace.po sync.irqMask.occurrence
      (sync.writeOccurrence write)) ∧
      trace.po sync.irqMask.occurrence sync.isbOccurrence := by
  constructor
  · exact sync.irqMaskBeforeWrites
  · exact trace.po_trans (sync.irqMaskBeforeWrites .hcrEl2)
      (sync.writesBeforeIsb .hcrEl2)

/-- Transitivity exposes the full first-to-last edge: the exact DAIFSet
    occurrence precedes the exact ERET occurrence. -/
theorem verified_eret_orders_irq_mask
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    {src : VerifiedStage trace armContextSync}
    (h : Step trace armContextSync src .transferred) :
    ∃ (sync : ContextSyncWitness trace armContextSync)
      (eretOccurrence : Occurrence),
      trace.action sync.irqMask.occurrence =
          .pstateImmediate .daifSetIrq AArch64Encoding.msrDaifSetIrq 0b0010#4 ∧
        trace.po sync.irqMask.occurrence eretOccurrence := by
  cases h with
  | eret sync eretOccurrence _ hPo =>
      exact ⟨sync, eretOccurrence, sync.irqMask.actionIsExact,
        trace.po_trans (irq_mask_precedes_context_and_isb sync).2 hPo⟩

/-- Strict program order separates the retained DAIFSet occurrence from each
    later register-write occurrence and from the ISB occurrence. -/
theorem irq_mask_occurrence_distinct_from_context
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    (sync : ContextSyncWitness trace armContextSync) :
    (∀ write, sync.irqMask.occurrence ≠ sync.writeOccurrence write) ∧
      sync.irqMask.occurrence ≠ sync.isbOccurrence := by
  constructor
  · intro write h
    exact trace.po_irrefl (sync.writeOccurrence write)
      (h ▸ sync.irqMaskBeforeWrites write)
  · intro h
    exact trace.po_irrefl sync.isbOccurrence
      (h ▸ (irq_mask_precedes_context_and_isb sync).2)

/-- Strict program order makes every required write occurrence distinct from
    the context-synchronizing ISB occurrence. -/
theorem write_occurrence_ne_isb
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    (sync : ContextSyncWitness trace armContextSync) (write : RequiredWrite) :
    sync.writeOccurrence write ≠ sync.isbOccurrence := by
  intro h
  exact trace.po_irrefl sync.isbOccurrence (h ▸ sync.writesBeforeIsb write)

/-- The total order obligation exposes the seven adjacent source-order edges. -/
theorem register_writes_follow_exact_adjacent_order
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    (sync : ContextSyncWitness trace armContextSync) :
    trace.po (sync.writeOccurrence .hcrEl2)
        (sync.writeOccurrence .vttbrEl2) ∧
      trace.po (sync.writeOccurrence .vttbrEl2)
        (sync.writeOccurrence .vtcrEl2) ∧
      trace.po (sync.writeOccurrence .vtcrEl2)
        (sync.writeOccurrence .cnthctlEl2) ∧
      trace.po (sync.writeOccurrence .cnthctlEl2)
        (sync.writeOccurrence .cntvoffEl2) ∧
      trace.po (sync.writeOccurrence .cntvoffEl2)
        (sync.writeOccurrence .spEl1) ∧
      trace.po (sync.writeOccurrence .spEl1)
        (sync.writeOccurrence .elrEl2) ∧
      trace.po (sync.writeOccurrence .elrEl2)
        (sync.writeOccurrence .spsrEl2) := by
  exact ⟨sync.writesFollowRegisterOrder _ _ (by decide),
    sync.writesFollowRegisterOrder _ _ (by decide),
    sync.writesFollowRegisterOrder _ _ (by decide),
    sync.writesFollowRegisterOrder _ _ (by decide),
    sync.writesFollowRegisterOrder _ _ (by decide),
    sync.writesFollowRegisterOrder _ _ (by decide),
    sync.writesFollowRegisterOrder _ _ (by decide)⟩

/-- Distinct exact register actions make the eight required write occurrences
    pairwise distinct. -/
theorem register_write_occurrence_injective
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    (sync : ContextSyncWitness trace armContextSync) :
    Function.Injective sync.writeOccurrence := by
  intro a b hOccurrence
  have hAction := congrArg trace.action hOccurrence
  rw [sync.writesAreExact a, sync.writesAreExact b] at hAction
  cases a <;> cases b <;> simp_all [RequiredWrite.reg]

/-- A refuted external Arm synchronization predicate cannot be bypassed by
    decoder identity or Oak's instruction-sync capability flag. -/
theorem no_context_sync_witness_when_architecture_refutes
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    (hRefutes : ∀ event, ¬ armContextSync trace event) :
    ¬ Nonempty (ContextSyncWitness trace armContextSync) := by
  rintro ⟨sync⟩
  exact hRefutes sync.isbOccurrence sync.architecturalSync

/-- The evidence-bearing transfer relation remains terminal. -/
theorem no_verified_step_after_transfer
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    {dst : VerifiedStage trace armContextSync} :
    ¬ Step trace armContextSync .transferred dst := by
  intro h
  cases h

end Oak.AArch64ColdEntry
