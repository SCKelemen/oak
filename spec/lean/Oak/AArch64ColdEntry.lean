import Oak.AArch64ControlTransfer
import Oak.AArch64Encoding
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

/-- The occurrence classes used by the verified cold-entry slice. A barrier is
    identified by its exact word, not by Oak's capability Boolean. -/
inductive Action where
  | sysReg (op : AArch64SysReg.Operation) (reg : AArch64SysReg.Reg)
  | barrier (word : BitVec 32)
  | controlTransfer (op : AArch64ControlTransfer.Operation)
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

/-- Exact cold-entry evidence: every required register write occurs before the
    same exact ISB word, and an external Arm model certifies that occurrence as
    context synchronizing. -/
structure ContextSyncWitness {Occurrence : Type} (trace : Trace Occurrence)
    (armContextSync : ArmContextSync Occurrence) where
  writeOccurrence : RequiredWrite -> Occurrence
  isbOccurrence : Occurrence
  writesAreExact : ∀ write,
    trace.action (writeOccurrence write) = .sysReg .write write.reg
  writesBeforeIsb : ∀ write, trace.po (writeOccurrence write) isbOccurrence
  isbIsExact : trace.action isbOccurrence = .barrier AArch64Encoding.isbSy
  architecturalSync : armContextSync trace isbOccurrence

/-- Evidence-bearing protocol states. The synchronized state retains the whole
    witness so ERET cannot silently switch to a different ISB occurrence. -/
inductive VerifiedStage {Occurrence : Type} (trace : Trace Occurrence)
    (armContextSync : ArmContextSync Occurrence) where
  | start
  | irqMasked
  | executionConfigured
  | stageTwoConfigured
  | timerConfigured
  | guestContextInstalled
  | synchronized (sync : ContextSyncWitness trace armContextSync)
  | transferred

/-- The authoritative cold-entry step relation. Reaching synchronized requires
    occurrence-indexed Arm context-sync evidence; transfer requires an exact
    ERET after that same ISB occurrence. -/
inductive Step {Occurrence : Type} (trace : Trace Occurrence)
    (armContextSync : ArmContextSync Occurrence) :
    VerifiedStage trace armContextSync -> VerifiedStage trace armContextSync -> Prop where
  | maskIrq : Step trace armContextSync .start .irqMasked
  | configureExecution : Step trace armContextSync .irqMasked .executionConfigured
  | configureStageTwo : Step trace armContextSync .executionConfigured .stageTwoConfigured
  | configureTimer : Step trace armContextSync .stageTwoConfigured .timerConfigured
  | installGuestContext : Step trace armContextSync .timerConfigured .guestContextInstalled
  | isb (sync : ContextSyncWitness trace armContextSync) :
      Step trace armContextSync .guestContextInstalled (.synchronized sync)
  | eret (sync : ContextSyncWitness trace armContextSync) (eretOccurrence : Occurrence)
      (hAction : trace.action eretOccurrence =
        .controlTransfer AArch64ControlTransfer.Operation.eret)
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
        .controlTransfer AArch64ControlTransfer.Operation.eret ∧
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
        .controlTransfer AArch64ControlTransfer.Operation.eret ∧
      ∀ write, trace.po (sync.writeOccurrence write) eretOccurrence := by
  cases h with
  | eret sync eretOccurrence hAction hPo =>
      exact ⟨sync, eretOccurrence, hAction,
        fun write => trace.po_trans (sync.writesBeforeIsb write) hPo⟩

/-- Strict program order makes every required write occurrence distinct from
    the context-synchronizing ISB occurrence. -/
theorem write_occurrence_ne_isb
    {Occurrence : Type} {trace : Trace Occurrence}
    {armContextSync : ArmContextSync Occurrence}
    (sync : ContextSyncWitness trace armContextSync) (write : RequiredWrite) :
    sync.writeOccurrence write ≠ sync.isbOccurrence := by
  intro h
  exact trace.po_irrefl sync.isbOccurrence (h ▸ sync.writesBeforeIsb write)

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
