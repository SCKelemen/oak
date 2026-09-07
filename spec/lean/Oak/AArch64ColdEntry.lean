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

inductive Step : Stage -> Stage -> Prop where
  | maskIrq : Step .start .irqMasked
  | configureExecution : Step .irqMasked .executionConfigured
  | configureStageTwo : Step .executionConfigured .stageTwoConfigured
  | configureTimer : Step .stageTwoConfigured .timerConfigured
  | installGuestContext : Step .timerConfigured .guestContextInstalled
  | isb : Step .guestContextInstalled .synchronized
  | eret : Step .synchronized .transferred

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
theorem eret_requires_synchronized {src : Stage}
    (h : Step src .transferred) : src = .synchronized := by
  cases h
  rfl

/-- ISB is the only modeled step that reaches the synchronized state. -/
theorem synchronized_requires_guest_context {src : Stage}
    (h : Step src .synchronized) : src = .guestContextInstalled := by
  cases h
  rfl

/-- The staged reference path has no ordinary state after architectural
    transfer; transfer is terminal in the cold-entry protocol. -/
theorem no_step_after_transfer {dst : Stage} : ¬ Step .transferred dst := by
  intro h
  cases h

end Oak.AArch64ColdEntry
