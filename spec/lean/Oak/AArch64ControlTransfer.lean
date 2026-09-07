namespace Oak.AArch64ControlTransfer

inductive Operation where
  | eret
  deriving DecidableEq, Repr

structure Capability where
  returnsToCaller : Bool
  transfersExceptionLevel : Bool
  ordersMemory : Bool
  completesMemory : Bool
  instructionSync : Bool
  deriving DecidableEq, Repr

def capability : Operation -> Capability
  | .eret => ⟨false, true, false, false, false⟩

/-- ERET is semantically non-returning from the Oak caller. -/
theorem eret_does_not_return :
    (capability .eret).returnsToCaller = false := by
  decide

/-- The transfer changes architectural exception context rather than acting as
    an ordinary call/return operation. -/
theorem eret_is_exception_return :
    (capability .eret).transfersExceptionLevel = true := by
  decide

/-- ERET itself must not be used as a substitute for explicit barrier
    operations required by the surrounding architectural protocol. -/
theorem eret_does_not_hide_barrier :
    (capability .eret).ordersMemory = false ∧
    (capability .eret).completesMemory = false ∧
    (capability .eret).instructionSync = false := by
  decide

end Oak.AArch64ControlTransfer
