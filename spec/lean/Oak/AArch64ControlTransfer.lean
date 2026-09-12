namespace Oak.AArch64ControlTransfer

inductive Operation where
  | eret
  | eretX0
  deriving DecidableEq, Repr

/-- The general registers a transfer hands to the target exception level:
    `eret_x0` delivers one value in x0; plain `eret` names none. The
    instruction is the same ERET; the handoff is what is live in the
    register at the instruction (`semir.Arm64ControlTransferSpec.Carries`). -/
def carries : Operation -> List String
  | .eret => []
  | .eretX0 => ["x0"]

structure Capability where
  returnsToCaller : Bool
  transfersExceptionLevel : Bool
  ordersMemory : Bool
  completesMemory : Bool
  instructionSync : Bool
  deriving DecidableEq, Repr

def capability : Operation -> Capability
  | .eret => ⟨false, true, false, false, false⟩
  | .eretX0 => ⟨false, true, false, false, false⟩

/-- The handoff changes what the target receives, not what the transfer
    is: `eret_x0` has exactly ERET's capability. -/
theorem eret_x0_is_eret : capability .eretX0 = capability .eret := rfl

/-- One value, in x0, and no more. -/
theorem eret_x0_carries_x0 : carries .eretX0 = ["x0"] := rfl

/-- Every control transfer is non-returning and hides no barrier. -/
theorem no_transfer_returns_or_hides_barrier (op : Operation) :
    (capability op).returnsToCaller = false ∧
    (capability op).ordersMemory = false ∧
    (capability op).completesMemory = false ∧
    (capability op).instructionSync = false := by
  cases op <;> decide

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
