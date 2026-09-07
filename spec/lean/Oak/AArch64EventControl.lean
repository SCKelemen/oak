namespace Oak.AArch64EventControl

inductive Operation where
  | daifSetIrq
  | daifClrIrq
  | wfi
  | wfe
  | sev
  deriving DecidableEq, Repr

structure Capability where
  changesIrqMask : Bool
  mayWait : Bool
  sendsEvent : Bool
  ordersMemory : Bool
  completesMemory : Bool
  instructionSync : Bool
  deriving DecidableEq, Repr

def capability : Operation -> Capability
  | .daifSetIrq => ⟨true, false, false, false, false, false⟩
  | .daifClrIrq => ⟨true, false, false, false, false, false⟩
  | .wfi => ⟨false, true, false, false, false, false⟩
  | .wfe => ⟨false, true, false, false, false, false⟩
  | .sev => ⟨false, false, true, false, false, false⟩

theorem daif_operations_only_change_irq_mask :
    (capability .daifSetIrq).changesIrqMask = true ∧
    (capability .daifClrIrq).changesIrqMask = true := by
  decide

theorem wait_operations_are_explicit :
    (capability .wfi).mayWait = true ∧
    (capability .wfe).mayWait = true ∧
    (capability .sev).sendsEvent = true := by
  decide

theorem event_control_does_not_hide_barrier (op : Operation) :
    (capability op).ordersMemory = false ∧
    (capability op).completesMemory = false ∧
    (capability op).instructionSync = false := by
  cases op <;> decide

end Oak.AArch64EventControl
