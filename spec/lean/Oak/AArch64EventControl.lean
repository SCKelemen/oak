namespace Oak.AArch64EventControl

inductive Operation where
  | daifSetIrq
  | daifClrIrq
  | wfi
  | wfe
  | sev
  deriving DecidableEq, Repr

/-- The four PSTATE DAIF mask bits updated by Arm's DAIFSet pseudocode. This
    record deliberately excludes every other PSTATE field and interrupt
    recognition/delivery state. -/
structure DAIFState where
  d : Bool
  a : Bool
  i : Bool
  f : Bool
  deriving DecidableEq, Repr

/-- Arm's successful DAIFSet body, restricted to its four visible DAIF bits. -/
def DAIFState.applySet (state : DAIFState) (operand : BitVec 4) : DAIFState :=
  ⟨state.d || operand.getLsbD 3, state.a || operand.getLsbD 2,
    state.i || operand.getLsbD 1, state.f || operand.getLsbD 0⟩

/-- `MSR DAIFSet, #2`: set PSTATE.I while preserving D, A, and F. -/
def DAIFState.maskIrq (state : DAIFState) : DAIFState :=
  state.applySet 0b0010#4

theorem daifset_irq_masks_and_preserves (state : DAIFState) :
    (state.maskIrq).i = true ∧
    (state.maskIrq).d = state.d ∧
    (state.maskIrq).a = state.a ∧
    (state.maskIrq).f = state.f := by
  obtain ⟨d, a, i, f⟩ := state
  cases d <;> cases a <;> cases i <;> cases f <;> decide

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
