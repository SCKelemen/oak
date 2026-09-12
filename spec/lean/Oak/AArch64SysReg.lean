namespace Oak.AArch64SysReg

inductive Reg where
  | currentel | esrEl2 | farEl2 | hpfarEl2 | cntvctEl0
  | hcrEl2 | vttbrEl2 | vtcrEl2 | cnthctlEl2 | cntvoffEl2
  | elrEl2 | spsrEl2 | cntvCtlEl0 | cntvCvalEl0
  | spEl1 | sctlrEl1 | ttbr0El1 | tcrEl1 | vbarEl1
  | mairEl1 | spEl0 | elrEl1 | spsrEl1
  deriving DecidableEq, Repr

def writable : Reg -> Bool
  | .currentel | .esrEl2 | .farEl2 | .hpfarEl2 | .cntvctEl0 => false
  | _ => true

inductive Operation where
  | read
  | write
  deriving DecidableEq, Repr

def legal : Operation -> Reg -> Bool
  | .read, _ => true
  | .write, reg => writable reg

theorem currentel_read_only : legal .write .currentel = false := rfl
theorem esr_el2_read_only : legal .write .esrEl2 = false := rfl
theorem far_el2_read_only : legal .write .farEl2 = false := rfl
theorem hpfar_el2_read_only : legal .write .hpfarEl2 = false := rfl
theorem cntvct_el0_read_only : legal .write .cntvctEl0 = false := rfl

theorem every_register_readable (reg : Reg) : legal .read reg = true := rfl

/-- The kernel adapter's registers (the OS pilot's R6) are read/write:
    the MMU register program writes `MAIR_EL1`; the EL0 entry writes
    `SP_EL0`, `ELR_EL1` and `SPSR_EL1` before `ERET`. -/
theorem kernel_adapter_registers_writable :
    legal .write .mairEl1 = true ∧ legal .write .spEl0 = true ∧
    legal .write .elrEl1 = true ∧ legal .write .spsrEl1 = true := ⟨rfl, rfl, rfl, rfl⟩

theorem legal_write_is_writable (reg : Reg)
    (h : legal .write reg = true) : writable reg = true := by
  simpa [legal] using h

/-- A system-register access is a machine-state effect. It is not an
    architectural memory barrier or context-synchronization event. -/
structure Capability where
  readsSystemState : Bool
  writesSystemState : Bool
  ordersMemory : Bool
  completesMemory : Bool
  instructionSync : Bool
  deriving DecidableEq, Repr

def capability : Operation -> Capability
  | .read => ⟨true, false, false, false, false⟩
  | .write => ⟨false, true, false, false, false⟩

theorem sysreg_does_not_hide_barrier (op : Operation) :
    (capability op).ordersMemory = false ∧
    (capability op).completesMemory = false ∧
    (capability op).instructionSync = false := by
  cases op <;> simp [capability]

theorem write_requires_separate_instruction_sync (reg : Reg)
    (h : legal .write reg = true) :
    (capability .write).instructionSync = false := by
  simp [capability]

end Oak.AArch64SysReg
