namespace Oak.AArch64SysReg

inductive Reg where
  | currentel | esrEl2 | farEl2 | hpfarEl2 | cntvctEl0
  | hcrEl2 | vttbrEl2 | vtcrEl2 | cnthctlEl2 | cntvoffEl2
  | elrEl2 | spsrEl2 | cntvCtlEl0 | cntvCvalEl0
  | spEl1 | sctlrEl1 | ttbr0El1 | tcrEl1 | vbarEl1
  | mairEl1 | spEl0 | elrEl1 | spsrEl1
  deriving DecidableEq, Repr

inductive ExceptionLevel where
  | el0 | el1 | el2 | el3
  deriving DecidableEq, Repr

def ExceptionLevel.isEL1 : ExceptionLevel → Bool
  | .el1 => true
  | _ => false

/-- The pinned model redirects an EL1 VTTBR_EL2 write into NVMem only under
    this nested-virtualization condition. The Boolean arguments are projections
    of the named architectural register bits, not a model of those registers. -/
def vttbrEl2RedirectsToNVMem (currentEL : ExceptionLevel)
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool) : Bool :=
  currentEL.isEL1 && hcrNv && hcrNv2 && !hcrTge && (scrNs || scrEel2)

/-- The VTTBR_EL2 component of the successful official write body. Every
    other system-register component and every access/trap effect is omitted. -/
structure VTTBRWriteComponent where
  redirectedToNVMem : Bool
  value : BitVec 64
  deriving DecidableEq, Repr

def writeVttbrEl2Component (currentEL : ExceptionLevel)
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool)
    (oldValue newValue : BitVec 64) : VTTBRWriteComponent :=
  if vttbrEl2RedirectsToNVMem currentEL hcrNv hcrNv2 hcrTge scrNs scrEel2 then
    ⟨true, oldValue⟩
  else
    ⟨false, newValue⟩

theorem write_vttbr_el2_at_el2_is_direct
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool)
    (oldValue newValue : BitVec 64) :
    writeVttbrEl2Component .el2 hcrNv hcrNv2 hcrTge scrNs scrEel2
      oldValue newValue = ⟨false, newValue⟩ := by
  rfl

theorem write_vttbr_el2_el1_nv_redirect_preserves_component
    (oldValue newValue : BitVec 64) :
    writeVttbrEl2Component .el1 true true false true false
      oldValue newValue = ⟨true, oldValue⟩ := by
  rfl

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
