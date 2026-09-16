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

/-- The pinned model uses the same nested-virtualization predicate for VTCR_EL2.
    Its Boolean arguments are projections of old architectural control bits;
    their consistency with the surrounding machine state is external. -/
def vtcrEl2RedirectsToNVMem (currentEL : ExceptionLevel)
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool) : Bool :=
  currentEL.isEL1 && hcrNv && hcrNv2 && !hcrTge && (scrNs || scrEel2)

/-- The successful official write body's 32-bit VTCR_EL2 component. The source
    X register is 64-bit, but the pinned Arm model stores only its low 32 bits.
    NVMem(64), other state, and access/trap effects are omitted. -/
structure VTCRWriteComponent where
  redirectedToNVMem : Bool
  value : BitVec 32
  deriving DecidableEq, Repr

def writeVtcrEl2Component (currentEL : ExceptionLevel)
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool)
    (oldValue : BitVec 32) (newValue : BitVec 64) : VTCRWriteComponent :=
  if vtcrEl2RedirectsToNVMem currentEL hcrNv hcrNv2 hcrTge scrNs scrEel2 then
    ⟨true, oldValue⟩
  else
    ⟨false, newValue.setWidth 32⟩

theorem write_vtcr_el2_at_el2_is_direct_low32
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool)
    (oldValue : BitVec 32) (newValue : BitVec 64) :
    writeVtcrEl2Component .el2 hcrNv hcrNv2 hcrTge scrNs scrEel2
      oldValue newValue = ⟨false, newValue.setWidth 32⟩ := by
  rfl

theorem write_vtcr_el2_el1_nv_redirect_preserves_component
    (oldValue : BitVec 32) (newValue : BitVec 64) :
    writeVtcrEl2Component .el1 true true false true false oldValue newValue =
      ⟨true, oldValue⟩ := by
  rfl

/-- The successful official CNTHCTL_EL2 write body. The architectural
    component is 32-bit even though the source X register is 64-bit. Access,
    traps, and every other machine-state component are omitted. -/
structure CNTHCTLWriteComponent where
  value : BitVec 32
  deriving DecidableEq, Repr

def writeCnthctlEl2Component (newValue : BitVec 64) : CNTHCTLWriteComponent :=
  ⟨newValue.setWidth 32⟩

theorem write_cnthctl_el2_is_direct_low32 (newValue : BitVec 64) :
    writeCnthctlEl2Component newValue = ⟨newValue.setWidth 32⟩ := by
  rfl

/-- The pinned CNTVOFF_EL2 body redirects under the same old-HCR nested-
    virtualization predicate used by VTTBR_EL2. These Boolean arguments are
    separate architectural-state projections, not fields of either value. -/
def cntvoffEl2RedirectsToNVMem (currentEL : ExceptionLevel)
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool) : Bool :=
  currentEL.isEL1 && hcrNv && hcrNv2 && !hcrTge && (scrNs || scrEel2)

/-- The successful official write body's 64-bit CNTVOFF_EL2 component.
    NVMem(96), every other state component, and access/trap effects are omitted. -/
structure CNTVOFFWriteComponent where
  redirectedToNVMem : Bool
  value : BitVec 64
  deriving DecidableEq, Repr

def writeCntvoffEl2Component (currentEL : ExceptionLevel)
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool)
    (oldValue newValue : BitVec 64) : CNTVOFFWriteComponent :=
  if cntvoffEl2RedirectsToNVMem currentEL hcrNv hcrNv2 hcrTge scrNs scrEel2 then
    ⟨true, oldValue⟩
  else
    ⟨false, newValue⟩

theorem write_cntvoff_el2_at_el2_is_direct
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool)
    (oldValue newValue : BitVec 64) :
    writeCntvoffEl2Component .el2 hcrNv hcrNv2 hcrTge scrNs scrEel2
      oldValue newValue = ⟨false, newValue⟩ := by
  rfl

theorem write_cntvoff_el2_el1_nv_redirect_preserves_component
    (oldValue newValue : BitVec 64) :
    writeCntvoffEl2Component .el1 true true false true false oldValue newValue =
      ⟨true, oldValue⟩ := by
  rfl

/-- The pinned SP_EL1 body redirects under the old-HCR nested-virtualization
    predicate. The Boolean inputs are separate machine-state projections. -/
def spEl1RedirectsToNVMem (currentEL : ExceptionLevel)
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool) : Bool :=
  currentEL.isEL1 && hcrNv && hcrNv2 && !hcrTge && (scrNs || scrEel2)

/-- The successful official write body's 64-bit SP_EL1 component. NVMem(576),
    other architectural state, and all access/trap effects are omitted. -/
structure SPEl1WriteComponent where
  redirectedToNVMem : Bool
  value : BitVec 64
  deriving DecidableEq, Repr

def writeSpEl1Component (currentEL : ExceptionLevel)
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool)
    (oldValue newValue : BitVec 64) : SPEl1WriteComponent :=
  if spEl1RedirectsToNVMem currentEL hcrNv hcrNv2 hcrTge scrNs scrEel2 then
    ⟨true, oldValue⟩
  else
    ⟨false, newValue⟩

theorem write_sp_el1_at_el2_is_direct
    (hcrNv hcrNv2 hcrTge scrNs scrEel2 : Bool)
    (oldValue newValue : BitVec 64) :
    writeSpEl1Component .el2 hcrNv hcrNv2 hcrTge scrNs scrEel2
      oldValue newValue = ⟨false, newValue⟩ := by
  rfl

theorem write_sp_el1_el1_nv_redirect_preserves_component
    (oldValue newValue : BitVec 64) :
    writeSpEl1Component .el1 true true false true false oldValue newValue =
      ⟨true, oldValue⟩ := by
  rfl

/-- The pinned model tests these old HCR_EL2 control-bit projections before
    writing HCR_EL2. They must not be derived from the incoming new value.
    Their consistency with `oldValue` remains a separate refinement premise. -/
def hcrEl2RedirectsToNVMem (currentEL : ExceptionLevel)
    (oldHcrNv oldHcrNv2 oldHcrTge scrNs scrEel2 : Bool) : Bool :=
  currentEL.isEL1 && oldHcrNv && oldHcrNv2 && !oldHcrTge && (scrNs || scrEel2)

/-- The HCR_EL2 component of the successful official write body. NVMem(120),
    every other state component, and every access/trap effect are omitted. -/
structure HCRWriteComponent where
  redirectedToNVMem : Bool
  value : BitVec 64
  deriving DecidableEq, Repr

def writeHcrEl2Component (currentEL : ExceptionLevel)
    (oldHcrNv oldHcrNv2 oldHcrTge scrNs scrEel2 : Bool)
    (oldValue newValue : BitVec 64) : HCRWriteComponent :=
  if hcrEl2RedirectsToNVMem currentEL oldHcrNv oldHcrNv2 oldHcrTge
      scrNs scrEel2 then
    ⟨true, oldValue⟩
  else
    ⟨false, newValue⟩

theorem write_hcr_el2_at_el2_is_direct
    (oldHcrNv oldHcrNv2 oldHcrTge scrNs scrEel2 : Bool)
    (oldValue newValue : BitVec 64) :
    writeHcrEl2Component .el2 oldHcrNv oldHcrNv2 oldHcrTge scrNs scrEel2
      oldValue newValue = ⟨false, newValue⟩ := by
  rfl

theorem write_hcr_el2_el1_old_nv_redirect_preserves_component
    (oldValue newValue : BitVec 64) :
    writeHcrEl2Component .el1 true true false true false oldValue newValue =
      ⟨true, oldValue⟩ := by
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
