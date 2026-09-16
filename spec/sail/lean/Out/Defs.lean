import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive CompareOp where | CompareOp_GT | CompareOp_GE | CompareOp_EQ | CompareOp_LE | CompareOp_LT
  deriving BEq, Inhabited, Repr
  open CompareOp

inductive LogicalOp where | LogicalOp_AND | LogicalOp_EOR | LogicalOp_ORR
  deriving BEq, Inhabited, Repr
  open LogicalOp

inductive VBitOp where | VBitOp_VBIF | VBitOp_VBIT | VBitOp_VBSL | VBitOp_VEOR
  deriving BEq, Inhabited, Repr
  open VBitOp

inductive MemBarrierOp where | MemBarrierOp_DSB | MemBarrierOp_DMB | MemBarrierOp_ISB | MemBarrierOp_SSBB | MemBarrierOp_PSSBB | MemBarrierOp_SB
  deriving BEq, Inhabited, Repr
  open MemBarrierOp

inductive MBReqDomain where | MBReqDomain_Nonshareable | MBReqDomain_InnerShareable | MBReqDomain_OuterShareable | MBReqDomain_FullSystem
  deriving BEq, Inhabited, Repr
  open MBReqDomain

inductive MBReqTypes where | MBReqTypes_Reads | MBReqTypes_Writes | MBReqTypes_All
  deriving BEq, Inhabited, Repr
  open MBReqTypes

inductive BarrierExecutionTarget where | BarrierExecutionTarget_DataSynchronizationBarrier | BarrierExecutionTarget_DataMemoryBarrier | BarrierExecutionTarget_InstructionSynchronizationBarrier | BarrierExecutionTarget_SpeculativeSynchronizationBarrierToVA | BarrierExecutionTarget_SpeculativeSynchronizationBarrierToPA | BarrierExecutionTarget_SpeculationBarrier
  deriving BEq, Inhabited, Repr
  open BarrierExecutionTarget

inductive TLBIOperationTarget where | TLBIOperationTarget_VMALLS12E1IS
  deriving BEq, Inhabited, Repr
  open TLBIOperationTarget

inductive PSTATEWriteTarget where | PSTATEWriteTarget_DAIFSet
  deriving BEq, Inhabited, Repr
  open PSTATEWriteTarget

inductive SystemRegisterWriteTarget where | SystemRegisterWriteTarget_VTTBR_EL2 | SystemRegisterWriteTarget_VTCR_EL2 | SystemRegisterWriteTarget_CNTHCTL_EL2 | SystemRegisterWriteTarget_CNTVOFF_EL2 | SystemRegisterWriteTarget_SP_EL1 | SystemRegisterWriteTarget_ELR_EL2 | SystemRegisterWriteTarget_SPSR_EL2 | SystemRegisterWriteTarget_HCR_EL2
  deriving BEq, Inhabited, Repr
  open SystemRegisterWriteTarget

structure ColdEntryRegisterState where
  hcr_el2 : (BitVec 64)
  vttbr_el2 : (BitVec 64)
  vtcr_el2 : (BitVec 32)
  cnthctl_el2 : (BitVec 32)
  cntvoff_el2 : (BitVec 64)
  sp_el1 : (BitVec 64)
  elr_el2 : (BitVec 64)
  spsr_el2 : (BitVec 32)
  deriving BEq, Inhabited, Repr

structure ColdEntryRegisterInputs where
  hcr_el2 : (BitVec 64)
  vttbr_el2 : (BitVec 64)
  vtcr_el2 : (BitVec 64)
  cnthctl_el2 : (BitVec 64)
  cntvoff_el2 : (BitVec 64)
  sp_el1 : (BitVec 64)
  elr_el2 : (BitVec 64)
  spsr_el2 : (BitVec 64)
  deriving BEq, Inhabited, Repr

structure ColdEntryRegisterSequenceResult where
  state : ColdEntryRegisterState
  write0 : SystemRegisterWriteTarget
  write1 : SystemRegisterWriteTarget
  write2 : SystemRegisterWriteTarget
  write3 : SystemRegisterWriteTarget
  write4 : SystemRegisterWriteTarget
  write5 : SystemRegisterWriteTarget
  write6 : SystemRegisterWriteTarget
  write7 : SystemRegisterWriteTarget
  deriving BEq, Inhabited, Repr

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception

