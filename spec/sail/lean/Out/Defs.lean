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

structure ProcState where
  N : (BitVec 1)
  Z : (BitVec 1)
  C : (BitVec 1)
  V : (BitVec 1)
  D : (BitVec 1)
  A : (BitVec 1)
  I : (BitVec 1)
  F : (BitVec 1)
  PAN : (BitVec 1)
  UAO : (BitVec 1)
  DIT : (BitVec 1)
  TCO : (BitVec 1)
  BTYPE : (BitVec 2)
  SS : (BitVec 1)
  IL : (BitVec 1)
  EL : (BitVec 2)
  nRW : (BitVec 1)
  SP : (BitVec 1)
  Q : (BitVec 1)
  GE : (BitVec 4)
  SSBS : (BitVec 1)
  IT : (BitVec 8)
  J : (BitVec 1)
  T : (BitVec 1)
  E : (BitVec 1)
  M : (BitVec 5)
  deriving BEq, Inhabited, Repr

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

inductive ExceptionReturnExecutionTarget where | ExceptionReturnExecutionTarget_ERET
  deriving BEq, Inhabited, Repr
  open ExceptionReturnExecutionTarget

structure PlainERETDecode where
  encoding_valid : Bool
  pre_postdecode_checks_pass : Bool
  target : ExceptionReturnExecutionTarget
  op4 : (BitVec 5)
  Rn : (BitVec 5)
  M : (BitVec 1)
  A : (BitVec 1)
  op2 : (BitVec 5)
  pac : Bool
  use_key_a : Bool
  deriving BEq, Inhabited, Repr

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

structure PlainERETInputsAtEL2 where
  dedicated_nv_trap : Bool
  target : (BitVec 64)
  spsr : (BitVec 32)
  deriving BEq, Inhabited, Repr

inductive BranchRegisterExecutionTarget where | BranchRegisterExecutionTarget_RET
  deriving BEq, Inhabited, Repr
  open BranchRegisterExecutionTarget

structure OrdinaryRETDecode where
  encoding_valid : Bool
  pre_postdecode_checks_pass : Bool
  target : BranchRegisterExecutionTarget
  Rm : (BitVec 5)
  Rn : (BitVec 5)
  M : (BitVec 1)
  A : (BitVec 1)
  op2 : (BitVec 5)
  op : (BitVec 2)
  Z : (BitVec 1)
  pac : Bool
  source_is_sp : Bool
  use_key_a : Bool
  deriving BEq, Inhabited, Repr

inductive DirectBranchImmediateExecutionTarget where | DirectBranchImmediateExecutionTarget_DIR | DirectBranchImmediateExecutionTarget_DIRCALL
  deriving BEq, Inhabited, Repr
  open DirectBranchImmediateExecutionTarget

structure OrdinaryBImmediateDecode where
  encoding_valid : Bool
  target : DirectBranchImmediateExecutionTarget
  imm26 : (BitVec 26)
  op : (BitVec 1)
  offset : (BitVec 64)
  deriving BEq, Inhabited, Repr

structure CBZ32Decode where
  encoding_valid : Bool
  Rt : (BitVec 5)
  imm19 : (BitVec 19)
  offset : (BitVec 64)
  deriving BEq, Inhabited, Repr

structure BRKDecode where
  encoding_valid : Bool
  immediate : (BitVec 16)
  deriving BEq, Inhabited, Repr

structure SoftwareBreakpointArguments where
  target_el : (BitVec 2)
  syndrome : (BitVec 25)
  preferred_exception_return : (BitVec 64)
  vect_offset : Int
  deriving BEq, Inhabited, Repr

inductive Register : Type where
  | __defaultRAM
  | __LSISyndrome
  | PSTATE
  | _R
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .__defaultRAM => (BitVec 56)
  | .__LSISyndrome => (BitVec 11)
  | .PSTATE => ProcState
  | ._R => (Vector (BitVec 64) 31)

instance : Inhabited (RegisterRef RegisterType ProcState) where
  default := .Reg PSTATE
instance : Inhabited (RegisterRef RegisterType (BitVec 11)) where
  default := .Reg __LSISyndrome
instance : Inhabited (RegisterRef RegisterType (BitVec 56)) where
  default := .Reg __defaultRAM
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 31)) where
  default := .Reg _R
abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception

