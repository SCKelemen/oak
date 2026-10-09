import Sail
namespace ReturnExecution
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

inductive LogicalOp where | LogicalOp_AND | LogicalOp_EOR | LogicalOp_ORR
  deriving BEq, Inhabited, Repr
  open LogicalOp

inductive ShiftType where | ShiftType_LSL | ShiftType_LSR | ShiftType_ASR | ShiftType_ROR
  deriving BEq, Inhabited, Repr
  open ShiftType

inductive BranchType where | BranchType_DIRCALL | BranchType_INDCALL | BranchType_ERET | BranchType_DBGEXIT | BranchType_RET | BranchType_DIR | BranchType_INDIR | BranchType_EXCEPTION | BranchType_RESET | BranchType_UNKNOWN
  deriving BEq, Inhabited, Repr
  open BranchType

inductive ArchVersion where | ARMv8p0 | ARMv8p1 | ARMv8p2 | ARMv8p3 | ARMv8p4 | ARMv8p5
  deriving BEq, Inhabited, Repr
  open ArchVersion

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

inductive exception where
  | Error_Undefined (_ : Unit)
  | Error_See (_ : String)
  | Error_Implementation_Defined (_ : String)
  | Error_ReservedEncoding (_ : Unit)
  | Error_ExceptionTaken (_ : Unit)
  | Error_Unpredictable (_ : Unit)
  | Error_SError (_ : Bool)
  deriving Inhabited, BEq, Repr
  open exception

inductive Register : Type where
  | __v85_implemented
  | __v84_implemented
  | __v83_implemented
  | __v82_implemented
  | __v81_implemented
  | CFG_ID_AA64PFR0_EL1_EL3
  | CFG_ID_AA64PFR0_EL1_EL2
  | CFG_ID_AA64PFR0_EL1_EL1
  | CFG_ID_AA64PFR0_EL1_EL0
  | SEE
  | __unconditional
  | BTypeNext
  | InGuardedPage
  | _R
  | __highest_el_aarch32
  | TCR_EL3
  | TCR_EL2
  | TCR_EL1
  | PSTATE
  | __PC_changed
  | _PC
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .__v85_implemented => Bool
  | .__v84_implemented => Bool
  | .__v83_implemented => Bool
  | .__v82_implemented => Bool
  | .__v81_implemented => Bool
  | .CFG_ID_AA64PFR0_EL1_EL3 => (BitVec 4)
  | .CFG_ID_AA64PFR0_EL1_EL2 => (BitVec 4)
  | .CFG_ID_AA64PFR0_EL1_EL1 => (BitVec 4)
  | .CFG_ID_AA64PFR0_EL1_EL0 => (BitVec 4)
  | .SEE => Int
  | .__unconditional => Bool
  | .BTypeNext => (BitVec 2)
  | .InGuardedPage => Bool
  | ._R => (Vector (BitVec 64) 31)
  | .__highest_el_aarch32 => Bool
  | .TCR_EL3 => (BitVec 32)
  | .TCR_EL2 => (BitVec 64)
  | .TCR_EL1 => (BitVec 64)
  | .PSTATE => ProcState
  | .__PC_changed => Bool
  | ._PC => (BitVec 64)

instance : Inhabited (RegisterRef RegisterType ProcState) where
  default := .Reg PSTATE
instance : Inhabited (RegisterRef RegisterType (BitVec 2)) where
  default := .Reg BTypeNext
instance : Inhabited (RegisterRef RegisterType (BitVec 32)) where
  default := .Reg TCR_EL3
instance : Inhabited (RegisterRef RegisterType (BitVec 4)) where
  default := .Reg CFG_ID_AA64PFR0_EL1_EL0
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg _PC
instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg __PC_changed
instance : Inhabited (RegisterRef RegisterType Int) where
  default := .Reg SEE
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 31)) where
  default := .Reg _R
abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception


end ReturnExecution
