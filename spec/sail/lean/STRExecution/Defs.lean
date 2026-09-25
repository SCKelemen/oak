import Sail

namespace STRExecution
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

inductive AccType where | AccType_NORMAL | AccType_VEC | AccType_STREAM | AccType_VECSTREAM | AccType_ATOMIC | AccType_ATOMICRW | AccType_ORDERED | AccType_ORDEREDRW | AccType_ORDEREDATOMIC | AccType_ORDEREDATOMICRW | AccType_LIMITEDORDERED | AccType_UNPRIV | AccType_IFETCH | AccType_PTW | AccType_NV2REGISTER | AccType_DC | AccType_DC_UNPRIV | AccType_IC | AccType_DCZVA | AccType_AT
  deriving BEq, Inhabited, Repr
  open AccType

inductive Unpredictable where | Unpredictable_WBOVERLAPLD | Unpredictable_WBOVERLAPST | Unpredictable_LDPOVERLAP | Unpredictable_BASEOVERLAP | Unpredictable_DATAOVERLAP | Unpredictable_DEVPAGE2 | Unpredictable_INSTRDEVICE | Unpredictable_RESCPACR | Unpredictable_RESMAIR | Unpredictable_RESTEXCB | Unpredictable_RESPRRR | Unpredictable_RESDACR | Unpredictable_RESVTCRS | Unpredictable_RESTnSZ | Unpredictable_OORTnSZ | Unpredictable_LARGEIPA | Unpredictable_ESRCONDPASS | Unpredictable_ILZEROIT | Unpredictable_ILZEROT | Unpredictable_BPVECTORCATCHPRI | Unpredictable_VCMATCHHALF | Unpredictable_VCMATCHDAPA | Unpredictable_WPMASKANDBAS | Unpredictable_WPBASCONTIGUOUS | Unpredictable_RESWPMASK | Unpredictable_WPMASKEDBITS | Unpredictable_RESBPWPCTRL | Unpredictable_BPNOTIMPL | Unpredictable_RESBPTYPE | Unpredictable_BPNOTCTXCMP | Unpredictable_BPMATCHHALF | Unpredictable_BPMISMATCHHALF | Unpredictable_RESTARTALIGNPC | Unpredictable_RESTARTZEROUPPERPC | Unpredictable_ZEROUPPER | Unpredictable_ERETZEROUPPERPC | Unpredictable_A32FORCEALIGNPC | Unpredictable_SMD | Unpredictable_AFUPDATE | Unpredictable_IESBinDebug | Unpredictable_ZEROPMSEVFR | Unpredictable_NOOPTYPES | Unpredictable_ZEROMINLATENCY | Unpredictable_ZEROBTYPE | Unpredictable_CLEARERRITEZERO
  deriving BEq, Inhabited, Repr
  open Unpredictable

inductive Constraint where | Constraint_NONE | Constraint_UNKNOWN | Constraint_UNDEF | Constraint_UNDEFEL0 | Constraint_NOP | Constraint_TRUE | Constraint_FALSE | Constraint_DISABLED | Constraint_UNCOND | Constraint_COND | Constraint_ADDITIONAL_DECODE | Constraint_WBSUPPRESS | Constraint_FAULT | Constraint_FORCE | Constraint_FORCENOSLCHECK
  deriving BEq, Inhabited, Repr
  open Constraint

inductive MemOp where | MemOp_LOAD | MemOp_STORE | MemOp_PREFETCH
  deriving BEq, Inhabited, Repr
  open MemOp

inductive MemType where | MemType_Normal | MemType_Device
  deriving BEq, Inhabited, Repr
  open MemType

inductive DeviceType where | DeviceType_GRE | DeviceType_nGRE | DeviceType_nGnRE | DeviceType_nGnRnE
  deriving BEq, Inhabited, Repr
  open DeviceType

inductive Fault where | Fault_None | Fault_AccessFlag | Fault_Alignment | Fault_Background | Fault_Domain | Fault_Permission | Fault_Translation | Fault_AddressSize | Fault_SyncExternal | Fault_SyncExternalOnWalk | Fault_SyncParity | Fault_SyncParityOnWalk | Fault_AsyncParity | Fault_AsyncExternal | Fault_Debug | Fault_TLBConflict | Fault_BranchTarget | Fault_HWUpdateAccessFlag | Fault_Lockdown | Fault_Exclusive | Fault_ICacheMaint
  deriving BEq, Inhabited, Repr
  open Fault

structure MemAttrHints where
  attrs : (BitVec 2)
  hints : (BitVec 2)
  transient : Bool
  deriving BEq, Inhabited, Repr

structure MemoryAttributes where
  typ : MemType
  device : DeviceType
  inner : MemAttrHints
  outer : MemAttrHints
  tagged : Bool
  shareable : Bool
  outershareable : Bool
  deriving BEq, Inhabited, Repr

structure FullAddress where
  address : (BitVec 52)
  NS : (BitVec 1)
  deriving BEq, Inhabited, Repr

structure FaultRecord where
  typ : Fault
  acctype : AccType
  ipaddress : FullAddress
  s2fs1walk : Bool
  write : Bool
  level : Int
  extflag : (BitVec 1)
  secondstage : Bool
  domain : (BitVec 4)
  errortype : (BitVec 2)
  debugmoe : (BitVec 4)
  deriving BEq, Inhabited, Repr

structure MPAMinfo where
  mpam_ns : (BitVec 1)
  partid : (BitVec 16)
  pmg : (BitVec 8)
  deriving BEq, Inhabited, Repr

structure AddressDescriptor where
  fault : FaultRecord
  memattrs : MemoryAttributes
  paddress : FullAddress
  vaddress : (BitVec 64)
  deriving BEq, Inhabited, Repr

structure AccessDescriptor where
  acctype : AccType
  mpam : MPAMinfo
  page_table_walk : Bool
  secondstage : Bool
  s2fs1walk : Bool
  level : Int
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

inductive Register : Type where
  | SCTLR_EL2
  | __LSISyndrome
  | PSTATE
  | _R
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .SCTLR_EL2 => (BitVec 64)
  | .__LSISyndrome => (BitVec 11)
  | .PSTATE => ProcState
  | ._R => (Vector (BitVec 64) 31)

instance : Inhabited (RegisterRef RegisterType ProcState) where
  default := .Reg PSTATE
instance : Inhabited (RegisterRef RegisterType (BitVec 11)) where
  default := .Reg __LSISyndrome
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg SCTLR_EL2
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 31)) where
  default := .Reg _R
abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception


end STRExecution
