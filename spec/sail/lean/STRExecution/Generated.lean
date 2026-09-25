import Sail
import STRExecution.Defs
import STRExecution.Interface

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

namespace STRExecution.Functions

open PreSail

open option
open exception
open Unpredictable
open Register
open MemType
open MemOp
open Fault
open DeviceType
open Constraint
open ArchVersion
open AccType

/-- Type quantifiers: k_ex5375_ : Bool, k_ex5374_ : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftl m n)
  else (Int.shiftr m (Neg.neg n))

/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftr m n)
  else (Int.shiftl m (Neg.neg n))

/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if (((n <b 0) && (m >b 0)) : Bool)
  then ((Int.tdiv (n +i 1) m) -i 1)
  else
    (if (((n >b 0) && (m <b 0)) : Bool)
    then ((Int.tdiv (n -i 1) m) -i 1)
    else (Int.tdiv n m))

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n -i (m *i (fdiv_int n m)))

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if ((len ≤b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if ((l ≥b n) : Bool)
  then ((sail_ones n) <<< i)
  else
    (let one : (BitVec n) := (sail_mask n (1#1 : (BitVec 1)))
    (((one <<< l) - one) <<< i))

/-- Type quantifiers: n : Nat, n > 0 -/
def to_bytes_le {n : _} (b : (BitVec (8 * n))) : (Vector (BitVec 8) n) := Id.run do
  let res := (vectorInit (BitVec.zero 8))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (vectorUpdate res i (Sail.BitVec.extractLsb b ((8 *i i) +i 7) (8 *i i)))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, n > 0 -/
def from_bytes_le {n : _} (v : (Vector (BitVec 8) n)) : (BitVec (8 * n)) := Id.run do
  let res := (BitVec.zero (8 *i n))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (Sail.BitVec.updateSubrange res ((8 *i i) +i 7) (8 *i i) (GetElem?.getElem! v i))
  (pure loop_vars)

/-- Type quantifiers: k_a : Type -/
def is_none (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => false
  | none => true

/-- Type quantifiers: k_a : Type -/
def is_some (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => true
  | none => false

/-- Type quantifiers: k_n : Int -/
def concat_str_bits (str : String) (x : (BitVec k_n)) : String :=
  (HAppend.hAppend str (BitVec.toFormatted x))

/-- Type quantifiers: x : Int -/
def concat_str_dec (str : String) (x : Int) : String :=
  (HAppend.hAppend str (Int.repr x))

/-- Type quantifiers: k_n : Int -/
def UInt (x : (BitVec k_n)) : Int :=
  (BitVec.toNatInt x)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def Zeros (n : Nat) : (BitVec n) :=
  (BitVec.zero n)

/-- Type quantifiers: o : Int, m : Int, n : Nat, n ≥ 0 -/
def __GetSlice_int (n : Nat) (m : Int) (o : Int) : (BitVec n) :=
  (get_slice_int n m o)

def undefined_AccType (_ : Unit) : SailM AccType := do
  (internal_pick
    [AccType_NORMAL, AccType_VEC, AccType_STREAM, AccType_VECSTREAM, AccType_ATOMIC, AccType_ATOMICRW, AccType_ORDERED, AccType_ORDEREDRW, AccType_ORDEREDATOMIC, AccType_ORDEREDATOMICRW, AccType_LIMITEDORDERED, AccType_UNPRIV, AccType_IFETCH, AccType_PTW, AccType_NV2REGISTER, AccType_DC, AccType_DC_UNPRIV, AccType_IC, AccType_DCZVA, AccType_AT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 19 -/
def AccType_of_num (arg_ : Nat) : AccType :=
  match arg_ with
  | 0 => AccType_NORMAL
  | 1 => AccType_VEC
  | 2 => AccType_STREAM
  | 3 => AccType_VECSTREAM
  | 4 => AccType_ATOMIC
  | 5 => AccType_ATOMICRW
  | 6 => AccType_ORDERED
  | 7 => AccType_ORDEREDRW
  | 8 => AccType_ORDEREDATOMIC
  | 9 => AccType_ORDEREDATOMICRW
  | 10 => AccType_LIMITEDORDERED
  | 11 => AccType_UNPRIV
  | 12 => AccType_IFETCH
  | 13 => AccType_PTW
  | 14 => AccType_NV2REGISTER
  | 15 => AccType_DC
  | 16 => AccType_DC_UNPRIV
  | 17 => AccType_IC
  | 18 => AccType_DCZVA
  | _ => AccType_AT

def num_of_AccType (arg_ : AccType) : Int :=
  match arg_ with
  | .AccType_NORMAL => 0
  | .AccType_VEC => 1
  | .AccType_STREAM => 2
  | .AccType_VECSTREAM => 3
  | .AccType_ATOMIC => 4
  | .AccType_ATOMICRW => 5
  | .AccType_ORDERED => 6
  | .AccType_ORDEREDRW => 7
  | .AccType_ORDEREDATOMIC => 8
  | .AccType_ORDEREDATOMICRW => 9
  | .AccType_LIMITEDORDERED => 10
  | .AccType_UNPRIV => 11
  | .AccType_IFETCH => 12
  | .AccType_PTW => 13
  | .AccType_NV2REGISTER => 14
  | .AccType_DC => 15
  | .AccType_DC_UNPRIV => 16
  | .AccType_IC => 17
  | .AccType_DCZVA => 18
  | .AccType_AT => 19

def undefined_Unpredictable (_ : Unit) : SailM Unpredictable := do
  (internal_pick
    [Unpredictable_WBOVERLAPLD, Unpredictable_WBOVERLAPST, Unpredictable_LDPOVERLAP, Unpredictable_BASEOVERLAP, Unpredictable_DATAOVERLAP, Unpredictable_DEVPAGE2, Unpredictable_INSTRDEVICE, Unpredictable_RESCPACR, Unpredictable_RESMAIR, Unpredictable_RESTEXCB, Unpredictable_RESPRRR, Unpredictable_RESDACR, Unpredictable_RESVTCRS, Unpredictable_RESTnSZ, Unpredictable_OORTnSZ, Unpredictable_LARGEIPA, Unpredictable_ESRCONDPASS, Unpredictable_ILZEROIT, Unpredictable_ILZEROT, Unpredictable_BPVECTORCATCHPRI, Unpredictable_VCMATCHHALF, Unpredictable_VCMATCHDAPA, Unpredictable_WPMASKANDBAS, Unpredictable_WPBASCONTIGUOUS, Unpredictable_RESWPMASK, Unpredictable_WPMASKEDBITS, Unpredictable_RESBPWPCTRL, Unpredictable_BPNOTIMPL, Unpredictable_RESBPTYPE, Unpredictable_BPNOTCTXCMP, Unpredictable_BPMATCHHALF, Unpredictable_BPMISMATCHHALF, Unpredictable_RESTARTALIGNPC, Unpredictable_RESTARTZEROUPPERPC, Unpredictable_ZEROUPPER, Unpredictable_ERETZEROUPPERPC, Unpredictable_A32FORCEALIGNPC, Unpredictable_SMD, Unpredictable_AFUPDATE, Unpredictable_IESBinDebug, Unpredictable_ZEROPMSEVFR, Unpredictable_NOOPTYPES, Unpredictable_ZEROMINLATENCY, Unpredictable_ZEROBTYPE, Unpredictable_CLEARERRITEZERO])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 44 -/
def Unpredictable_of_num (arg_ : Nat) : Unpredictable :=
  match arg_ with
  | 0 => Unpredictable_WBOVERLAPLD
  | 1 => Unpredictable_WBOVERLAPST
  | 2 => Unpredictable_LDPOVERLAP
  | 3 => Unpredictable_BASEOVERLAP
  | 4 => Unpredictable_DATAOVERLAP
  | 5 => Unpredictable_DEVPAGE2
  | 6 => Unpredictable_INSTRDEVICE
  | 7 => Unpredictable_RESCPACR
  | 8 => Unpredictable_RESMAIR
  | 9 => Unpredictable_RESTEXCB
  | 10 => Unpredictable_RESPRRR
  | 11 => Unpredictable_RESDACR
  | 12 => Unpredictable_RESVTCRS
  | 13 => Unpredictable_RESTnSZ
  | 14 => Unpredictable_OORTnSZ
  | 15 => Unpredictable_LARGEIPA
  | 16 => Unpredictable_ESRCONDPASS
  | 17 => Unpredictable_ILZEROIT
  | 18 => Unpredictable_ILZEROT
  | 19 => Unpredictable_BPVECTORCATCHPRI
  | 20 => Unpredictable_VCMATCHHALF
  | 21 => Unpredictable_VCMATCHDAPA
  | 22 => Unpredictable_WPMASKANDBAS
  | 23 => Unpredictable_WPBASCONTIGUOUS
  | 24 => Unpredictable_RESWPMASK
  | 25 => Unpredictable_WPMASKEDBITS
  | 26 => Unpredictable_RESBPWPCTRL
  | 27 => Unpredictable_BPNOTIMPL
  | 28 => Unpredictable_RESBPTYPE
  | 29 => Unpredictable_BPNOTCTXCMP
  | 30 => Unpredictable_BPMATCHHALF
  | 31 => Unpredictable_BPMISMATCHHALF
  | 32 => Unpredictable_RESTARTALIGNPC
  | 33 => Unpredictable_RESTARTZEROUPPERPC
  | 34 => Unpredictable_ZEROUPPER
  | 35 => Unpredictable_ERETZEROUPPERPC
  | 36 => Unpredictable_A32FORCEALIGNPC
  | 37 => Unpredictable_SMD
  | 38 => Unpredictable_AFUPDATE
  | 39 => Unpredictable_IESBinDebug
  | 40 => Unpredictable_ZEROPMSEVFR
  | 41 => Unpredictable_NOOPTYPES
  | 42 => Unpredictable_ZEROMINLATENCY
  | 43 => Unpredictable_ZEROBTYPE
  | _ => Unpredictable_CLEARERRITEZERO

def num_of_Unpredictable (arg_ : Unpredictable) : Int :=
  match arg_ with
  | .Unpredictable_WBOVERLAPLD => 0
  | .Unpredictable_WBOVERLAPST => 1
  | .Unpredictable_LDPOVERLAP => 2
  | .Unpredictable_BASEOVERLAP => 3
  | .Unpredictable_DATAOVERLAP => 4
  | .Unpredictable_DEVPAGE2 => 5
  | .Unpredictable_INSTRDEVICE => 6
  | .Unpredictable_RESCPACR => 7
  | .Unpredictable_RESMAIR => 8
  | .Unpredictable_RESTEXCB => 9
  | .Unpredictable_RESPRRR => 10
  | .Unpredictable_RESDACR => 11
  | .Unpredictable_RESVTCRS => 12
  | .Unpredictable_RESTnSZ => 13
  | .Unpredictable_OORTnSZ => 14
  | .Unpredictable_LARGEIPA => 15
  | .Unpredictable_ESRCONDPASS => 16
  | .Unpredictable_ILZEROIT => 17
  | .Unpredictable_ILZEROT => 18
  | .Unpredictable_BPVECTORCATCHPRI => 19
  | .Unpredictable_VCMATCHHALF => 20
  | .Unpredictable_VCMATCHDAPA => 21
  | .Unpredictable_WPMASKANDBAS => 22
  | .Unpredictable_WPBASCONTIGUOUS => 23
  | .Unpredictable_RESWPMASK => 24
  | .Unpredictable_WPMASKEDBITS => 25
  | .Unpredictable_RESBPWPCTRL => 26
  | .Unpredictable_BPNOTIMPL => 27
  | .Unpredictable_RESBPTYPE => 28
  | .Unpredictable_BPNOTCTXCMP => 29
  | .Unpredictable_BPMATCHHALF => 30
  | .Unpredictable_BPMISMATCHHALF => 31
  | .Unpredictable_RESTARTALIGNPC => 32
  | .Unpredictable_RESTARTZEROUPPERPC => 33
  | .Unpredictable_ZEROUPPER => 34
  | .Unpredictable_ERETZEROUPPERPC => 35
  | .Unpredictable_A32FORCEALIGNPC => 36
  | .Unpredictable_SMD => 37
  | .Unpredictable_AFUPDATE => 38
  | .Unpredictable_IESBinDebug => 39
  | .Unpredictable_ZEROPMSEVFR => 40
  | .Unpredictable_NOOPTYPES => 41
  | .Unpredictable_ZEROMINLATENCY => 42
  | .Unpredictable_ZEROBTYPE => 43
  | .Unpredictable_CLEARERRITEZERO => 44

def undefined_Constraint (_ : Unit) : SailM Constraint := do
  (internal_pick
    [Constraint_NONE, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_UNDEFEL0, Constraint_NOP, Constraint_TRUE, Constraint_FALSE, Constraint_DISABLED, Constraint_UNCOND, Constraint_COND, Constraint_ADDITIONAL_DECODE, Constraint_WBSUPPRESS, Constraint_FAULT, Constraint_FORCE, Constraint_FORCENOSLCHECK])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 14 -/
def Constraint_of_num (arg_ : Nat) : Constraint :=
  match arg_ with
  | 0 => Constraint_NONE
  | 1 => Constraint_UNKNOWN
  | 2 => Constraint_UNDEF
  | 3 => Constraint_UNDEFEL0
  | 4 => Constraint_NOP
  | 5 => Constraint_TRUE
  | 6 => Constraint_FALSE
  | 7 => Constraint_DISABLED
  | 8 => Constraint_UNCOND
  | 9 => Constraint_COND
  | 10 => Constraint_ADDITIONAL_DECODE
  | 11 => Constraint_WBSUPPRESS
  | 12 => Constraint_FAULT
  | 13 => Constraint_FORCE
  | _ => Constraint_FORCENOSLCHECK

def num_of_Constraint (arg_ : Constraint) : Int :=
  match arg_ with
  | .Constraint_NONE => 0
  | .Constraint_UNKNOWN => 1
  | .Constraint_UNDEF => 2
  | .Constraint_UNDEFEL0 => 3
  | .Constraint_NOP => 4
  | .Constraint_TRUE => 5
  | .Constraint_FALSE => 6
  | .Constraint_DISABLED => 7
  | .Constraint_UNCOND => 8
  | .Constraint_COND => 9
  | .Constraint_ADDITIONAL_DECODE => 10
  | .Constraint_WBSUPPRESS => 11
  | .Constraint_FAULT => 12
  | .Constraint_FORCE => 13
  | .Constraint_FORCENOSLCHECK => 14

def undefined_MemOp (_ : Unit) : SailM MemOp := do
  (internal_pick [MemOp_LOAD, MemOp_STORE, MemOp_PREFETCH])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MemOp_of_num (arg_ : Nat) : MemOp :=
  match arg_ with
  | 0 => MemOp_LOAD
  | 1 => MemOp_STORE
  | _ => MemOp_PREFETCH

def num_of_MemOp (arg_ : MemOp) : Int :=
  match arg_ with
  | .MemOp_LOAD => 0
  | .MemOp_STORE => 1
  | .MemOp_PREFETCH => 2

def undefined_MemType (_ : Unit) : SailM MemType := do
  (internal_pick [MemType_Normal, MemType_Device])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def MemType_of_num (arg_ : Nat) : MemType :=
  match arg_ with
  | 0 => MemType_Normal
  | _ => MemType_Device

def num_of_MemType (arg_ : MemType) : Int :=
  match arg_ with
  | .MemType_Normal => 0
  | .MemType_Device => 1

def undefined_DeviceType (_ : Unit) : SailM DeviceType := do
  (internal_pick [DeviceType_GRE, DeviceType_nGRE, DeviceType_nGnRE, DeviceType_nGnRnE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def DeviceType_of_num (arg_ : Nat) : DeviceType :=
  match arg_ with
  | 0 => DeviceType_GRE
  | 1 => DeviceType_nGRE
  | 2 => DeviceType_nGnRE
  | _ => DeviceType_nGnRnE

def num_of_DeviceType (arg_ : DeviceType) : Int :=
  match arg_ with
  | .DeviceType_GRE => 0
  | .DeviceType_nGRE => 1
  | .DeviceType_nGnRE => 2
  | .DeviceType_nGnRnE => 3

def undefined_Fault (_ : Unit) : SailM Fault := do
  (internal_pick
    [Fault_None, Fault_AccessFlag, Fault_Alignment, Fault_Background, Fault_Domain, Fault_Permission, Fault_Translation, Fault_AddressSize, Fault_SyncExternal, Fault_SyncExternalOnWalk, Fault_SyncParity, Fault_SyncParityOnWalk, Fault_AsyncParity, Fault_AsyncExternal, Fault_Debug, Fault_TLBConflict, Fault_BranchTarget, Fault_HWUpdateAccessFlag, Fault_Lockdown, Fault_Exclusive, Fault_ICacheMaint])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 20 -/
def Fault_of_num (arg_ : Nat) : Fault :=
  match arg_ with
  | 0 => Fault_None
  | 1 => Fault_AccessFlag
  | 2 => Fault_Alignment
  | 3 => Fault_Background
  | 4 => Fault_Domain
  | 5 => Fault_Permission
  | 6 => Fault_Translation
  | 7 => Fault_AddressSize
  | 8 => Fault_SyncExternal
  | 9 => Fault_SyncExternalOnWalk
  | 10 => Fault_SyncParity
  | 11 => Fault_SyncParityOnWalk
  | 12 => Fault_AsyncParity
  | 13 => Fault_AsyncExternal
  | 14 => Fault_Debug
  | 15 => Fault_TLBConflict
  | 16 => Fault_BranchTarget
  | 17 => Fault_HWUpdateAccessFlag
  | 18 => Fault_Lockdown
  | 19 => Fault_Exclusive
  | _ => Fault_ICacheMaint

def num_of_Fault (arg_ : Fault) : Int :=
  match arg_ with
  | .Fault_None => 0
  | .Fault_AccessFlag => 1
  | .Fault_Alignment => 2
  | .Fault_Background => 3
  | .Fault_Domain => 4
  | .Fault_Permission => 5
  | .Fault_Translation => 6
  | .Fault_AddressSize => 7
  | .Fault_SyncExternal => 8
  | .Fault_SyncExternalOnWalk => 9
  | .Fault_SyncParity => 10
  | .Fault_SyncParityOnWalk => 11
  | .Fault_AsyncParity => 12
  | .Fault_AsyncExternal => 13
  | .Fault_Debug => 14
  | .Fault_TLBConflict => 15
  | .Fault_BranchTarget => 16
  | .Fault_HWUpdateAccessFlag => 17
  | .Fault_Lockdown => 18
  | .Fault_Exclusive => 19
  | .Fault_ICacheMaint => 20

def undefined_MemAttrHints (_ : Unit) : SailM MemAttrHints := do
  (pure { attrs := ← (undefined_bitvector 2)
          hints := ← (undefined_bitvector 2)
          transient := ← (undefined_bool ()) })

def undefined_MemoryAttributes (_ : Unit) : SailM MemoryAttributes := do
  (pure { typ := ← (undefined_MemType ())
          device := ← (undefined_DeviceType ())
          inner := ← (undefined_MemAttrHints ())
          outer := ← (undefined_MemAttrHints ())
          tagged := ← (undefined_bool ())
          shareable := ← (undefined_bool ())
          outershareable := ← (undefined_bool ()) })

def undefined_FullAddress (_ : Unit) : SailM FullAddress := do
  (pure { address := ← (undefined_bitvector 52)
          NS := ← (undefined_bitvector 1) })

def undefined_FaultRecord (_ : Unit) : SailM FaultRecord := do
  (pure { typ := ← (undefined_Fault ())
          acctype := ← (undefined_AccType ())
          ipaddress := ← (undefined_FullAddress ())
          s2fs1walk := ← (undefined_bool ())
          write := ← (undefined_bool ())
          level := ← (undefined_int ())
          extflag := ← (undefined_bitvector 1)
          secondstage := ← (undefined_bool ())
          domain := ← (undefined_bitvector 4)
          errortype := ← (undefined_bitvector 2)
          debugmoe := ← (undefined_bitvector 4) })

def undefined_MPAMinfo (_ : Unit) : SailM MPAMinfo := do
  (pure { mpam_ns := ← (undefined_bitvector 1)
          partid := ← (undefined_bitvector 16)
          pmg := ← (undefined_bitvector 8) })

def undefined_AddressDescriptor (_ : Unit) : SailM AddressDescriptor := do
  (pure { fault := ← (undefined_FaultRecord ())
          memattrs := ← (undefined_MemoryAttributes ())
          paddress := ← (undefined_FullAddress ())
          vaddress := ← (undefined_bitvector 64) })

def undefined_AccessDescriptor (_ : Unit) : SailM AccessDescriptor := do
  (pure { acctype := ← (undefined_AccType ())
          mpam := ← (undefined_MPAMinfo ())
          page_table_walk := ← (undefined_bool ())
          secondstage := ← (undefined_bool ())
          s2fs1walk := ← (undefined_bool ())
          level := ← (undefined_int ()) })

def undefined_ProcState (_ : Unit) : SailM ProcState := do
  (pure { N := ← (undefined_bitvector 1)
          Z := ← (undefined_bitvector 1)
          C := ← (undefined_bitvector 1)
          V := ← (undefined_bitvector 1)
          D := ← (undefined_bitvector 1)
          A := ← (undefined_bitvector 1)
          I := ← (undefined_bitvector 1)
          F := ← (undefined_bitvector 1)
          PAN := ← (undefined_bitvector 1)
          UAO := ← (undefined_bitvector 1)
          DIT := ← (undefined_bitvector 1)
          TCO := ← (undefined_bitvector 1)
          BTYPE := ← (undefined_bitvector 2)
          SS := ← (undefined_bitvector 1)
          IL := ← (undefined_bitvector 1)
          EL := ← (undefined_bitvector 2)
          nRW := ← (undefined_bitvector 1)
          SP := ← (undefined_bitvector 1)
          Q := ← (undefined_bitvector 1)
          GE := ← (undefined_bitvector 4)
          SSBS := ← (undefined_bitvector 1)
          IT := ← (undefined_bitvector 8)
          J := ← (undefined_bitvector 1)
          T := ← (undefined_bitvector 1)
          E := ← (undefined_bitvector 1)
          M := ← (undefined_bitvector 5) })

def EL0 : (BitVec 2) := 0b00#2

def EL1 : (BitVec 2) := 0b01#2

/-- Type quantifiers: width : Nat, n : Nat, n ≥ 0 ∧ n ≤ 31 ∧ width ∈ {8, 16, 32, 64} -/
def aget_X {width : _} (n : Nat) : SailM (BitVec width) := do
  if ((n != 31) : Bool)
  then (pure (BitVec.slice (GetElem?.getElem! (← readReg _R) n) 0 width))
  else (pure (Zeros width))

/-- Type quantifiers: size : Nat, k_sign_extend : Bool, Rt : Nat, k_sixty_four : Bool, k_acq_rel :
  Bool, size ∈ {1, 2, 4, 8} ∧ 0 ≤ Rt ∧ Rt ≤ 31 -/
def MakeLSInstructionSyndrome (size : Nat) (sign_extend : Bool) (Rt : Nat) (sixty_four : Bool) (acq_rel : Bool) : SailM (BitVec 11) := do
  assert ((size == 1) || ((size == 2) || ((size == 4) || (size == 8)))) "str_execution.sail:310.56-310.57"
  assert ((0 ≤b Rt) && (Rt ≤b 31)) "str_execution.sail:311.29-311.30"
  let sz ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let sz : (BitVec 2) :=
    match size with
    | 1 => 0b00#2
    | 2 => 0b01#2
    | 4 => 0b10#2
    | _ => 0b11#2
  let sz := sz
  let ext :=
    if (sign_extend : Bool)
    then 1#1
    else 0#1
  let sf :=
    if (sixty_four : Bool)
    then 1#1
    else 0#1
  let ar :=
    if (acq_rel : Bool)
    then 1#1
    else 0#1
  (pure (((((1#1 +++ sz) +++ ext) +++ (__GetSlice_int 5 Rt 0)) +++ sf) +++ ar))

/-- Type quantifiers: k_ex5662_ : Bool, k_ex5661_ : Bool, k_ex5660_ : Bool, size : Nat, Rt : Nat, size
  ∈ {1, 2, 4, 8} ∧ 0 ≤ Rt ∧ Rt ≤ 31 -/
def AArch64_SetLSInstructionSyndrome (size : Nat) (sign_extend : Bool) (Rt : Nat) (sixty_four : Bool) (acq_rel : Bool) : SailM Unit := do
  if ((← do
    if ((← readReg PSTATE).EL == EL0) then pure true
    else pure ((← readReg PSTATE).EL == EL1)) : Bool)
  then
    writeReg __LSISyndrome (← (MakeLSInstructionSyndrome size sign_extend Rt sixty_four acq_rel))
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, k_postindex : Bool, regsize : Int, k_signed : Bool, t
  : Nat, k_wback : Bool, n ≥ 0 ∧ n ≤ 31 ∨ not((not((n = 31)))) ∧
  t ≥ 0 ∧ t ≤ 31 ∧ datasize ∈ {8, 16, 32, 64} -/
def memory_single_general_immediate_signed_postidx (boundaries : Boundaries) (acctype : AccType) (datasize : Nat) (memop : MemOp) (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (regsize : Int) (signed : Bool) (t : Nat) (wback__arg : Bool) : SailM Unit := do
  let wback : Bool := wback__arg
  if ((← (boundaries.HaveMTEExt ())) : Bool)
  then
    (do
      let is_load_store := ((memop == MemOp_STORE) || (memop == MemOp_LOAD))
      (boundaries.SetNotTagCheckedInstruction ((is_load_store && (n == 31)) && (! wback))))
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((memop == MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (boundaries.ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        assert ((c == Constraint_WBSUPPRESS) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP)))) "str_execution.sail:403.113-403.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (boundaries.EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ =>
            (do
              assert false "Pattern match failure at str_execution.sail:404.8-417.9"
              throw Error.Exit) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((memop == MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (boundaries.ConstrainUnpredictable Unpredictable_WBOVERLAPST)
        assert ((c == Constraint_NONE) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP)))) "str_execution.sail:421.107-421.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (boundaries.EndOfInstruction ())
            (pure rt_unknown))
        | _ =>
          (do
            assert false "Pattern match failure at str_execution.sail:422.8-435.9"
            throw Error.Exit))
    else (pure rt_unknown) ) : SailM Bool )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((memop != MemOp_PREFETCH) : Bool)
        then (boundaries.CheckSPAlignment ())
        else (pure ())
        (boundaries.aget_SP))
    else
      (do
        (aget_X (width := 64) n)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then
          (do
            (undefined_bitvector datasize))
        else
          (do
            (aget_X (width := datasize) t)) ) : SailM (BitVec datasize) )
      if ((! wback) : Bool)
      then (AArch64_SetLSInstructionSyndrome (Nat.div datasize 8) false t (regsize == 64) false)
      else (pure ())
      (boundaries.aset_Mem address (Nat.div datasize 8) acctype data))
  | .MemOp_LOAD =>
    (do
      if ((! wback) : Bool)
      then (AArch64_SetLSInstructionSyndrome (Nat.div datasize 8) signed t (regsize == 64) false)
      else (pure ())
      let data ← (boundaries.aget_Mem address (Nat.div datasize 8) acctype)
      if (signed : Bool)
      then (boundaries.aset_X t (← (boundaries.SignExtend__0 data regsize)))
      else (boundaries.aset_X t (← (boundaries.ZeroExtend__0 data regsize))))
  | .MemOp_PREFETCH => (boundaries.Prefetch address (__GetSlice_int 5 t 0))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then
          (do
            (undefined_bitvector 64))
        else
          (if (postindex : Bool)
          then (pure (address + offset))
          else (pure address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (boundaries.aset_SP address)
      else (boundaries.aset_X n address))
  else (pure ())

/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 ∧ size ∈ {1, 2, 4, 8, 16} -/
def aset_Mem (boundaries : Boundaries) (memory : MemoryBoundaries) (address : (BitVec 64)) (size : Nat) (acctype : AccType) (value_name__arg : (BitVec (8 * size))) : SailM Unit := do
  let value_name := value_name__arg
  let iswrite := true
  let value_name ← (( do
    if ((← do
      let nvEndian ← do
        if (← memory.HaveNV2Ext ()) then
          if (acctype == AccType_NV2REGISTER) then
            pure ((BitVec.join1 [(BitVec.access (← readReg SCTLR_EL2) 25)]) == 1#1)
          else pure false
        else pure false
      if nvEndian then pure true else memory.BigEndian ()) : Bool)
    then
      (do
        (memory.BigEndianReverse value_name))
    else (pure value_name) ) : SailM (BitVec (8 * size)) )
  let aligned ← (( do (undefined_bool ()) ) : SailM Bool )
  let aligned ← (memory.AArch64_CheckAlignment address size acctype iswrite)
  let atomic ← (( do (undefined_bool ()) ) : SailM Bool )
  let atomic ← (( do
    if (((size != 16) || (! ((acctype == AccType_VEC) || (acctype == AccType_VECSTREAM)))) : Bool)
    then (pure aligned)
    else
      (do
        (pure (address == (← (memory.Align__1 address 8))))) ) : SailM Bool )
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  if ((! atomic) : Bool)
  then
    (do
      assert (size >b 1) "str_execution.sail:531.23-531.24"
      (memory.AArch64_aset_MemSingle address 1 acctype aligned (BitVec.slice value_name 0 8))
      let aligned ← (( do
        if ((! aligned) : Bool)
        then
          (do
            let c ← (boundaries.ConstrainUnpredictable Unpredictable_DEVPAGE2)
            assert ((c == Constraint_FAULT) || (c == Constraint_NONE)) "str_execution.sail:535.63-535.64"
            if ((c == Constraint_NONE) : Bool)
            then (pure true)
            else (pure aligned))
        else (pure aligned) ) : SailM Bool )
      let loop_i_lower := 1
      let loop_i_upper := (size -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          (memory.AArch64_aset_MemSingle (BitVec.addInt address i) 1 acctype aligned
            (BitVec.slice value_name (8 *i i) 8))
      (pure loop_vars))
  else
    (do
      if (((size == 16) && ((acctype == AccType_VEC) || (acctype == AccType_VECSTREAM))) : Bool)
      then
        (do
          (memory.AArch64_aset_MemSingle address 8 acctype aligned (BitVec.slice value_name 0 64))
          (memory.AArch64_aset_MemSingle (BitVec.addInt address 8) 8 acctype aligned
            (BitVec.slice value_name 64 64)))
      else (memory.AArch64_aset_MemSingle address size acctype aligned value_name))

def IsFault (addrdesc : AddressDescriptor) : Bool :=
  (addrdesc.fault.typ != Fault_None)

/-- Type quantifiers: size : Nat, k_wasaligned : Bool, size ∈ {1, 2, 4, 8, 16} -/
def AArch64_aset_MemSingle (boundaries : Boundaries) (memory : MemoryBoundaries) (single : MemSingleBoundaries) (address : (BitVec 64)) (size : Nat) (acctype : AccType) (wasaligned : Bool) (value_name : (BitVec (8 * size))) : SailM Unit := do
  assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "str_execution.sail:592.69-592.70"
  assert (address == (← (memory.Align__1 address size))) "str_execution.sail:593.42-593.43"
  let memaddrdesc ← (( do (undefined_AddressDescriptor ()) ) : SailM AddressDescriptor )
  let iswrite := true
  let memaddrdesc ← do (single.AArch64_TranslateAddress address acctype iswrite wasaligned size)
  if ((IsFault memaddrdesc) : Bool)
  then (single.AArch64_Abort address memaddrdesc.fault)
  else (pure ())
  if (memaddrdesc.memattrs.shareable : Bool)
  then (single.ClearExclusiveByAddress memaddrdesc.paddress (← (single.ProcessorID ())) size)
  else (pure ())
  let accdesc ← do (single.CreateAccessDescriptor acctype)
  if ((← (boundaries.HaveMTEExt ())) : Bool)
  then
    (do
      if ((← (single.AccessIsTagChecked (← (boundaries.ZeroExtend__0 address 64)) acctype)) : Bool)
      then
        (do
          let ptag ← do (single.TransformTag (← (boundaries.ZeroExtend__0 address 64)))
          if ((! (← (single.CheckTag memaddrdesc ptag iswrite))) : Bool)
          then (single.TagCheckFail (← (boundaries.ZeroExtend__0 address 64)) iswrite)
          else (pure ()))
      else (pure ()))
  else (pure ())
  (single.aset__Mem memaddrdesc size accdesc value_name)

def undefined_ArchVersion (_ : Unit) : SailM ArchVersion := do
  (internal_pick [ARMv8p0, ARMv8p1, ARMv8p2, ARMv8p3, ARMv8p4, ARMv8p5])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def ArchVersion_of_num (arg_ : Nat) : ArchVersion :=
  match arg_ with
  | 0 => ARMv8p0
  | 1 => ARMv8p1
  | 2 => ARMv8p2
  | 3 => ARMv8p3
  | 4 => ARMv8p4
  | _ => ARMv8p5

def num_of_ArchVersion (arg_ : ArchVersion) : Int :=
  match arg_ with
  | .ARMv8p0 => 0
  | .ARMv8p1 => 1
  | .ARMv8p2 => 2
  | .ARMv8p3 => 3
  | .ARMv8p4 => 4
  | .ARMv8p5 => 5

def HasArchVersion (version : ArchVersion) : SailM Bool := do
  (do
    let through1 ← do
      if version == ARMv8p0 then pure true
      else if version == ARMv8p1 then readReg __v81_implemented else pure false
    let through2 ← do
      if through1 then pure true
      else if version == ARMv8p2 then readReg __v82_implemented else pure false
    let through3 ← do
      if through2 then pure true
      else if version == ARMv8p3 then readReg __v83_implemented else pure false
    let through4 ← do
      if through3 then pure true
      else if version == ARMv8p4 then readReg __v84_implemented else pure false
    if through4 then pure true
    else if version == ARMv8p5 then readReg __v85_implemented else pure false)

def HaveNV2Ext (_ : Unit) : SailM Bool := do
  (HasArchVersion ARMv8p4)

/-- Type quantifiers: k_M : Nat, N : Int, k_M ≥ 0 -/
def ZeroExtend__0 (x : (BitVec k_M)) (N : Int) : SailM (BitVec N) := do
  assert (N ≥b (Sail.BitVec.length x)) "str_execution.sail:644.18-644.19"
  (pure ((Zeros (N -i (Sail.BitVec.length x))) +++ x))

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg _R (← (undefined_vector 31 (← (undefined_bitvector 64))))
  writeReg PSTATE (← (undefined_ProcState ()))
  writeReg __LSISyndrome (← (undefined_bitvector 11))
  writeReg SCTLR_EL2 (← (undefined_bitvector 64))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  writeReg __v85_implemented true
  writeReg __v84_implemented true
  writeReg __v83_implemented true
  writeReg __v82_implemented true
  writeReg __v81_implemented true
  (initialize_registers ())

end STRExecution.Functions
