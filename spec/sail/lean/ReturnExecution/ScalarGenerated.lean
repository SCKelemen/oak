import Sail
import ReturnExecution.Defs
import ReturnExecution.ScalarInterface

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

namespace ReturnExecution.ScalarFunctions
open PreSail

open option
open exception
open ShiftType
open Register
open LogicalOp
open BranchType

/-- Type quantifiers: k_ex4820_ : Bool, k_ex4819_ : Bool -/
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

def undefined_LogicalOp (_ : Unit) : SailM LogicalOp := do
  (internal_pick [LogicalOp_AND, LogicalOp_EOR, LogicalOp_ORR])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def LogicalOp_of_num (arg_ : Nat) : LogicalOp :=
  match arg_ with
  | 0 => LogicalOp_AND
  | 1 => LogicalOp_EOR
  | _ => LogicalOp_ORR

def num_of_LogicalOp (arg_ : LogicalOp) : Int :=
  match arg_ with
  | .LogicalOp_AND => 0
  | .LogicalOp_EOR => 1
  | .LogicalOp_ORR => 2

def undefined_ShiftType (_ : Unit) : SailM ShiftType := do
  (internal_pick [ShiftType_LSL, ShiftType_LSR, ShiftType_ASR, ShiftType_ROR])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ShiftType_of_num (arg_ : Nat) : ShiftType :=
  match arg_ with
  | 0 => ShiftType_LSL
  | 1 => ShiftType_LSR
  | 2 => ShiftType_ASR
  | _ => ShiftType_ROR

def num_of_ShiftType (arg_ : ShiftType) : Int :=
  match arg_ with
  | .ShiftType_LSL => 0
  | .ShiftType_LSR => 1
  | .ShiftType_ASR => 2
  | .ShiftType_ROR => 3

def undefined_BranchType (_ : Unit) : SailM BranchType := do
  (internal_pick
    [BranchType_DIRCALL, BranchType_INDCALL, BranchType_ERET, BranchType_DBGEXIT, BranchType_RET, BranchType_DIR, BranchType_INDIR, BranchType_EXCEPTION, BranchType_RESET, BranchType_UNKNOWN])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 9 -/
def BranchType_of_num (arg_ : Nat) : BranchType :=
  match arg_ with
  | 0 => BranchType_DIRCALL
  | 1 => BranchType_INDCALL
  | 2 => BranchType_ERET
  | 3 => BranchType_DBGEXIT
  | 4 => BranchType_RET
  | 5 => BranchType_DIR
  | 6 => BranchType_INDIR
  | 7 => BranchType_EXCEPTION
  | 8 => BranchType_RESET
  | _ => BranchType_UNKNOWN

def num_of_BranchType (arg_ : BranchType) : Int :=
  match arg_ with
  | .BranchType_DIRCALL => 0
  | .BranchType_INDCALL => 1
  | .BranchType_ERET => 2
  | .BranchType_DBGEXIT => 3
  | .BranchType_RET => 4
  | .BranchType_DIR => 5
  | .BranchType_INDIR => 6
  | .BranchType_EXCEPTION => 7
  | .BranchType_RESET => 8
  | .BranchType_UNKNOWN => 9

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

/-- Type quantifiers: k_M : Nat, N : Int, k_M ≥ 0 -/
def ZeroExtend__0 (x : (BitVec k_M)) (N : Int) : SailM (BitVec N) := do
  assert (N ≥b (Sail.BitVec.length x)) "scalar_execution.sail:142.18-142.19"
  (pure ((Zeros (N -i (Sail.BitVec.length x))) +++ x))

/-- Type quantifiers: width : Nat, n : Nat, n ≥ 0 ∧ n ≤ 31 ∧ width ∈ {8, 16, 32, 64} -/
def aget_X {width : _} (n : Nat) : SailM (BitVec width) := do
  if ((n != 31) : Bool)
  then (pure (BitVec.slice (GetElem?.getElem! (← readReg _R) n) 0 width))
  else (pure (Zeros width))

/-- Type quantifiers: k_width : Int, n : Nat, n ≥ 0 ∧ n ≤ 31 -/
def aset_X (n : Nat) (value_name : (BitVec k_width)) : SailM Unit := do
  assert (((Sail.BitVec.length value_name) == 32) || ((Sail.BitVec.length value_name) == 64)) "scalar_execution.sail:158.38-158.39"
  if ((n != 31) : Bool)
  then writeReg _R (vectorUpdate (← readReg _R) n (← (ZeroExtend__0 value_name 64)))
  else (pure ())

/-- Type quantifiers: k_N : Nat, shift : Nat, shift ≥ 0 ∧ k_N ≥ 0 -/
def LSL (boundaries : ScalarBoundaries) (x : (BitVec k_N)) (shift : Nat) : SailM (BitVec k_N) := do
  assert (shift ≥b 0) "scalar_execution.sail:173.21-173.22"
  let __anon1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length x)) ) : SailM (BitVec k_N) )
  if ((shift == 0) : Bool)
  then (pure x)
  else
    (do
      let (tup__0, tup__1) ← do (boundaries.LSL_C x shift)
      let result : (BitVec k_N) := tup__0
      let __anon1 : (BitVec 1) := tup__1
      (pure result))

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def IsZero (x : (BitVec k_N)) : Bool :=
  (x == (Zeros (Sail.BitVec.length x)))

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def IsZeroBit (x : (BitVec k_N)) : (BitVec 1) :=
  if ((IsZero x) : Bool)
  then 1#1
  else 0#1

def DecodeShift (op : (BitVec 2)) : ShiftType :=
  match op with
  | 0b00 => ShiftType_LSL
  | 0b01 => ShiftType_LSR
  | 0b10 => ShiftType_ASR
  | _ => ShiftType_ROR

/-- Type quantifiers: N : Nat, reg : Nat, amount : Nat, reg ≥ 0 ∧
  reg ≤ 31 ∧ N ∈ {8, 16, 32, 64} ∧ amount ≥ 0 -/
def ShiftReg (boundaries : ScalarBoundaries) {N : _} (reg : Nat) (typ : ShiftType) (amount : Nat) : SailM (BitVec N) := do
  let result ← (( do (aget_X (width := N) reg) ) : SailM (BitVec N) )
  match typ with
  | .ShiftType_LSL =>
    (do
      (LSL boundaries result amount))
  | .ShiftType_LSR =>
    (do
      (boundaries.LSR result amount))
  | .ShiftType_ASR =>
    (do
      (boundaries.ASR result amount))
  | .ShiftType_ROR =>
    (do
      (boundaries.ROR result amount))

def __PostDecode (boundaries : ScalarBoundaries) (_ : Unit) : SailM Unit := do
  if (((← (boundaries.HaveBTIExt ())) && (! (← (boundaries.UsingAArch32 ())))) : Bool)
  then (boundaries.BranchTargetCheck ())
  else (pure ())

/-- Type quantifiers: d : Nat, datasize : Nat, k_invert : Bool, m : Nat, n : Nat, k_setflags : Bool, shift_amount
  : Nat, n ≥ 0 ∧ n ≤ 31 ∧ datasize ∈ {8, 16, 32, 64} ∧
  m ≥ 0 ∧ m ≤ 31 ∧ shift_amount ≥ 0 ∧ d ≥ 0 ∧ d ≤ 31 -/
def integer_logical_shiftedreg (boundaries : ScalarBoundaries) (d : Nat) (datasize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : LogicalOp) (setflags : Bool) (shift_amount : Nat) (shift_type : ShiftType) : SailM Unit := do
  let operand1 ← (( do (aget_X (width := datasize) n) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (ShiftReg boundaries (N := datasize) m shift_type shift_amount) ) : SailM
    (BitVec datasize) )
  let operand2 : (BitVec datasize) :=
    if (invert : Bool)
    then (Complement.complement operand2)
    else operand2
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result : (BitVec datasize) :=
    match op with
    | .LogicalOp_AND => (operand1 &&& operand2)
    | .LogicalOp_ORR => (operand1 ||| operand2)
    | .LogicalOp_EOR => (operand1 ^^^ operand2)
  let result := result
  if (setflags : Bool)
  then
    (do
      let split_vec :=
        (((BitVec.join1 [(BitVec.access result (datasize -i 1))]) +++ (IsZeroBit result)) +++ 0b00#2)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (aset_X d result)

def integer_logical_shiftedreg_decode (boundaries : ScalarBoundaries) (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  writeReg __unconditional true
  let d := (UInt Rd)
  let n := (UInt Rn)
  let m := (UInt Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access imm6 5)]) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure ())
  let shift_type := (DecodeShift shift)
  let shift_amount := (UInt imm6)
  let invert := (N == 1#1)
  (__PostDecode boundaries ())
  (integer_logical_shiftedreg boundaries d datasize invert m n op setflags shift_amount shift_type)

/-- Type quantifiers: m : Int, n : Nat, k_pac : Bool, k_source_is_sp : Bool, k_use_key_a : Bool, n
  ≥ 0 ∧ n ≤ 31 ∧ m ≥ 0 ∧ m ≤ 31 ∨ not((not((k_source_is_sp)))) ∨ not((k_pac)) -/
def branch_unconditional_register (boundaries : ScalarBoundaries) (branch_type : BranchType) (m : Int) (n : Nat) (pac : Bool) (source_is_sp : Bool) (use_key_a : Bool) : SailM Unit := do
  let target ← (( do (aget_X (width := 64) n) ) : SailM (BitVec 64) )
  match branch_type with
  | .BranchType_INDIR =>
    (do
      if ((← readReg InGuardedPage) : Bool)
      then
        (do
          if (((n == 16) || (n == 17)) : Bool)
          then writeReg BTypeNext 0b01#2
          else writeReg BTypeNext 0b11#2)
      else writeReg BTypeNext 0b01#2)
  | .BranchType_INDCALL => writeReg BTypeNext 0b10#2
  | .BranchType_RET => writeReg BTypeNext 0b00#2
  | _ =>
    (do
      assert false "Pattern match failure at scalar_execution.sail:350.4-368.5"
      throw Error.Exit)
  let target ← (( do
    if (pac : Bool)
    then
      (do
        let modifier ← (( do
          if (source_is_sp : Bool)
          then (boundaries.aget_SP)
          else (aget_X (width := 64) m) ) : SailM (BitVec 64) )
        if (use_key_a : Bool)
        then
          (do
            (boundaries.AuthIA target modifier))
        else
          (do
            (boundaries.AuthIB target modifier)))
    else (pure target) ) : SailM (BitVec 64) )
  if ((branch_type == BranchType_INDCALL) : Bool)
  then (aset_X 30 (BitVec.addInt (← (boundaries.aget_PC ())) 4))
  else (pure ())
  (boundaries.BranchTo target branch_type)

def branch_unconditional_register_decode (boundaries : ScalarBoundaries) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op2 : (BitVec 5)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  writeReg __unconditional true
  let n : Int := (UInt Rn)
  let branch_type ← (( do (undefined_BranchType ()) ) : SailM BranchType )
  let m := (UInt Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((pac && (! (← (boundaries.HavePACExt ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure ()))
  let branch_type ← (( do
    match op with
    | 0b00 => (pure BranchType_INDIR)
    | 0b01 => (pure BranchType_INDCALL)
    | 0b10 => (pure BranchType_RET)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM BranchType )
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure ())
        let (n, source_is_sp) ← (( do
          if ((branch_type == BranchType_RET) : Bool)
          then
            (do
              if ((n != 31) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure ())
              let n : Int := 30
              let source_is_sp : Bool := true
              (pure (n, source_is_sp)))
          else (pure (n, source_is_sp)) ) : SailM (Int × Bool) )
        (pure (n, source_is_sp)))
    else (pure (n, source_is_sp)) ) : SailM (Int × Bool) )
  (__PostDecode boundaries ())
  let n := n
  assert ((0 ≤b n) && (n ≤b 31)) "scalar_execution.sail:428.43-428.44"
  (branch_unconditional_register boundaries branch_type m n pac source_is_sp use_key_a)

def decode64 (boundaries : ScalarBoundaries) (op_code : (BitVec 32)) : SailM Unit := do
  if (((((Sail.BitVec.extractLsb op_code 30 24) == (0b0001010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
             op_code 21 21) == (0#1 : (BitVec 1)))) && ((← readReg SEE) <b 1845)) : Bool)
  then
    (do
      writeReg SEE 1845
      let Rd : (BitVec 5) := (Sail.BitVec.extractLsb op_code 4 0)
      let Rn : (BitVec 5) := (Sail.BitVec.extractLsb op_code 9 5)
      let imm6 : (BitVec 6) := (Sail.BitVec.extractLsb op_code 15 10)
      let Rm : (BitVec 5) := (Sail.BitVec.extractLsb op_code 20 16)
      let N : (BitVec 1) := (BitVec.join1 [(BitVec.access op_code 21)])
      let shift : (BitVec 2) := (Sail.BitVec.extractLsb op_code 23 22)
      let opc : (BitVec 2) := (Sail.BitVec.extractLsb op_code 30 29)
      let sf : (BitVec 1) := (BitVec.join1 [(BitVec.access op_code 31)])
      (integer_logical_shiftedreg_decode boundaries Rd Rn imm6 Rm N shift opc sf))
  else
    (do
      if (((((Sail.BitVec.extractLsb op_code 30 24) == (0b0101010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                 op_code 21 21) == (0#1 : (BitVec 1)))) && ((← readReg SEE) <b 1858)) : Bool)
      then
        (do
          writeReg SEE 1858
          let Rd : (BitVec 5) := (Sail.BitVec.extractLsb op_code 4 0)
          let Rn : (BitVec 5) := (Sail.BitVec.extractLsb op_code 9 5)
          let imm6 : (BitVec 6) := (Sail.BitVec.extractLsb op_code 15 10)
          let Rm : (BitVec 5) := (Sail.BitVec.extractLsb op_code 20 16)
          let N : (BitVec 1) := (BitVec.join1 [(BitVec.access op_code 21)])
          let shift : (BitVec 2) := (Sail.BitVec.extractLsb op_code 23 22)
          let opc : (BitVec 2) := (Sail.BitVec.extractLsb op_code 30 29)
          let sf : (BitVec 1) := (BitVec.join1 [(BitVec.access op_code 31)])
          (integer_logical_shiftedreg_decode boundaries Rd Rn imm6 Rm N shift opc sf))
      else
        (do
          if (((((Sail.BitVec.extractLsb op_code 30 24) == (0b1001010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                     op_code 21 21) == (0#1 : (BitVec 1)))) && ((← readReg SEE) <b 1788)) : Bool)
          then
            (do
              writeReg SEE 1788
              let Rd : (BitVec 5) := (Sail.BitVec.extractLsb op_code 4 0)
              let Rn : (BitVec 5) := (Sail.BitVec.extractLsb op_code 9 5)
              let imm6 : (BitVec 6) := (Sail.BitVec.extractLsb op_code 15 10)
              let Rm : (BitVec 5) := (Sail.BitVec.extractLsb op_code 20 16)
              let N : (BitVec 1) := (BitVec.join1 [(BitVec.access op_code 21)])
              let shift : (BitVec 2) := (Sail.BitVec.extractLsb op_code 23 22)
              let opc : (BitVec 2) := (Sail.BitVec.extractLsb op_code 30 29)
              let sf : (BitVec 1) := (BitVec.join1 [(BitVec.access op_code 31)])
              (integer_logical_shiftedreg_decode boundaries Rd Rn imm6 Rm N shift opc sf))
          else
            (do
              if (((((Sail.BitVec.extractLsb op_code 31 10) == (0b1101011001011111000000#22 : (BitVec 22))) && ((Sail.BitVec.extractLsb
                         op_code 4 0) == (0b00000#5 : (BitVec 5)))) && ((← readReg SEE) <b 1522)) : Bool)
              then
                (do
                  writeReg SEE 1522
                  let Rm : (BitVec 5) := (Sail.BitVec.extractLsb op_code 4 0)
                  let Rn : (BitVec 5) := (Sail.BitVec.extractLsb op_code 9 5)
                  let M : (BitVec 1) := (BitVec.join1 [(BitVec.access op_code 10)])
                  let A : (BitVec 1) := (BitVec.join1 [(BitVec.access op_code 11)])
                  let op2 : (BitVec 5) := (Sail.BitVec.extractLsb op_code 20 16)
                  let op : (BitVec 2) := (Sail.BitVec.extractLsb op_code 22 21)
                  let Z : (BitVec 1) := (BitVec.join1 [(BitVec.access op_code 24)])
                  (branch_unconditional_register_decode boundaries Rm Rn M A op2 op Z))
              else sailThrow ((Error_Undefined ())))))

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg _R (← (undefined_vector 31 (← (undefined_bitvector 64))))
  writeReg PSTATE (← (undefined_ProcState ()))
  writeReg InGuardedPage (← (undefined_bool ()))
  writeReg BTypeNext (← (undefined_bitvector 2))
  writeReg __unconditional (← (undefined_bool ()))
  writeReg SEE (← (undefined_int ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end ReturnExecution.ScalarFunctions
