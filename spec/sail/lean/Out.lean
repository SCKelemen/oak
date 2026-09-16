import Sail
import Out.Defs
import Out.Specialization
import Out.FakeReal

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

namespace Out.Functions

open option
open VBitOp
open TLBIOperationTarget
open PSTATEWriteTarget
open MemBarrierOp
open MBReqTypes
open MBReqDomain
open LogicalOp
open CompareOp
open BarrierExecutionTarget

/-- Type quantifiers: k_ex11343_ : Bool, k_ex11342_ : Bool -/
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

/-- Type quantifiers: k_n : Nat, k_n ≥ 1 -/
def SInt (x : (BitVec k_n)) : Int :=
  (BitVec.toInt x)

/-- Type quantifiers: o : Int, m : Int, n : Nat, n ≥ 0 -/
def __GetSlice_int (n : Nat) (m : Int) (o : Int) : (BitVec n) :=
  (get_slice_int n m o)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def Zeros (n : Nat) : (BitVec n) :=
  (BitVec.zero n)

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def IsZero (x : (BitVec k_N)) : Bool :=
  (x == (Zeros (Sail.BitVec.length x)))

/-- Type quantifiers: k_N : Nat, k_N ≥ 1 -/
def AddWithCarry (x : (BitVec k_N)) (y : (BitVec k_N)) (carry_in : (BitVec 1)) : ((BitVec k_N) × (BitVec 4)) :=
  let unsigned_sum := (((UInt x) +i (UInt y)) +i (UInt carry_in))
  let signed_sum := (((SInt x) +i (SInt y)) +i (UInt carry_in))
  let result : (BitVec k_N) := (__GetSlice_int (Sail.BitVec.length y) unsigned_sum 0)
  let n : (BitVec 1) := (BitVec.join1 [(BitVec.access result ((Sail.BitVec.length y) -i 1))])
  let z : (BitVec 1) :=
    if ((IsZero result) : Bool)
    then 1#1
    else 0#1
  let c : (BitVec 1) :=
    if (((UInt result) == unsigned_sum) : Bool)
    then 0#1
    else 1#1
  let v : (BitVec 1) :=
    if (((SInt result) == signed_sum) : Bool)
    then 0#1
    else 1#1
  (result, (((n +++ z) +++ c) +++ v))

def ConditionHolds (cond : (BitVec 4)) (nzcv : (BitVec 4)) : Bool :=
  let result : Bool := false
  let result : Bool :=
    match (BitVec.slice cond 1 3) with
    | 0b000 => ((BitVec.access nzcv 2) == 1#1)
    | 0b001 => ((BitVec.access nzcv 1) == 1#1)
    | 0b010 => ((BitVec.access nzcv 3) == 1#1)
    | 0b011 => ((BitVec.access nzcv 0) == 1#1)
    | 0b100 => (((BitVec.access nzcv 1) == 1#1) && ((BitVec.access nzcv 2) == 0#1))
    | 0b101 => ((BitVec.access nzcv 3) == (BitVec.access nzcv 0))
    | 0b110 =>
      (((BitVec.access nzcv 3) == (BitVec.access nzcv 0)) && ((BitVec.access nzcv 2) == 0#1))
    | _ => true
  if ((((BitVec.join1 [(BitVec.access cond 0)]) == 1#1) && (cond != 0xF#4)) : Bool)
  then (! result)
  else result

/-- Type quantifiers: k_ex11527_ : Bool, k_ex11526_ : Bool, k_datasize : Nat, k_datasize ∈
  {32, 64} -/
def integer_conditional_select (condition : (BitVec 4)) (nzcv : (BitVec 4)) (else_inc : Bool) (else_inv : Bool) (operand1 : (BitVec k_datasize)) (operand2 : (BitVec k_datasize)) : (BitVec k_datasize) :=
  let result : (BitVec k_datasize) := operand2
  if ((ConditionHolds condition nzcv) : Bool)
  then operand1
  else
    (let result : (BitVec k_datasize) := operand2
    let result : (BitVec k_datasize) :=
      if (else_inv : Bool)
      then (Complement.complement result)
      else result
    if (else_inc : Bool)
    then (BitVec.addInt result 1)
    else result)

/-- Type quantifiers: k_ex11543_ : Bool, k_datasize : Nat, k_datasize ∈ {32, 64} -/
def integer_conditional_compare_register (condition : (BitVec 4)) (nzcv : (BitVec 4)) (flags__arg : (BitVec 4)) (operand1 : (BitVec k_datasize)) (operand2__arg : (BitVec k_datasize)) (sub_op : Bool) : (BitVec 4) :=
  let flags : (BitVec 4) := flags__arg
  let operand2 : (BitVec k_datasize) := operand2__arg
  let carry_in : (BitVec 1) := 0#1
  let __anon1 : (BitVec k_datasize) := operand1
  if ((ConditionHolds condition nzcv) : Bool)
  then
    (let (carry_in, operand2) : ((BitVec 1) × (BitVec k_datasize)) :=
      if (sub_op : Bool)
      then
        (let operand2 : (BitVec k_datasize) := (Complement.complement operand2)
        let carry_in : (BitVec 1) := 1#1
        (carry_in, operand2))
      else (carry_in, operand2)
    let (tup__0, tup__1) :=
      ((AddWithCarry operand1 operand2 carry_in) : ((BitVec k_datasize) × (BitVec 4)))
    let __anon1 : (BitVec k_datasize) := tup__0
    tup__1)
  else flags

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def HighestSetBit (x : (BitVec k_N)) : Int := ExceptM.run do
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length x) -i 1)
  let mut loop_vars := ()
  for i in [loop_i_upper:loop_i_lower:-1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.join1 [(BitVec.access x i)]) == 1#1) : Bool)
      then throw (i : Int)
      else (pure ())
  (pure loop_vars)
  (pure (Neg.neg 1))

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def CountLeadingZeroBits (x : (BitVec k_N)) : Int :=
  ((Sail.BitVec.length x) -i ((HighestSetBit x) +i 1))

/-- Type quantifiers: pos : Int, n : Int, m : Nat, m ≥ 0 -/
def __SetSlice_bits (n : Int) (m : Nat) (v : (BitVec n)) (pos : Int) (x : (BitVec m)) : (BitVec n) :=
  (set_slice m v pos x)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def Ones (n : Nat) : (BitVec n) :=
  (BitVec.replicateBits 1#1 n)

/-- Type quantifiers: k_N : Nat, k_unsigned : Bool, k_N ≥ 1 -/
def asl_Int (x : (BitVec k_N)) (is_unsigned : Bool) : Int :=
  if (is_unsigned : Bool)
  then (UInt x)
  else (SInt x)

/-- Type quantifiers: k_N : Nat, e : Nat, size : Nat, size ≥ 1 ∧
  e ≥ 0 ∧ ((e + 1) * size) ≤ k_N -/
def aget_Elem (vector_name : (BitVec k_N)) (e : Nat) (size : Nat) : (BitVec size) :=
  (BitVec.slice vector_name (e *i size) size)

/-- Type quantifiers: k_N : Nat, e : Nat, size : Nat, size ≥ 1 ∧
  e ≥ 0 ∧ ((e + 1) * size) ≤ k_N -/
def aset_Elem (vector_name : (BitVec k_N)) (e : Nat) (size : Nat) (value_name : (BitVec size)) : (BitVec k_N) :=
  (__SetSlice_bits (Sail.BitVec.length vector_name) size vector_name (e *i size) value_name)

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitCount (x : (BitVec k_N)) : Int := Id.run do
  let result : Int := 0
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length x) -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars :=
      if (((BitVec.join1 [(BitVec.access x i)]) == 1#1) : Bool)
      then (result +i 1)
      else result
  (pure loop_vars)

/-- Type quantifiers: N : Nat, i : Int, N ≥ 0 -/
def UnsignedSatQ (i : Int) (N : Nat) : ((BitVec N) × Bool) :=
  let result : Int := 0
  let saturated : Bool := false
  let (result, saturated) : (Int × Bool) :=
    if ((i >b ((2 ^i N) -i 1)) : Bool)
    then
      (let result : Int := ((2 ^i N) -i 1)
      let saturated : Bool := true
      (result, saturated))
    else
      (let (result, saturated) : (Int × Bool) :=
        if ((i <b 0) : Bool)
        then
          (let result : Int := 0
          let saturated : Bool := true
          (result, saturated))
        else
          (let result : Int := i
          let saturated : Bool := false
          (result, saturated))
      (result, saturated))
  ((__GetSlice_int N result 0), saturated)

/-- Type quantifiers: N : Nat, i : Int, N ≥ 1 -/
def SignedSatQ (i : Int) (N : Nat) : ((BitVec N) × Bool) :=
  let result : Int := 0
  let saturated : Bool := false
  let (result, saturated) : (Int × Bool) :=
    if ((i >b ((2 ^i (N -i 1)) -i 1)) : Bool)
    then
      (let result : Int := ((2 ^i (N -i 1)) -i 1)
      let saturated : Bool := true
      (result, saturated))
    else
      (let (result, saturated) : (Int × Bool) :=
        if ((i <b (Neg.neg (2 ^i (N -i 1)))) : Bool)
        then
          (let result : Int := (Neg.neg (2 ^i (N -i 1)))
          let saturated : Bool := true
          (result, saturated))
        else
          (let result : Int := i
          let saturated : Bool := false
          (result, saturated))
      (result, saturated))
  ((__GetSlice_int N result 0), saturated)

/-- Type quantifiers: N : Nat, i : Int, k_unsigned : Bool, N ≥ 1 -/
def SatQ (i : Int) (N : Nat) (is_unsigned : Bool) : ((BitVec N) × Bool) :=
  let (result, sat) :=
    if (is_unsigned : Bool)
    then (UnsignedSatQ i N)
    else (SignedSatQ i N)
  (result, sat)

/-- Type quantifiers: datasize : Nat, elements : Nat, esize : Nat, esize ≥ 1 ∧
  elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_transfer_integer_dup (datasize : Nat) (elements : Nat) (esize : Nat) (element : (BitVec esize)) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := result
  for e in [loop_e_lower:loop_e_upper:1]i do
    let result := loop_vars
    loop_vars := (aset_Elem result e esize element)
  (pure loop_vars)

/-- Type quantifiers: k_ex11682_ : Bool, datasize : Nat, elements : Nat, esize : Nat, esize ≥ 1
  ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_add_wrapping_single (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (sub_op : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element1 : (BitVec esize) := (Zeros esize)
  let element2 : (BitVec esize) := (Zeros esize)
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars :=
        let element1 : (BitVec esize) := (aget_Elem operand1 e esize)
        let element2 : (BitVec esize) := (aget_Elem operand2 e esize)
        let result : (BitVec datasize) :=
          if (sub_op : Bool)
          then (aset_Elem result e esize (element1 - element2))
          else (aset_Elem result e esize (element1 + element2))
        (element1, element2, result)
    (pure loop_vars) ) : Id ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: k_ex11750_ : Bool, k_ex11749_ : Bool, datasize : Nat, elements : Nat, esize :
  Nat, esize ≥ 1 ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_maxmin_single (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (minimum : Bool) (is_unsigned : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element1 : Int := 0
  let element2 : Int := 0
  let maxmin : Int := 0
  let (element1, element2, maxmin, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, maxmin, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, maxmin, result) := loop_vars
      loop_vars :=
        let element1 : Int := (asl_Int (aget_Elem operand1 e esize) is_unsigned)
        let element2 : Int := (asl_Int (aget_Elem operand2 e esize) is_unsigned)
        let maxmin : Int :=
          if (minimum : Bool)
          then (Min.min element1 element2)
          else (Max.max element1 element2)
        let result : (BitVec datasize) := (aset_Elem result e esize (__GetSlice_int esize maxmin 0))
        (element1, element2, maxmin, result)
    (pure loop_vars) ) : Id (Int × Int × Int × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: k_ex11801_ : Bool, k_ex11800_ : Bool, datasize : Nat, elements : Nat, esize :
  Nat, esize ≥ 1 ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_cmp_int (cmp_eq : Bool) (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (is_unsigned : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element1 : Int := 0
  let element2 : Int := 0
  let test_passed : Bool := false
  let (element1, element2, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, test_passed) := loop_vars
      loop_vars :=
        let element1 : Int := (asl_Int (aget_Elem operand1 e esize) is_unsigned)
        let element2 : Int := (asl_Int (aget_Elem operand2 e esize) is_unsigned)
        let test_passed : Bool :=
          if (cmp_eq : Bool)
          then (element1 ≥b element2)
          else (element1 >b element2)
        let result : (BitVec datasize) :=
          (aset_Elem result e esize
            (if (test_passed : Bool)
            then (Ones esize)
            else (Zeros esize)))
        (element1, element2, result, test_passed)
    (pure loop_vars) ) : Id (Int × Int × (BitVec datasize) × Bool) )
  (pure result)

/-- Type quantifiers: k_ex11847_ : Bool, datasize : Nat, elements : Nat, esize : Nat, esize ≥ 1
  ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_cmp_bitwise (and_test : Bool) (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element1 : (BitVec esize) := (Zeros esize)
  let element2 : (BitVec esize) := (Zeros esize)
  let test_passed : Bool := false
  let (element1, element2, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, test_passed) := loop_vars
      loop_vars :=
        let element1 : (BitVec esize) := (aget_Elem operand1 e esize)
        let element2 : (BitVec esize) := (aget_Elem operand2 e esize)
        let test_passed : Bool :=
          if (and_test : Bool)
          then (! (IsZero (element1 &&& element2)))
          else (element1 == element2)
        let result : (BitVec datasize) :=
          (aset_Elem result e esize
            (if (test_passed : Bool)
            then (Ones esize)
            else (Zeros esize)))
        (element1, element2, result, test_passed)
    (pure loop_vars) ) : Id ((BitVec esize) × (BitVec esize) × (BitVec datasize) × Bool) )
  (pure result)

def undefined_CompareOp (_ : Unit) : SailM CompareOp := do
  (internal_pick [CompareOp_GT, CompareOp_GE, CompareOp_EQ, CompareOp_LE, CompareOp_LT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def CompareOp_of_num (arg_ : Nat) : CompareOp :=
  match arg_ with
  | 0 => CompareOp_GT
  | 1 => CompareOp_GE
  | 2 => CompareOp_EQ
  | 3 => CompareOp_LE
  | _ => CompareOp_LT

def num_of_CompareOp (arg_ : CompareOp) : Int :=
  match arg_ with
  | .CompareOp_GT => 0
  | .CompareOp_GE => 1
  | .CompareOp_EQ => 2
  | .CompareOp_LE => 3
  | .CompareOp_LT => 4

/-- Type quantifiers: datasize : Nat, elements : Nat, esize : Nat, esize ≥ 1 ∧
  elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_unary_cmp_int_bulk (comparison : CompareOp) (datasize : Nat) (elements : Nat) (esize : Nat) (operand : (BitVec datasize)) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element : Int := 0
  let test_passed : Bool := false
  let (element, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, test_passed) := loop_vars
      loop_vars :=
        let element : Int := (SInt (aget_Elem operand e esize))
        let test_passed : Bool :=
          match comparison with
          | .CompareOp_GT => (element >b 0)
          | .CompareOp_GE => (element ≥b 0)
          | .CompareOp_EQ => (element == 0)
          | .CompareOp_LE => (element ≤b 0)
          | .CompareOp_LT => (element <b 0)
        let result : (BitVec datasize) :=
          (aset_Elem result e esize
            (if (test_passed : Bool)
            then (Ones esize)
            else (Zeros esize)))
        (element, result, test_passed)
    (pure loop_vars) ) : Id (Int × (BitVec datasize) × Bool) )
  (pure result)

/-- Type quantifiers: k_ex11976_ : Bool, datasize : Nat, elements : Nat, esize : Nat, esize ≥ 1
  ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_sub_saturating (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (is_unsigned : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element1 : Int := 0
  let element2 : Int := 0
  let diff : Int := 0
  let (diff, element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (diff, element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (diff, element1, element2, result) := loop_vars
      loop_vars :=
        let element1 : Int := (asl_Int (aget_Elem operand1 e esize) is_unsigned)
        let element2 : Int := (asl_Int (aget_Elem operand2 e esize) is_unsigned)
        let diff : Int := (element1 -i element2)
        let (__tc1, sat) := (SatQ diff esize is_unsigned)
        let result : (BitVec datasize) := (aset_Elem result e esize __tc1)
        (diff, element1, element2, result)
    (pure loop_vars) ) : Id (Int × Int × Int × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: k_ex12027_ : Bool, shift : Int, k_ex12025_ : Bool, k_ex12024_ : Bool, datasize
  : Nat, elements : Nat, esize : Nat, esize ≥ 1 ∧
  elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_shift_right (accumulate : Bool) (datasize : Nat) (elements : Nat) (esize : Nat) (operand : (BitVec datasize)) (accumulator : (BitVec datasize)) (round : Bool) (shift : Int) (is_unsigned : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let round_const : Int :=
    if (round : Bool)
    then (_shl_int_general 1 (shift -i 1))
    else 0
  let element : Int := 0
  let operand2 : (BitVec datasize) :=
    if (accumulate : Bool)
    then accumulator
    else (Zeros datasize)
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars :=
        let element : Int :=
          (_shr_int_general ((asl_Int (aget_Elem operand e esize) is_unsigned) +i round_const) shift)
        let result : (BitVec datasize) :=
          (aset_Elem result e esize
            ((aget_Elem operand2 e esize) + (__GetSlice_int esize element 0)))
        (element, result)
    (pure loop_vars) ) : Id (Int × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: k_ex12080_ : Bool, datasize : Nat, elements : Nat, elements ≥ 1 ∧
  (elements * 8) = datasize ∧ datasize ≤ 128 -/
def vector_transfer_vector_table (datasize : Nat) (elements : Nat) (is_tbl : Bool) (indices : (BitVec datasize)) (table : (BitVec 128)) (dst : (BitVec datasize)) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) :=
    if (is_tbl : Bool)
    then (Zeros datasize)
    else dst
  let loop_i_lower := 0
  let loop_i_upper := (elements -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars :=
      let index := (UInt (aget_Elem indices i 8))
      if ((index <b 16) : Bool)
      then (aset_Elem result i 8 (aget_Elem table index 8))
      else result
  (pure loop_vars)

/-- Type quantifiers: position : Int, datasize : Nat, datasize ≥ 1 -/
def vector_transfer_vector_extract (datasize : Nat) (hi : (BitVec datasize)) (lo : (BitVec datasize)) (position : Int) : (BitVec datasize) :=
  let concat : (BitVec (2 * datasize)) := (hi +++ lo)
  (BitVec.slice concat position datasize)

/-- Type quantifiers: k_ex12112_ : Bool, k_ex12111_ : Bool, datasize : Nat, elements : Nat, esize :
  Nat, esize ≥ 1 ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_reduce_intmax (datasize : Nat) (elements : Nat) (esize : Nat) (operand : (BitVec datasize)) (min : Bool) (is_unsigned : Bool) : (BitVec esize) := Id.run do
  let maxmin : Int := 0
  let element : Int := 0
  let maxmin : Int := (asl_Int (aget_Elem operand 0 esize) is_unsigned)
  let (element, maxmin) ← (( do
    let loop_e_lower := 1
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, maxmin)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, maxmin) := loop_vars
      loop_vars :=
        let element : Int := (asl_Int (aget_Elem operand e esize) is_unsigned)
        let maxmin : Int :=
          if (min : Bool)
          then (Min.min maxmin element)
          else (Max.max maxmin element)
        (element, maxmin)
    (pure loop_vars) ) : Id (Int × Int) )
  (pure (__GetSlice_int esize maxmin 0))

/-- Type quantifiers: datasize : Nat, elements : Nat, esize : Nat, esize ≥ 1 ∧
  elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_unary_cnt (datasize : Nat) (elements : Nat) (esize : Nat) (operand : (BitVec datasize)) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let count : Int := 0
  let (count, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (count, result) := loop_vars
      loop_vars :=
        let count : Int := (BitCount (aget_Elem operand e esize))
        let result : (BitVec datasize) := (aset_Elem result e esize (__GetSlice_int esize count 0))
        (count, result)
    (pure loop_vars) ) : Id (Int × (BitVec datasize)) )
  (pure result)

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

/-- Type quantifiers: k_ex12170_ : Bool, datasize : Nat, datasize ≥ 1 -/
def vector_arithmetic_binary_uniform_logical_andorr (datasize : Nat) (invert : Bool) (operand1 : (BitVec datasize)) (operand2__arg : (BitVec datasize)) (op : LogicalOp) : (BitVec datasize) :=
  let operand2 : (BitVec datasize) := operand2__arg
  let result : (BitVec datasize) := (Zeros datasize)
  let operand2 : (BitVec datasize) :=
    if (invert : Bool)
    then (Complement.complement operand2)
    else operand2
  match op with
  | .LogicalOp_AND => (operand1 &&& operand2)
  | .LogicalOp_ORR => (operand1 ||| operand2)
  | .LogicalOp_EOR => (operand1 ^^^ operand2)

def undefined_VBitOp (_ : Unit) : SailM VBitOp := do
  (internal_pick [VBitOp_VBIF, VBitOp_VBIT, VBitOp_VBSL, VBitOp_VEOR])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def VBitOp_of_num (arg_ : Nat) : VBitOp :=
  match arg_ with
  | 0 => VBitOp_VBIF
  | 1 => VBitOp_VBIT
  | 2 => VBitOp_VBSL
  | _ => VBitOp_VEOR

def num_of_VBitOp (arg_ : VBitOp) : Int :=
  match arg_ with
  | .VBitOp_VBIF => 0
  | .VBitOp_VBIT => 1
  | .VBitOp_VBSL => 2
  | .VBitOp_VEOR => 3

/-- Type quantifiers: datasize : Nat, datasize ≥ 1 -/
def vector_arithmetic_binary_uniform_logical_bsleor (datasize : Nat) (vm : (BitVec datasize)) (vn : (BitVec datasize)) (dst : (BitVec datasize)) (op : VBitOp) : (BitVec datasize) :=
  let operand1 : (BitVec datasize) := (Zeros datasize)
  let operand2 : (BitVec datasize) := (Zeros datasize)
  let operand3 : (BitVec datasize) := (Zeros datasize)
  let operand4 : (BitVec datasize) := vn
  let (operand1, operand2, operand3) : ((BitVec datasize) × (BitVec datasize) × (BitVec datasize)) :=
    match op with
    | .VBitOp_VEOR =>
      (let operand1 : (BitVec datasize) := vm
      let operand2 : (BitVec datasize) := (Zeros datasize)
      let operand3 : (BitVec datasize) := (Ones datasize)
      (operand1, operand2, operand3))
    | .VBitOp_VBSL =>
      (let operand1 : (BitVec datasize) := vm
      let operand2 : (BitVec datasize) := operand1
      let operand3 : (BitVec datasize) := dst
      (operand1, operand2, operand3))
    | .VBitOp_VBIT =>
      (let operand1 : (BitVec datasize) := dst
      let operand2 : (BitVec datasize) := operand1
      let operand3 : (BitVec datasize) := vm
      (operand1, operand2, operand3))
    | .VBitOp_VBIF =>
      (let operand1 : (BitVec datasize) := dst
      let operand2 : (BitVec datasize) := operand1
      let operand3 : (BitVec datasize) := (Complement.complement vm)
      (operand1, operand2, operand3))
  let operand3 := operand3
  let operand2 := operand2
  let operand1 := operand1
  (operand1 ^^^ ((operand2 ^^^ operand4) &&& operand3))

/-- Type quantifiers: k_N : Nat, k_N ≥ 1 -/
def FPNeg (op : (BitVec k_N)) : (BitVec k_N) :=
  ((Complement.complement (BitVec.join1 [(BitVec.access op ((Sail.BitVec.length op) -i 1))])) +++ (BitVec.slice
      op 0 ((Sail.BitVec.length op) -i 1)))

/-- Type quantifiers: k_N : Nat, k_N ≥ 1 -/
def FPAbs (op : (BitVec k_N)) : (BitVec k_N) :=
  (0#1 +++ (BitVec.slice op 0 ((Sail.BitVec.length op) -i 1)))

/-- Type quantifiers: k_ex12329_ : Bool, datasize : Nat, elements : Nat, esize : Nat, esize ∈
  {32, 64} ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_add_fp (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (fpcr : (BitVec 32)) (pair : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let concat : (BitVec (2 * datasize)) := (operand2 +++ operand1)
  let element1 : (BitVec esize) := (Zeros esize)
  let element2 : (BitVec esize) := (Zeros esize)
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars :=
        let (element1, element2) : ((BitVec esize) × (BitVec esize)) :=
          if (pair : Bool)
          then
            (let element1 : (BitVec esize) := (aget_Elem concat (2 *i e) esize)
            let element2 : (BitVec esize) := (aget_Elem concat ((2 *i e) +i 1) esize)
            (element1, element2))
          else
            (let element1 : (BitVec esize) := (aget_Elem operand1 e esize)
            let element2 : (BitVec esize) := (aget_Elem operand2 e esize)
            (element1, element2))
        let result : (BitVec datasize) :=
          (aset_Elem result e esize (Sail.FPAdd element1 element2 fpcr))
        (element1, element2, result)
    (pure loop_vars) ) : Id ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: k_ex12436_ : Bool, datasize : Nat, elements : Nat, esize : Nat, esize ∈
  {32, 64} ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_sub_fp (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (fpcr : (BitVec 32)) (abs : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element1 : (BitVec esize) := (Zeros esize)
  let element2 : (BitVec esize) := (Zeros esize)
  let diff : (BitVec esize) := (Zeros esize)
  let (diff, element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (diff, element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (diff, element1, element2, result) := loop_vars
      loop_vars :=
        let element1 : (BitVec esize) := (aget_Elem operand1 e esize)
        let element2 : (BitVec esize) := (aget_Elem operand2 e esize)
        let diff : (BitVec esize) := (Sail.FPSub element1 element2 fpcr)
        let result : (BitVec datasize) :=
          (aset_Elem result e esize
            (if (abs : Bool)
            then (FPAbs diff)
            else diff))
        (diff, element1, element2, result)
    (pure loop_vars) ) : Id
    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: datasize : Nat, elements : Nat, esize : Nat, esize ∈ {32, 64} ∧
  elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_mul_fp_product (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (fpcr : (BitVec 32)) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element1 : (BitVec esize) := (Zeros esize)
  let element2 : (BitVec esize) := (Zeros esize)
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars :=
        let element1 : (BitVec esize) := (aget_Elem operand1 e esize)
        let element2 : (BitVec esize) := (aget_Elem operand2 e esize)
        let result : (BitVec datasize) :=
          (aset_Elem result e esize (Sail.FPMul element1 element2 fpcr))
        (element1, element2, result)
    (pure loop_vars) ) : Id ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: k_ex12610_ : Bool, datasize : Nat, elements : Nat, esize : Nat, esize ∈
  {32, 64} ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_mul_fp_fused (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (operand3 : (BitVec datasize)) (fpcr : (BitVec 32)) (sub_op : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element1 : (BitVec esize) := (Zeros esize)
  let element2 : (BitVec esize) := (Zeros esize)
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars :=
        let element1 : (BitVec esize) := (aget_Elem operand1 e esize)
        let element2 : (BitVec esize) := (aget_Elem operand2 e esize)
        let element1 : (BitVec esize) :=
          if (sub_op : Bool)
          then (FPNeg element1)
          else element1
        let result : (BitVec datasize) :=
          (aset_Elem result e esize
            (Sail.FPMulAdd (aget_Elem operand3 e esize) element1 element2 fpcr))
        (element1, element2, result)
    (pure loop_vars) ) : Id ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: k_ex12686_ : Bool, k_ex12685_ : Bool, datasize : Nat, elements : Nat, esize :
  Nat, esize ∈ {32, 64} ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_maxmin_fp_1985 (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (fpcr : (BitVec 32)) (minimum : Bool) (pair : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let concat : (BitVec (2 * datasize)) := (operand2 +++ operand1)
  let element1 : (BitVec esize) := (Zeros esize)
  let element2 : (BitVec esize) := (Zeros esize)
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars :=
        let (element1, element2) : ((BitVec esize) × (BitVec esize)) :=
          if (pair : Bool)
          then
            (let element1 : (BitVec esize) := (aget_Elem concat (2 *i e) esize)
            let element2 : (BitVec esize) := (aget_Elem concat ((2 *i e) +i 1) esize)
            (element1, element2))
          else
            (let element1 : (BitVec esize) := (aget_Elem operand1 e esize)
            let element2 : (BitVec esize) := (aget_Elem operand2 e esize)
            (element1, element2))
        let result : (BitVec datasize) :=
          if (minimum : Bool)
          then (aset_Elem result e esize (Sail.FPMin element1 element2 fpcr))
          else (aset_Elem result e esize (Sail.FPMax element1 element2 fpcr))
        (element1, element2, result)
    (pure loop_vars) ) : Id ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: k_ex12784_ : Bool, k_ex12783_ : Bool, datasize : Nat, elements : Nat, esize :
  Nat, esize ∈ {32, 64} ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_binary_uniform_maxmin_fp_2008 (datasize : Nat) (elements : Nat) (esize : Nat) (operand1 : (BitVec datasize)) (operand2 : (BitVec datasize)) (fpcr : (BitVec 32)) (minimum : Bool) (pair : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let concat : (BitVec (2 * datasize)) := (operand2 +++ operand1)
  let element1 : (BitVec esize) := (Zeros esize)
  let element2 : (BitVec esize) := (Zeros esize)
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars :=
        let (element1, element2) : ((BitVec esize) × (BitVec esize)) :=
          if (pair : Bool)
          then
            (let element1 : (BitVec esize) := (aget_Elem concat (2 *i e) esize)
            let element2 : (BitVec esize) := (aget_Elem concat ((2 *i e) +i 1) esize)
            (element1, element2))
          else
            (let element1 : (BitVec esize) := (aget_Elem operand1 e esize)
            let element2 : (BitVec esize) := (aget_Elem operand2 e esize)
            (element1, element2))
        let result : (BitVec datasize) :=
          if (minimum : Bool)
          then (aset_Elem result e esize (Sail.FPMinNum element1 element2 fpcr))
          else (aset_Elem result e esize (Sail.FPMaxNum element1 element2 fpcr))
        (element1, element2, result)
    (pure loop_vars) ) : Id ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: datasize : Nat, elements : Nat, esize : Nat, esize ∈ {32, 64} ∧
  elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_unary_special_sqrt (datasize : Nat) (elements : Nat) (esize : Nat) (operand : (BitVec datasize)) (fpcr : (BitVec 32)) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element : (BitVec esize) := (Zeros esize)
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars :=
        let element : (BitVec esize) := (aget_Elem operand e esize)
        let result : (BitVec datasize) := (aset_Elem result e esize (Sail.FPSqrt element fpcr))
        (element, result)
    (pure loop_vars) ) : Id ((BitVec esize) × (BitVec datasize)) )
  (pure result)

/-- Type quantifiers: k_ex12931_ : Bool, datasize : Nat, elements : Nat, esize : Nat, esize ∈
  {32, 64} ∧ elements ≥ 1 ∧ (elements * esize) = datasize -/
def vector_arithmetic_unary_diffneg_fp (datasize : Nat) (elements : Nat) (esize : Nat) (operand : (BitVec datasize)) (neg : Bool) : (BitVec datasize) := Id.run do
  let result : (BitVec datasize) := (Zeros datasize)
  let element : (BitVec esize) := (Zeros esize)
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars :=
        let element : (BitVec esize) := (aget_Elem operand e esize)
        let element : (BitVec esize) :=
          if (neg : Bool)
          then (FPNeg element)
          else (FPAbs element)
        let result : (BitVec datasize) := (aset_Elem result e esize element)
        (element, result)
    (pure loop_vars) ) : Id ((BitVec esize) × (BitVec datasize)) )
  (pure result)

def undefined_MemBarrierOp (_ : Unit) : SailM MemBarrierOp := do
  (internal_pick
    [MemBarrierOp_DSB, MemBarrierOp_DMB, MemBarrierOp_ISB, MemBarrierOp_SSBB, MemBarrierOp_PSSBB, MemBarrierOp_SB])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def MemBarrierOp_of_num (arg_ : Nat) : MemBarrierOp :=
  match arg_ with
  | 0 => MemBarrierOp_DSB
  | 1 => MemBarrierOp_DMB
  | 2 => MemBarrierOp_ISB
  | 3 => MemBarrierOp_SSBB
  | 4 => MemBarrierOp_PSSBB
  | _ => MemBarrierOp_SB

def num_of_MemBarrierOp (arg_ : MemBarrierOp) : Int :=
  match arg_ with
  | .MemBarrierOp_DSB => 0
  | .MemBarrierOp_DMB => 1
  | .MemBarrierOp_ISB => 2
  | .MemBarrierOp_SSBB => 3
  | .MemBarrierOp_PSSBB => 4
  | .MemBarrierOp_SB => 5

def undefined_MBReqDomain (_ : Unit) : SailM MBReqDomain := do
  (internal_pick
    [MBReqDomain_Nonshareable, MBReqDomain_InnerShareable, MBReqDomain_OuterShareable, MBReqDomain_FullSystem])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def MBReqDomain_of_num (arg_ : Nat) : MBReqDomain :=
  match arg_ with
  | 0 => MBReqDomain_Nonshareable
  | 1 => MBReqDomain_InnerShareable
  | 2 => MBReqDomain_OuterShareable
  | _ => MBReqDomain_FullSystem

def num_of_MBReqDomain (arg_ : MBReqDomain) : Int :=
  match arg_ with
  | .MBReqDomain_Nonshareable => 0
  | .MBReqDomain_InnerShareable => 1
  | .MBReqDomain_OuterShareable => 2
  | .MBReqDomain_FullSystem => 3

def undefined_MBReqTypes (_ : Unit) : SailM MBReqTypes := do
  (internal_pick [MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MBReqTypes_of_num (arg_ : Nat) : MBReqTypes :=
  match arg_ with
  | 0 => MBReqTypes_Reads
  | 1 => MBReqTypes_Writes
  | _ => MBReqTypes_All

def num_of_MBReqTypes (arg_ : MBReqTypes) : Int :=
  match arg_ with
  | .MBReqTypes_Reads => 0
  | .MBReqTypes_Writes => 1
  | .MBReqTypes_All => 2

def undefined_BarrierExecutionTarget (_ : Unit) : SailM BarrierExecutionTarget := do
  (internal_pick
    [BarrierExecutionTarget_DataSynchronizationBarrier, BarrierExecutionTarget_DataMemoryBarrier, BarrierExecutionTarget_InstructionSynchronizationBarrier, BarrierExecutionTarget_SpeculativeSynchronizationBarrierToVA, BarrierExecutionTarget_SpeculativeSynchronizationBarrierToPA, BarrierExecutionTarget_SpeculationBarrier])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def BarrierExecutionTarget_of_num (arg_ : Nat) : BarrierExecutionTarget :=
  match arg_ with
  | 0 => BarrierExecutionTarget_DataSynchronizationBarrier
  | 1 => BarrierExecutionTarget_DataMemoryBarrier
  | 2 => BarrierExecutionTarget_InstructionSynchronizationBarrier
  | 3 => BarrierExecutionTarget_SpeculativeSynchronizationBarrierToVA
  | 4 => BarrierExecutionTarget_SpeculativeSynchronizationBarrierToPA
  | _ => BarrierExecutionTarget_SpeculationBarrier

def num_of_BarrierExecutionTarget (arg_ : BarrierExecutionTarget) : Int :=
  match arg_ with
  | .BarrierExecutionTarget_DataSynchronizationBarrier => 0
  | .BarrierExecutionTarget_DataMemoryBarrier => 1
  | .BarrierExecutionTarget_InstructionSynchronizationBarrier => 2
  | .BarrierExecutionTarget_SpeculativeSynchronizationBarrierToVA => 3
  | .BarrierExecutionTarget_SpeculativeSynchronizationBarrierToPA => 4
  | .BarrierExecutionTarget_SpeculationBarrier => 5

def system_barriers_target_pure (domain : MBReqDomain) (op : MemBarrierOp) (types : MBReqTypes) : BarrierExecutionTarget :=
  match op with
  | .MemBarrierOp_DSB => BarrierExecutionTarget_DataSynchronizationBarrier
  | .MemBarrierOp_DMB => BarrierExecutionTarget_DataMemoryBarrier
  | .MemBarrierOp_ISB => BarrierExecutionTarget_InstructionSynchronizationBarrier
  | .MemBarrierOp_SSBB => BarrierExecutionTarget_SpeculativeSynchronizationBarrierToVA
  | .MemBarrierOp_PSSBB => BarrierExecutionTarget_SpeculativeSynchronizationBarrierToPA
  | .MemBarrierOp_SB => BarrierExecutionTarget_SpeculationBarrier

def system_barriers_decode_pure (opc : (BitVec 2)) (CRm : (BitVec 4)) : (Bool × MemBarrierOp × MBReqDomain × MBReqTypes) :=
  let valid : Bool := true
  let op : MemBarrierOp := MemBarrierOp_DSB
  let domain : MBReqDomain := MBReqDomain_FullSystem
  let types : MBReqTypes := MBReqTypes_All
  let (op, valid) : (MemBarrierOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : MemBarrierOp := MemBarrierOp_DSB
      (op, valid))
    | 0b01 =>
      (let op : MemBarrierOp := MemBarrierOp_DMB
      (op, valid))
    | 0b10 =>
      (let op : MemBarrierOp := MemBarrierOp_ISB
      (op, valid))
    | _ =>
      (let valid : Bool := false
      (op, valid))
  let domain : MBReqDomain :=
    match (BitVec.slice CRm 2 2) with
    | 0b00 => MBReqDomain_OuterShareable
    | 0b01 => MBReqDomain_Nonshareable
    | 0b10 => MBReqDomain_InnerShareable
    | _ => MBReqDomain_FullSystem
  let (domain, op, types) : (MBReqDomain × MemBarrierOp × MBReqTypes) :=
    match (BitVec.slice CRm 0 2) with
    | 0b01 =>
      (let types : MBReqTypes := MBReqTypes_Reads
      (domain, op, types))
    | 0b10 =>
      (let types : MBReqTypes := MBReqTypes_Writes
      (domain, op, types))
    | 0b11 =>
      (let types : MBReqTypes := MBReqTypes_All
      (domain, op, types))
    | _ =>
      (let (domain, op, types) : (MBReqDomain × MemBarrierOp × MBReqTypes) :=
        if (((BitVec.slice CRm 2 2) == 0b01#2) : Bool)
        then
          (let op : MemBarrierOp := MemBarrierOp_PSSBB
          (domain, op, types))
        else
          (let (domain, op, types) : (MBReqDomain × MemBarrierOp × MBReqTypes) :=
            if ((((BitVec.slice CRm 2 2) == 0b00#2) && (opc == 0b00#2)) : Bool)
            then
              (let op : MemBarrierOp := MemBarrierOp_SSBB
              (domain, op, types))
            else
              (let types : MBReqTypes := MBReqTypes_All
              let domain : MBReqDomain := MBReqDomain_FullSystem
              (domain, op, types))
          (domain, op, types))
      (domain, op, types))
  (valid, op, domain, types)

def decode64_barrier_pure (op_code : (BitVec 32)) : (Bool × MemBarrierOp × MBReqDomain × MBReqTypes) :=
  let CRm : (BitVec 4) := (BitVec.slice op_code 8 4)
  if (((op_code &&& 0xFFFFF0FF#32) == 0xD503309F#32) : Bool)
  then (system_barriers_decode_pure 0b00#2 CRm)
  else
    (if (((op_code &&& 0xFFFFF0FF#32) == 0xD50330BF#32) : Bool)
    then (system_barriers_decode_pure 0b01#2 CRm)
    else
      (if (((op_code &&& 0xFFFFF0FF#32) == 0xD50330DF#32) : Bool)
      then (system_barriers_decode_pure 0b10#2 CRm)
      else (false, MemBarrierOp_DSB, MBReqDomain_FullSystem, MBReqTypes_All)))

def undefined_TLBIOperationTarget (_ : Unit) : SailM TLBIOperationTarget := do
  (internal_pick [TLBIOperationTarget_VMALLS12E1IS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def TLBIOperationTarget_of_num (arg_ : Nat) : TLBIOperationTarget :=
  match arg_ with
  | _ => TLBIOperationTarget_VMALLS12E1IS

def num_of_TLBIOperationTarget (arg_ : TLBIOperationTarget) : Int :=
  match arg_ with
  | .TLBIOperationTarget_VMALLS12E1IS => 0

def aarch64_sysops_write_tlbi_target_pure (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) : (Bool × TLBIOperationTarget) :=
  if (((op0 == 0b01#2) && ((op1 == 0b100#3) && ((CRn == 0x8#4) && ((op2 == 0b110#3) && (CRm == 0x3#4))))) : Bool)
  then (true, TLBIOperationTarget_VMALLS12E1IS)
  else (false, TLBIOperationTarget_VMALLS12E1IS)

def decode64_tlbi_target_pure (op_code : (BitVec 32)) : (Bool × TLBIOperationTarget) :=
  let op0 : (BitVec 2) := (BitVec.slice op_code 19 2)
  let op1 : (BitVec 3) := (BitVec.slice op_code 16 3)
  let CRn : (BitVec 4) := (BitVec.slice op_code 12 4)
  let CRm : (BitVec 4) := (BitVec.slice op_code 8 4)
  let op2 : (BitVec 3) := (BitVec.slice op_code 5 3)
  if (((op_code &&& 0xFFF80000#32) == 0xD5080000#32) : Bool)
  then (aarch64_sysops_write_tlbi_target_pure op0 op1 CRn op2 CRm)
  else (false, TLBIOperationTarget_VMALLS12E1IS)

def undefined_PSTATEWriteTarget (_ : Unit) : SailM PSTATEWriteTarget := do
  (internal_pick [PSTATEWriteTarget_DAIFSet])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def PSTATEWriteTarget_of_num (arg_ : Nat) : PSTATEWriteTarget :=
  match arg_ with
  | _ => PSTATEWriteTarget_DAIFSet

def num_of_PSTATEWriteTarget (arg_ : PSTATEWriteTarget) : Int :=
  match arg_ with
  | .PSTATEWriteTarget_DAIFSet => 0

def system_register_cpsr_daifset_target_pure (op2 : (BitVec 3)) (CRm : (BitVec 4)) (op1 : (BitVec 3)) : (Bool × PSTATEWriteTarget × (BitVec 4)) :=
  if (((op1 +++ op2) == 0b011110#6) : Bool)
  then (true, PSTATEWriteTarget_DAIFSet, CRm)
  else (false, PSTATEWriteTarget_DAIFSet, CRm)

def decode64_pstate_write_target_pure (op_code : (BitVec 32)) : (Bool × PSTATEWriteTarget × (BitVec 4)) :=
  let op2 : (BitVec 3) := (BitVec.slice op_code 5 3)
  let CRm : (BitVec 4) := (BitVec.slice op_code 8 4)
  let op1 : (BitVec 3) := (BitVec.slice op_code 16 3)
  if (((op_code &&& 0xFFF8F01F#32) == 0xD500401F#32) : Bool)
  then (system_register_cpsr_daifset_target_pure op2 CRm op1)
  else (false, PSTATEWriteTarget_DAIFSet, CRm)

def system_register_cpsr_daifset_pure (d : (BitVec 1)) (a : (BitVec 1)) (i : (BitVec 1)) (f : (BitVec 1)) (operand : (BitVec 4)) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
  let d_out : (BitVec 1) := (d ||| (BitVec.join1 [(BitVec.access operand 3)]))
  let a_out : (BitVec 1) := (a ||| (BitVec.join1 [(BitVec.access operand 2)]))
  let i_out : (BitVec 1) := (i ||| (BitVec.join1 [(BitVec.access operand 1)]))
  let f_out : (BitVec 1) := (f ||| (BitVec.join1 [(BitVec.access operand 0)]))
  (d_out, a_out, i_out, f_out)

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
