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

/-- Type quantifiers: k_ex1974_ : Bool, k_ex1973_ : Bool -/
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

/-- Type quantifiers: k_ex2158_ : Bool, k_ex2157_ : Bool, k_datasize : Nat, k_datasize ∈ {32, 64} -/
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

/-- Type quantifiers: k_ex2174_ : Bool, k_datasize : Nat, k_datasize ∈ {32, 64} -/
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

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
