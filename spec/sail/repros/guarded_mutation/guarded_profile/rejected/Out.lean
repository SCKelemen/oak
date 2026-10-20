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

/-- Type quantifiers: k_ex1128_ : Bool, k_ex1127_ : Bool -/
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

/-- Type quantifiers: n : Int, k_ex1225_ : Bool -/
def nested (early : Bool) (n : Int) : Int :=
  let x : Int := 3
  let y : Int := 7
  if (early : Bool)
  then 31
  else
    (let (x, y) : (Int × Int) :=
      let questionMark := n
      let (x, y) : (Int × Int) :=
        if ((questionMark == 1) : Bool)
        then
          (let (x, y) : (Int × Int) :=
            match n with
            | questionMark =>
              (let x : Int := 11
              let y : Int := 13
              (x, y))
          (x, y))
        else
          (let (x, y) : (Int × Int) :=
            if ((questionMark == 2) : Bool)
            then
              (let x : Int := 19
              (x, y))
            else
              (let y : Int := 23
              (x, y))
          (x, y))
      (x, y)
    ((x *i 100) +i y))

/-- Type quantifiers: n : Int, k_ex1253_ : Bool -/
def shadow_case (early : Bool) (n : Int) : SailM Int := do
  let x : Int := 5
  if (early : Bool)
  then (pure 31)
  else
    (do
      let questionMark := n
      if ((questionMark == 1) : Bool)
      then
        (let tempval := 9
        (pure (tempval +i 1)))
      else
        (do
          let x := 99
          assert (x == 99) "liveness.sail:23.36-23.37"
          (pure x)))

def sail_main (_ : Unit) : SailM Unit := do
  let _ : Unit := (print_int "nested false1=" (nested false 1))
  let _ : Unit := (print_int "nested false2=" (nested false 2))
  let _ : Unit := (print_int "nested false0=" (nested false 0))
  let _ : Unit := (print_int "nested true1=" (nested true 1))
  (pure (print_int "shadow_case false1=" (← (shadow_case false 1))))
  (pure (print_int "shadow_case false0=" (← (shadow_case false 0))))

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions

open Out.Functions

def main (_ : List String) : IO UInt32 := do
  main_of_sail_main ⟨default, (), default, default, default, default⟩ sail_main
