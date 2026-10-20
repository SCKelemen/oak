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

open Register

/-- Type quantifiers: k_ex1981_ : Bool, k_ex1980_ : Bool -/
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

/-- Type quantifiers: k_n : Int -/
def concat_str_bits (str : String) (x : (BitVec k_n)) : String :=
  (HAppend.hAppend str (BitVec.toFormatted x))

/-- Type quantifiers: x : Int -/
def concat_str_dec (str : String) (x : Int) : String :=
  (HAppend.hAppend str (Int.repr x))

def EL1 : (BitVec 2) := 0b01#2

def EL2 : (BitVec 2) := 0b10#2

def EL3 : (BitVec 2) := 0b11#2

def HaveEL (el : (BitVec 2)) : Bool :=
  true

def S1TranslationRegime (el : (BitVec 2)) : (BitVec 2) :=
  0b01#2

def ELUsingAArch32 (el : (BitVec 2)) : Bool :=
  false

def HavePACExt (_ : Unit) : Bool :=
  false

def HaveVirtHostExt (_ : Unit) : Bool :=
  false

def ELIsInHost (el : (BitVec 2)) : Bool :=
  false

/-- Type quantifiers: k_IsInstr : Bool -/
def AddrTop (address : (BitVec 64)) (IsInstr : Bool) (el : (BitVec 2)) : SailM Int := do
  assert (HaveEL el) "original_addr_top.sail:80.21-80.22"
  let regime := (S1TranslationRegime el)
  let tbi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let tbid ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  if ((ELUsingAArch32 regime) : Bool)
  then (pure 31)
  else
    (do
      let questionMark := regime
      if ((questionMark == EL1) : Bool)
      then
        (do
          let tbi ←
            if (((BitVec.join1 [(BitVec.access address 55)]) == 1#1) : Bool)
            then (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL1) 38)]))
            else (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL1) 37)]))
          if ((HavePACExt ()) : Bool)
          then
            (do
              let tbid ←
                if (((BitVec.join1 [(BitVec.access address 55)]) == 1#1) : Bool)
                then (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL1) 52)]))
                else (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL1) 51)]))
              (pure ()))
          else (pure ()))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              if (((HaveVirtHostExt ()) && (ELIsInHost el)) : Bool)
              then
                (do
                  let tbi ←
                    if (((BitVec.join1 [(BitVec.access address 55)]) == 1#1) : Bool)
                    then (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 38)]))
                    else (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 37)]))
                  if ((HavePACExt ()) : Bool)
                  then
                    (do
                      let tbid ←
                        if (((BitVec.join1 [(BitVec.access address 55)]) == 1#1) : Bool)
                        then (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 52)]))
                        else (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 51)]))
                      (pure ()))
                  else (pure ()))
              else
                (do
                  let tbi ← (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 20)]))
                  if ((HavePACExt ()) : Bool)
                  then
                    (do
                      let tbid ← (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 29)]))
                      (pure ()))
                  else (pure ())))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let tbi ← (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL3) 20)]))
                  if ((HavePACExt ()) : Bool)
                  then
                    (do
                      let tbid ← (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL3) 29)]))
                      (pure ()))
                  else (pure ()))
              else
                (do
                  assert false "Pattern match failure at original_addr_top.sail:87.8-113.9"
                  throw Error.Exit)))
      if (((tbi == 1#1) && (((! (HavePACExt ())) || (tbid == 0#1)) || (! IsInstr))) : Bool)
      then (pure 55)
      else (pure 63))

def observe (tcr : (BitVec 64)) : SailM Int := do
  writeReg TCR_EL1 tcr
  (AddrTop 0x0000000000000000#64 true 0b01#2)

def sail_main (_ : Unit) : SailM Unit := do
  (pure (print_int "TBI0=0 -> " (← (observe 0x0000000000000000#64))))
  (pure (print_int "TBI0=1 -> " (← (observe 0x0000002000000000#64))))

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg TCR_EL1 (← (undefined_bitvector 64))
  writeReg TCR_EL2 (← (undefined_bitvector 64))
  writeReg TCR_EL3 (← (undefined_bitvector 32))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Out.Functions

open Out.Functions

def main (_ : List String) : IO UInt32 := do
  main_of_sail_main ⟨default, (), default, default, default, default⟩ (sail_model_init >=> sail_main)
