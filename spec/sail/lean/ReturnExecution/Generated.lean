import Sail
import ReturnExecution.Defs
import ReturnExecution.Interface

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

namespace ReturnExecution.Functions
open PreSail

open option
open exception
open ShiftType
open Register
open LogicalOp
open BranchType
open ArchVersion

/-- Type quantifiers: k_ex6688_ : Bool, k_ex6687_ : Bool -/
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

def EL2 : (BitVec 2) := 0b10#2

def EL3 : (BitVec 2) := 0b11#2

/-- Type quantifiers: k_M : Nat, N : Int, k_M ≥ 0 -/
def ZeroExtend__0 (x : (BitVec k_M)) (N : Int) : SailM (BitVec N) := do
  assert (N ≥b (Sail.BitVec.length x)) "return.sail:183.18-183.19"
  (pure ((Zeros (N -i (Sail.BitVec.length x))) +++ x))

/-- Type quantifiers: k_M : Nat, N : Int, k_M ≥ 0 -/
def ZeroExtend__1 {N : _} (x : (BitVec k_M)) : SailM (BitVec N) := do
  (ZeroExtend__0 x N)

def HaveEL (el : (BitVec 2)) : SailM Bool := do
  if (((el == EL1) || (el == EL0)) : Bool)
  then (pure true)
  else
    (do
      if ((el == EL2) : Bool)
      then (pure ((← readReg CFG_ID_AA64PFR0_EL1_EL2) != 0x0#4))
      else
        (do
          if ((el == EL3) : Bool)
          then (pure ((← readReg CFG_ID_AA64PFR0_EL1_EL3) != 0x0#4))
          else
            (do
              assert false "return.sail:217.28-217.29"
              throw Error.Exit)))

def HasArchVersion (version : ArchVersion) : SailM Bool := do
  (pure ((((((version == ARMv8p0) || ((version == ARMv8p1) && (← readReg __v81_implemented))) || ((version == ARMv8p2) && (← readReg __v82_implemented))) || ((version == ARMv8p3) && (← readReg __v83_implemented))) || ((version == ARMv8p4) && (← readReg __v84_implemented))) || ((version == ARMv8p5) && (← readReg __v85_implemented))))

def HavePACExt (_ : Unit) : SailM Bool := do
  (HasArchVersion ARMv8p3)

def HaveAnyAArch32 (_ : Unit) : SailM Bool := do
  (pure (((((← readReg CFG_ID_AA64PFR0_EL1_EL0) == 0x2#4) || ((← readReg CFG_ID_AA64PFR0_EL1_EL1) == 0x2#4)) || ((← readReg CFG_ID_AA64PFR0_EL1_EL2) == 0x2#4)) || ((← readReg CFG_ID_AA64PFR0_EL1_EL3) == 0x2#4)))

def HighestELUsingAArch32 (_ : Unit) : SailM Bool := do
  readReg __highest_el_aarch32

def UsingAArch32 (_ : Unit) : SailM Bool := do
  let aarch32 ← do (pure ((← readReg PSTATE).nRW == 1#1))
  if ((! (← (HaveAnyAArch32 ()))) : Bool)
  then assert (! aarch32) "return.sail:253.25-253.26"
  else (pure ())
  if ((← (HighestELUsingAArch32 ())) : Bool)
  then assert aarch32 "return.sail:256.22-256.23"
  else (pure ())
  (pure aarch32)

def HaveVirtHostExt (_ : Unit) : SailM Bool := do
  (HasArchVersion ARMv8p1)

def HaveSecureEL2Ext (_ : Unit) : SailM Bool := do
  (HasArchVersion ARMv8p4)

def aget_SCR_GEN (boundaries : Boundaries) (_ : Unit) : SailM (BitVec 32) := do
  assert (← (HaveEL EL3)) "return.sail:276.22-276.23"
  let r ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  if ((← (HighestELUsingAArch32 ())) : Bool)
  then
    (do
      (boundaries.get_SCR ()))
  else
    (do
      readReg SCR_EL3)

def HighestEL (_ : Unit) : SailM (BitVec 2) := do
  if ((← (HaveEL EL3)) : Bool)
  then (pure EL3)
  else
    (do
      if ((← (HaveEL EL2)) : Bool)
      then (pure EL2)
      else (pure EL1))

def IsSecureBelowEL3 (boundaries : Boundaries) (_ : Unit) : SailM Bool := do
  if ((← (HaveEL EL3)) : Bool)
  then (pure ((BitVec.join1 [(BitVec.access (← (aget_SCR_GEN boundaries ())) 0)]) == 0#1))
  else
    (do
      if (((← (HaveEL EL2)) && ((! (← (HaveSecureEL2Ext ()))) || (← (HighestELUsingAArch32 ())))) : Bool)
      then (pure false)
      else (boundaries.__IMPDEF_boolean "Secure-only implementation"))

def HaveAArch32EL (el : (BitVec 2)) : SailM Bool := do
  if ((! (← (HaveEL el))) : Bool)
  then (pure false)
  else
    (do
      if ((! (← (HaveAnyAArch32 ()))) : Bool)
      then (pure false)
      else
        (do
          if ((← (HighestELUsingAArch32 ())) : Bool)
          then (pure true)
          else
            (do
              if ((el == (← (HighestEL ()))) : Bool)
              then (pure false)
              else
                (do
                  if ((el == EL0) : Bool)
                  then (pure true)
                  else
                    (do
                      let questionMark := el
                      if ((questionMark == EL0) : Bool)
                      then (pure ((← readReg CFG_ID_AA64PFR0_EL1_EL0) == 0x2#4))
                      else
                        (do
                          if ((questionMark == EL1) : Bool)
                          then (pure ((← readReg CFG_ID_AA64PFR0_EL1_EL1) == 0x2#4))
                          else
                            (do
                              if ((questionMark == EL2) : Bool)
                              then (pure ((← readReg CFG_ID_AA64PFR0_EL1_EL2) == 0x2#4))
                              else
                                (do
                                  if ((questionMark == EL3) : Bool)
                                  then (pure ((← readReg CFG_ID_AA64PFR0_EL1_EL3) == 0x2#4))
                                  else
                                    (do
                                      assert false "Pattern match failure at return.sail:333.24-346.25"
                                      throw Error.Exit)))))))))

/-- Type quantifiers: k_secure : Bool -/
def ELStateUsingAArch32K (el : (BitVec 2)) (secure : Bool) : SailM (Bool × Bool) := do
  let aarch32 ← (( do (undefined_bool ()) ) : SailM Bool )
  let known ← (( do (undefined_bool ()) ) : SailM Bool )
  let known : Bool := true
  let aarch32_at_el1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let aarch32_below_el3 ← (( do (undefined_bool ()) ) : SailM Bool )
  let (aarch32, known) ← (( do
    if ((! (← (HaveAArch32EL el))) : Bool)
    then
      (let aarch32 : Bool := false
      (pure (aarch32, known)))
    else
      (do
        let (aarch32, known) ← (( do
          if ((← (HighestELUsingAArch32 ())) : Bool)
          then
            (let aarch32 : Bool := true
            (pure (aarch32, known)))
          else
            (do
              let aarch32_below_el3 ←
                (pure ((← (HaveEL EL3)) && ((BitVec.join1 [(BitVec.access (← readReg SCR_EL3) 10)]) == 0#1)))
              let aarch32_at_el1 ←
                (pure (aarch32_below_el3 || ((((← (HaveEL EL2)) && (((← (HaveSecureEL2Ext ())) && ((BitVec.join1 [(BitVec.access
                                    (← readReg SCR_EL3) 18)]) == 1#1)) || (! secure))) && ((BitVec.join1 [(BitVec.access
                              (← readReg HCR_EL2) 31)]) == 0#1)) && (! ((((BitVec.join1 [(BitVec.access
                                  (← readReg HCR_EL2) 34)]) == 1#1) && ((BitVec.join1 [(BitVec.access
                                  (← readReg HCR_EL2) 27)]) == 1#1)) && (← (HaveVirtHostExt ())))))))
              let (aarch32, known) ← (( do
                if (((el == EL0) && (! aarch32_at_el1)) : Bool)
                then
                  (do
                    let (aarch32, known) ← (( do
                      if (((← readReg PSTATE).EL == EL0) : Bool)
                      then
                        (do
                          let aarch32 ← (pure ((← readReg PSTATE).nRW == 1#1))
                          (pure (aarch32, known)))
                      else
                        (let known : Bool := false
                        (pure (aarch32, known))) ) : SailM (Bool × Bool) )
                    (pure (aarch32, known)))
                else
                  (let aarch32 : Bool :=
                    ((aarch32_below_el3 && (el != EL3)) || (aarch32_at_el1 && ((el == EL1) || (el == EL0))))
                  (pure (aarch32, known))) ) : SailM (Bool × Bool) )
              (pure (aarch32, known))) ) : SailM (Bool × Bool) )
        (pure (aarch32, known))) ) : SailM (Bool × Bool) )
  let aarch32 ← (( do
    if ((! known) : Bool)
    then
      (do
        (undefined_bool ()))
    else (pure aarch32) ) : SailM Bool )
  (pure (known, aarch32))

/-- Type quantifiers: k_secure : Bool -/
def ELStateUsingAArch32 (el : (BitVec 2)) (secure : Bool) : SailM Bool := do
  let aarch32 ← (( do (undefined_bool ()) ) : SailM Bool )
  let known ← (( do (undefined_bool ()) ) : SailM Bool )
  let (aarch32, known) ← (( do
    let (tup__0, tup__1) ← do (ELStateUsingAArch32K el secure)
    let known : Bool := tup__0
    let aarch32 : Bool := tup__1
    (pure (aarch32, known)) ) : SailM (Bool × Bool) )
  assert known "return.sail:395.16-395.17"
  (pure aarch32)

def ELUsingAArch32 (boundaries : Boundaries) (el : (BitVec 2)) : SailM Bool := do
  (ELStateUsingAArch32 el (← (IsSecureBelowEL3 boundaries ())))

def S1TranslationRegime__0 (boundaries : Boundaries) (el : (BitVec 2)) : SailM (BitVec 2) := do
  if ((el != EL0) : Bool)
  then (pure el)
  else
    (do
      if ((((← (HaveEL EL3)) && (← (ELUsingAArch32 boundaries EL3))) && ((BitVec.join1 [(BitVec.access
                 (← (boundaries.get_SCR ())) 0)]) == 0#1)) : Bool)
      then (pure EL3)
      else
        (do
          if (((← (HaveVirtHostExt ())) && (← (boundaries.ELIsInHost el))) : Bool)
          then (pure EL2)
          else (pure EL1)))

/-- Type quantifiers: k_IsInstr : Bool -/
def AddrTop (boundaries : Boundaries) (address : (BitVec 64)) (IsInstr : Bool) (el : (BitVec 2)) : SailM Int := do
  assert (← (HaveEL el)) "return.sail:428.21-428.22"
  let regime ← do (S1TranslationRegime__0 boundaries el)
  let tbi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let tbid ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  if ((← (ELUsingAArch32 boundaries regime)) : Bool)
  then (pure 31)
  else
    (do
      let (tbi, tbid) ← (( do
        let questionMark := regime
        let (tbi, tbid) ← (( do
          if ((questionMark == EL1) : Bool)
          then
            (do
              let tbi ←
                if (((BitVec.join1 [(BitVec.access address 55)]) == 1#1) : Bool)
                then (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL1) 38)]))
                else (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL1) 37)]))
              let tbid ← (( do
                if ((← (HavePACExt ())) : Bool)
                then
                  (do
                    if (((BitVec.join1 [(BitVec.access address 55)]) == 1#1) : Bool)
                    then (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL1) 52)]))
                    else (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL1) 51)])))
                else (pure tbid) ) : SailM (BitVec 1) )
              (pure (tbi, tbid)))
          else
            (do
              let (tbi, tbid) ← (( do
                if ((questionMark == EL2) : Bool)
                then
                  (do
                    let (tbi, tbid) ← (( do
                      if (((← (HaveVirtHostExt ())) && (← (boundaries.ELIsInHost el))) : Bool)
                      then
                        (do
                          let tbi ←
                            if (((BitVec.join1 [(BitVec.access address 55)]) == 1#1) : Bool)
                            then (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 38)]))
                            else (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 37)]))
                          let tbid ← (( do
                            if ((← (HavePACExt ())) : Bool)
                            then
                              (do
                                if (((BitVec.join1 [(BitVec.access address 55)]) == 1#1) : Bool)
                                then
                                  (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 52)]))
                                else
                                  (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 51)])))
                            else (pure tbid) ) : SailM (BitVec 1) )
                          (pure (tbi, tbid)))
                      else
                        (do
                          let tbi ←
                            (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 20)]))
                          let tbid ← (( do
                            if ((← (HavePACExt ())) : Bool)
                            then
                              (do
                                (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 29)])))
                            else (pure tbid) ) : SailM (BitVec 1) )
                          (pure (tbi, tbid))) ) : SailM ((BitVec 1) × (BitVec 1)) )
                    (pure (tbi, tbid)))
                else
                  (do
                    let (tbi, tbid) ← (( do
                      if ((questionMark == EL3) : Bool)
                      then
                        (do
                          let tbi ←
                            (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL3) 20)]))
                          let tbid ← (( do
                            if ((← (HavePACExt ())) : Bool)
                            then
                              (do
                                (pure (BitVec.join1 [(BitVec.access (← readReg TCR_EL3) 29)])))
                            else (pure tbid) ) : SailM (BitVec 1) )
                          (pure (tbi, tbid)))
                      else
                        (do
                          assert false "Pattern match failure at return.sail:435.8-461.9"
                          throw Error.Exit) ) : SailM ((BitVec 1) × (BitVec 1)) )
                    (pure (tbi, tbid))) ) : SailM ((BitVec 1) × (BitVec 1)) )
              (pure (tbi, tbid))) ) : SailM ((BitVec 1) × (BitVec 1)) )
        (pure (tbi, tbid)) ) : SailM ((BitVec 1) × (BitVec 1)) )
      if (((tbi == 1#1) && (((! (← (HavePACExt ()))) || (tbid == 0#1)) || (! IsInstr))) : Bool)
      then (pure 55)
      else (pure 63))

def Hint_Branch (hint : BranchType) : Unit :=
  ()

def AArch64_BranchAddr (boundaries : Boundaries) (vaddress : (BitVec 64)) : SailM (BitVec 64) := do
  assert (! (← (UsingAArch32 ()))) "return.sail:475.28-475.29"
  let msbit ← do (AddrTop boundaries vaddress true (← readReg PSTATE).EL)
  assert ((msbit +i 1) ≥b 0) "return.sail:477.25-477.26"
  if ((msbit == 63) : Bool)
  then (pure vaddress)
  else
    (do
      if ((((((← readReg PSTATE).EL == EL0) || ((← readReg PSTATE).EL == EL1)) || (← (boundaries.IsInHost
                 ()))) && ((BitVec.join1 [(BitVec.access vaddress msbit)]) == 1#1)) : Bool)
      then (boundaries.SignExtend__1 (BitVec.slice vaddress 0 (msbit +i 1)))
      else (ZeroExtend__1 (N := 64) (BitVec.slice vaddress 0 (msbit +i 1))))

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BranchTo (boundaries : Boundaries) (target : (BitVec k_N)) (branch_type : BranchType) : SailM Unit := do
  let _ : Unit := (Hint_Branch branch_type)
  if (((Sail.BitVec.length target) == 32) : Bool)
  then
    (do
      assert (← (UsingAArch32 ())) "return.sail:495.29-495.30"
      writeReg _PC (← (ZeroExtend__1 (N := 64) target)))
  else
    (do
      assert (((Sail.BitVec.length target) == 64) && (! (← (UsingAArch32 ())))) "return.sail:498.43-498.44"
      writeReg _PC (← (AArch64_BranchAddr boundaries (BitVec.slice target 0 64))))
  writeReg __PC_changed true

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg _PC (← (undefined_bitvector 64))
  writeReg __PC_changed (← (undefined_bool ()))
  writeReg PSTATE (← (undefined_ProcState ()))
  writeReg TCR_EL1 (← (undefined_bitvector 64))
  writeReg TCR_EL2 (← (undefined_bitvector 64))
  writeReg TCR_EL3 (← (undefined_bitvector 32))
  writeReg __highest_el_aarch32 (← (undefined_bool ()))
  writeReg SCR_EL3 (← (undefined_bitvector 32))
  writeReg HCR_EL2 (← (undefined_bitvector 64))
  writeReg _R (← (undefined_vector 31 (← (undefined_bitvector 64))))
  writeReg InGuardedPage (← (undefined_bool ()))
  writeReg BTypeNext (← (undefined_bitvector 2))
  writeReg __unconditional (← (undefined_bool ()))
  writeReg SEE (← (undefined_int ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  writeReg CFG_ID_AA64PFR0_EL1_EL0 0x2#4
  writeReg CFG_ID_AA64PFR0_EL1_EL1 0x2#4
  writeReg CFG_ID_AA64PFR0_EL1_EL2 0x2#4
  writeReg CFG_ID_AA64PFR0_EL1_EL3 0x2#4
  writeReg __v81_implemented true
  writeReg __v82_implemented true
  writeReg __v83_implemented true
  writeReg __v84_implemented true
  writeReg __v85_implemented true
  (initialize_registers ())

end ReturnExecution.Functions
