/**************************************************************************/
/* BSD 3-clause Clear License                                             */
/*                                                                        */
/* Copyright (c) 2019                                                     */
/*   Arm Limited (or its affiliates),                                     */
/*   Alasdair Armstrong,                                                  */
/*   Alastair Reid,                                                       */
/*   Thomas Bauereiss,                                                    */
/*   Peter Sewell,                                                        */
/*   Kathryn Gray,                                                        */
/*   Anthony Fox                                                          */
/*                                                                        */
/* All rights reserved.                                                   */
/*                                                                        */
/* Redistribution and use in source and binary forms, with or without     */
/* modification, are permitted (subject to the limitations in the         */
/* disclaimer below) provided that the following conditions are met:      */
/*                                                                        */
/* 	* Redistributions of source code must retain the above            */
/*        copyright notice, this list of conditions and the following     */
/* 	  disclaimer.                                                     */
/*      * Redistributions in binary form must reproduce the above         */
/*        copyright notice, this list of conditions and the following     */
/*        disclaimer in the documentation and/or other materials          */
/* 	  provided with the distribution.                                 */
/* 	* Neither the name of ARM Limited nor the names of its            */
/*        contributors may be used to endorse or promote products         */
/*        derived from this software without specific prior written       */
/*        permission.                                                     */
/*                                                                        */
/* NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE        */
/* GRANTED BY THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT    */
/* HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED            */
/* WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF   */
/* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE               */
/* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE  */
/* LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR    */
/* CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF   */
/* SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        */
/* BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,  */
/* WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE   */
/* OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN */
/* IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                          */
/**************************************************************************/

default Order dec
$include <flow.sail>
$include "return_vector.sail"
$include <arith.sail>
$include <option.sail>
$include <string.sail>
overload ~ = {not_bool, not_vec}
val ediv_nat = pure { lean: "Nat.div" } : forall 'n 'm, 'n >= 0 & 'm > 0.
  (int('n), int('m)) -> int(div('n, 'm))
overload operator / = {ediv_nat}
val eq_anything = pure { lean: "_lean_beq" } : forall ('a : Type). ('a, 'a) -> bool
val neq_anything = pure { lean: "_lean_bne" } : forall ('a : Type). ('a, 'a) -> bool
overload operator == = {eq_anything}
overload operator != = {neq_anything}
val UInt : forall 'n. bits('n) -> {'m, 0 <= 'm <= 2 ^ 'n - 1. int('m)}
function UInt(x) = unsigned(x)
val Zeros : forall 'n, 'n >= 0. int('n) -> bits('n)
function Zeros(n) = sail_zeros(n)
val __GetSlice_int : forall 'n, 'n >= 0. (int('n), int, int) -> bits('n)
function __GetSlice_int(n, m, o) = get_slice_int(n, m, o)

enum LogicalOp = {LogicalOp_AND, LogicalOp_EOR, LogicalOp_ORR}

enum ShiftType = {ShiftType_LSL, ShiftType_LSR, ShiftType_ASR, ShiftType_ROR}

enum BranchType = {
  BranchType_DIRCALL,
  BranchType_INDCALL,
  BranchType_ERET,
  BranchType_DBGEXIT,
  BranchType_RET,
  BranchType_DIR,
  BranchType_INDIR,
  BranchType_EXCEPTION,
  BranchType_RESET,
  BranchType_UNKNOWN
}

struct ProcState = {
  N : bits(1),
  Z : bits(1),
  C : bits(1),
  V : bits(1),
  D : bits(1),
  A : bits(1),
  I : bits(1),
  F : bits(1),
  PAN : bits(1),
  UAO : bits(1),
  DIT : bits(1),
  TCO : bits(1),
  BTYPE : bits(2),
  SS : bits(1),
  IL : bits(1),
  EL : bits(2),
  nRW : bits(1),
  SP : bits(1),
  Q : bits(1),
  GE : bits(4),
  SSBS : bits(1),
  IT : bits(8),
  J : bits(1),
  T : bits(1),
  E : bits(1),
  M : bits(5)
}

union exception = {
  Error_Undefined : unit,
  Error_See : string,
  Error_Implementation_Defined : string,
  Error_ReservedEncoding : unit,
  Error_ExceptionTaken : unit,
  Error_Unpredictable : unit,
  Error_SError : bool
}

register _PC : bits(64)

register __PC_changed : bool

register PSTATE : ProcState

register TCR_EL1 : bits(64)

register TCR_EL2 : bits(64)

register TCR_EL3 : bits(32)

register _R : vector(31, dec, bits(64))

register InGuardedPage : bool

register BTypeNext : bits(2)

register __unconditional : bool

register SEE : int

let EL0 : bits(2) = 0b00

let EL1 : bits(2) = 0b01

let EL2 : bits(2) = 0b10

let EL3 : bits(2) = 0b11

val ZeroExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0.
  (bits('M), int('N)) -> bits('N) effect {escape}

function ZeroExtend__0 (x, N) = {
    assert(N >= 'M);
    Zeros(N - 'M) @ x
}

val ZeroExtend__1 : forall ('M : Int) ('N : Int), 'M >= 0.
  (implicit('N), bits('M)) -> bits('N) effect {escape}

function ZeroExtend__1 (N, x) = ZeroExtend__0(x, N)

overload ZeroExtend = {ZeroExtend__0, ZeroExtend__1}
val UsingAArch32 = impure { lean: "boundaries.UsingAArch32" } : unit -> bool effect {escape, rreg}

val IsInHost = impure { lean: "boundaries.IsInHost" } : unit -> bool effect {escape, rreg, undef}

val SignExtend__1 = impure { lean: "boundaries.SignExtend__1" } : forall ('M : Int) ('N : Int), 'M >= 0.
  (implicit('N), bits('M)) -> bits('N) effect {escape}

val HaveEL = impure { lean: "boundaries.HaveEL" } : bits(2) -> bool effect {escape}

val S1TranslationRegime__0 = impure { lean: "boundaries.S1TranslationRegime__0" } : bits(2) -> bits(2) effect {escape, rreg, undef}

val ELUsingAArch32 = impure { lean: "boundaries.ELUsingAArch32" } : bits(2) -> bool effect {escape, rreg, undef}

val HavePACExt = impure { lean: "boundaries.HavePACExt" } : unit -> bool

val HaveVirtHostExt = impure { lean: "boundaries.HaveVirtHostExt" } : unit -> bool

val ELIsInHost = impure { lean: "boundaries.ELIsInHost" } : bits(2) -> bool effect {escape, rreg, undef}

overload SignExtend = {SignExtend__1}
overload S1TranslationRegime = {S1TranslationRegime__0}
val AddrTop : forall ('IsInstr : Bool).
  (bits(64), bool('IsInstr), bits(2)) -> {'top, 'top in {31, 55, 63}. int('top)} effect {escape, rreg, undef}

function AddrTop (address, IsInstr, el) = {
    assert(HaveEL(el));
    let regime = S1TranslationRegime(el);
    tbi : bits(1) = undefined : bits(1);
    tbid : bits(1) = undefined : bits(1);
    if ELUsingAArch32(regime) then {
        return(31)
    } else {
        match regime {
          ? if ? == EL1 => {
              tbi = if [address[55]] == 0b1 then [TCR_EL1[38]] else [TCR_EL1[37]];
              if HavePACExt() then {
                  tbid = if [address[55]] == 0b1 then [TCR_EL1[52]] else [TCR_EL1[51]]
              }
          },
          ? if ? == EL2 => {
              if HaveVirtHostExt() & ELIsInHost(el) then {
                  tbi = if [address[55]] == 0b1 then [TCR_EL2[38]] else [TCR_EL2[37]];
                  if HavePACExt() then {
                      tbid = if [address[55]] == 0b1 then [TCR_EL2[52]] else [TCR_EL2[51]]
                  }
              } else {
                  tbi = [TCR_EL2[20]];
                  if HavePACExt() then {
                      tbid = [TCR_EL2[29]]
                  }
              }
          },
          ? if ? == EL3 => {
              tbi = [TCR_EL3[20]];
              if HavePACExt() then {
                  tbid = [TCR_EL3[29]]
              }
          }
        }
    };
    if tbi == 0b1 & ((~(HavePACExt()) | tbid == 0b0) | ~(IsInstr)) then 55 else 63
}

val Hint_Branch : BranchType -> unit

function Hint_Branch hint = {
    return()
}

val AArch64_BranchAddr : bits(64) -> bits(64) effect {escape, rreg, undef}

function AArch64_BranchAddr vaddress = {
    assert(~(UsingAArch32()));
    let msbit = AddrTop(vaddress, true, PSTATE.EL);
    assert(msbit + 1 >= 0);
    if msbit == 63 then {
        return(vaddress)
    } else {
        if ((PSTATE.EL == EL0 | PSTATE.EL == EL1) | IsInHost()) & [vaddress[msbit]] == 0b1 then {
            return(SignExtend(slice(vaddress, 0, msbit + 1)))
        } else {
            return(ZeroExtend(slice(vaddress, 0, msbit + 1)))
        }
    }
}

val BranchTo : forall ('N : Int), 'N >= 0.
  (bits('N), BranchType) -> unit effect {escape, rreg, undef, wreg}

function BranchTo (target, branch_type) = {
    Hint_Branch(branch_type);
    if 'N == 32 then {
        assert(UsingAArch32());
        _PC = ZeroExtend(target)
    } else {
        assert('N == 64 & ~(UsingAArch32()));
        _PC = AArch64_BranchAddr(slice(target, 0, 64))
    };
    __PC_changed = true;
    return()
}

