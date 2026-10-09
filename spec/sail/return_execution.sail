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

enum ArchVersion = {ARMv8p0, ARMv8p1, ARMv8p2, ARMv8p3, ARMv8p4, ARMv8p5}

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

register __highest_el_aarch32 : bool

register SCR_EL3 : bits(32)

register HCR_EL2 : bits(64)

register _R : vector(31, dec, bits(64))

register InGuardedPage : bool

register BTypeNext : bits(2)

register __unconditional : bool

register SEE : int

register configuration CFG_ID_AA64PFR0_EL1_EL0 : bits(4) = 0x2

register configuration CFG_ID_AA64PFR0_EL1_EL1 : bits(4) = 0x2

register configuration CFG_ID_AA64PFR0_EL1_EL2 : bits(4) = 0x2

register configuration CFG_ID_AA64PFR0_EL1_EL3 : bits(4) = 0x2

register configuration __v81_implemented : bool = true

register configuration __v82_implemented : bool = true

register configuration __v83_implemented : bool = true

register configuration __v84_implemented : bool = true

register configuration __v85_implemented : bool = true

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
val IsInHost = impure { lean: "boundaries.IsInHost" } : unit -> bool effect {escape, rreg, undef}

val SignExtend__1 = impure { lean: "boundaries.SignExtend__1" } : forall ('M : Int) ('N : Int), 'M >= 0.
  (implicit('N), bits('M)) -> bits('N) effect {escape}

val ELIsInHost = impure { lean: "boundaries.ELIsInHost" } : bits(2) -> bool effect {escape, rreg, undef}

val get_SCR = impure { lean: "boundaries.get_SCR" } : unit -> bits(32) effect {rreg, undef}

val __IMPDEF_boolean = impure { lean: "boundaries.__IMPDEF_boolean" } : string -> bool effect {escape}

overload SignExtend = {SignExtend__1}
val HaveEL : bits(2) -> bool effect {escape}

function HaveEL el = {
    if el == EL1 | el == EL0 then {
        return(true)
    } else {
        if el == EL2 then {
            return(CFG_ID_AA64PFR0_EL1_EL2 != 0x0)
        } else {
            if el == EL3 then {
                return(CFG_ID_AA64PFR0_EL1_EL3 != 0x0)
            } else {
                assert(false);
                false
            }
        }
    }
}

val HasArchVersion : ArchVersion -> bool

function HasArchVersion version = {
    ((((version == ARMv8p0 | version == ARMv8p1 & __v81_implemented) | version == ARMv8p2 & __v82_implemented) | version == ARMv8p3 & __v83_implemented) | version == ARMv8p4 & __v84_implemented) | version == ARMv8p5 & __v85_implemented
}

val HavePACExt : unit -> bool

function HavePACExt () = {
    HasArchVersion(ARMv8p3)
}

val HaveBTIExt : unit -> bool

function HaveBTIExt () = {
    HasArchVersion(ARMv8p5)
}

val HaveAnyAArch32 : unit -> bool

function HaveAnyAArch32 () = {
    ((CFG_ID_AA64PFR0_EL1_EL0 == 0x2 | CFG_ID_AA64PFR0_EL1_EL1 == 0x2) | CFG_ID_AA64PFR0_EL1_EL2 == 0x2) | CFG_ID_AA64PFR0_EL1_EL3 == 0x2
}

val HighestELUsingAArch32 : unit -> bool effect {rreg}

function HighestELUsingAArch32 () = {
    __highest_el_aarch32
}

val UsingAArch32 : unit -> bool effect {escape, rreg}

function UsingAArch32 () = {
    let aarch32 = PSTATE.nRW == 0b1;
    if ~(HaveAnyAArch32()) then {
        assert(~(aarch32))
    };
    if HighestELUsingAArch32() then {
        assert(aarch32)
    };
    aarch32
}

val HaveVirtHostExt : unit -> bool

function HaveVirtHostExt () = {
    HasArchVersion(ARMv8p1)
}

val HaveSecureEL2Ext : unit -> bool

function HaveSecureEL2Ext () = {
    HasArchVersion(ARMv8p4)
}

val aget_SCR_GEN : unit -> bits(32) effect {escape, rreg, undef}

function aget_SCR_GEN () = {
    assert(HaveEL(EL3));
    r : bits(32) = undefined : bits(32);
    if HighestELUsingAArch32() then {
        r = get_SCR()
    } else {
        r = SCR_EL3
    };
    r
}

overload SCR_GEN = {aget_SCR_GEN}
val HighestEL : unit -> bits(2) effect {escape}

function HighestEL () = {
    if HaveEL(EL3) then {
        return(EL3)
    } else {
        if HaveEL(EL2) then {
            return(EL2)
        } else {
            return(EL1)
        }
    }
}

val IsSecureBelowEL3 : unit -> bool effect {escape, rreg, undef}

function IsSecureBelowEL3 () = {
    if HaveEL(EL3) then {
        return([SCR_GEN()[0]] == 0b0)
    } else {
        if HaveEL(EL2) & (~(HaveSecureEL2Ext()) | HighestELUsingAArch32()) then {
            return(false)
        } else {
            return(__IMPDEF_boolean("Secure-only implementation"))
        }
    }
}

val HaveAArch32EL : bits(2) -> bool effect {escape, rreg}

function HaveAArch32EL el = {
    if ~(HaveEL(el)) then {
        return(false)
    } else {
        if ~(HaveAnyAArch32()) then {
            return(false)
        } else {
            if HighestELUsingAArch32() then {
                return(true)
            } else {
                if el == HighestEL() then {
                    return(false)
                } else {
                    if el == EL0 then {
                        return(true)
                    } else {
                        match el {
                          ? if ? == EL0 => {
                              return(CFG_ID_AA64PFR0_EL1_EL0 == 0x2)
                          },
                          ? if ? == EL1 => {
                              return(CFG_ID_AA64PFR0_EL1_EL1 == 0x2)
                          },
                          ? if ? == EL2 => {
                              return(CFG_ID_AA64PFR0_EL1_EL2 == 0x2)
                          },
                          ? if ? == EL3 => {
                              return(CFG_ID_AA64PFR0_EL1_EL3 == 0x2)
                          }
                        }
                    }
                }
            }
        }
    }
}

val ELStateUsingAArch32K : forall ('secure : Bool).
  (bits(2), bool('secure)) -> (bool, bool) effect {escape, rreg, undef}

function ELStateUsingAArch32K (el, secure) = {
    aarch32 : bool = undefined : bool;
    known : bool = undefined : bool;
    known = true;
    aarch32_at_el1 : bool = undefined : bool;
    aarch32_below_el3 : bool = undefined : bool;
    if ~(HaveAArch32EL(el)) then {
        aarch32 = false
    } else {
        if HighestELUsingAArch32() then {
            aarch32 = true
        } else {
            aarch32_below_el3 = HaveEL(EL3) & [SCR_EL3[10]] == 0b0;
            aarch32_at_el1 = aarch32_below_el3 | ((HaveEL(EL2) & (HaveSecureEL2Ext() & [SCR_EL3[18]] == 0b1 | ~(secure))) & [HCR_EL2[31]] == 0b0) & ~(([HCR_EL2[34]] == 0b1 & [HCR_EL2[27]] == 0b1) & HaveVirtHostExt());
            if el == EL0 & ~(aarch32_at_el1) then {
                if PSTATE.EL == EL0 then {
                    aarch32 = PSTATE.nRW == 0b1
                } else {
                    known = false
                }
            } else {
                aarch32 = aarch32_below_el3 & el != EL3 | aarch32_at_el1 & (el == EL1 | el == EL0)
            }
        }
    };
    if ~(known) then {
        aarch32 = undefined : bool
    };
    return((known, aarch32))
}

val ELStateUsingAArch32 : forall ('secure : Bool).
  (bits(2), bool('secure)) -> bool effect {escape, rreg, undef}

function ELStateUsingAArch32 (el, secure) = {
    aarch32 : bool = undefined : bool;
    known : bool = undefined : bool;
    (known, aarch32) = ELStateUsingAArch32K(el, secure);
    assert(known);
    aarch32
}

val ELUsingAArch32 : bits(2) -> bool effect {escape, rreg, undef}

function ELUsingAArch32 el = {
    ELStateUsingAArch32(el, IsSecureBelowEL3())
}

val S1TranslationRegime__0 : bits(2) -> bits(2) effect {escape, rreg, undef}

function S1TranslationRegime__0 el = {
    if el != EL0 then {
        return(el)
    } else {
        if (HaveEL(EL3) & ELUsingAArch32(EL3)) & [get_SCR()[0]] == 0b0 then {
            return(EL3)
        } else {
            if HaveVirtHostExt() & ELIsInHost(el) then {
                return(EL2)
            } else {
                return(EL1)
            }
        }
    }
}

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

register __currentInstr : bits(32)

register EDSCR : bits(32)

register BTypeCompatible : bool

val AArch64_BranchTargetException = impure { lean: "boundaries.AArch64_BranchTargetException" } : bits(52) -> unit effect {escape, rreg, undef, wreg}

val ThisInstr : unit -> bits(32) effect {rreg}

function ThisInstr () = {
    __currentInstr
}

val ThisInstrAddr : forall ('N : Int).
  implicit('N) -> bits('N) effect {escape, rreg}

function ThisInstrAddr N = {
    assert('N == 64 | 'N == 32 & UsingAArch32());
    slice(_PC, 0, 'N)
}

val Halted : unit -> bool effect {rreg}

function Halted () = {
    ~(slice(EDSCR, 0, 6) == 0b000001 | slice(EDSCR, 0, 6) == 0b000010)
}

val AArch64_ExecutingBTIInstr : unit -> bool effect {rreg, undef}

function AArch64_ExecutingBTIInstr () = {
    if ~(HaveBTIExt()) then {
        return(false)
    };
    let instr = ThisInstr();
    CRm : bits(4) = undefined : bits(4);
    op2 : bits(3) = undefined : bits(3);
    if (slice(instr, 22, 10) == 0b1101010100 & slice(instr, 12, 10) == 0b0000110010) & slice(instr, 0, 5) == 0b11111 then {
        CRm = slice(instr, 8, 4);
        op2 = slice(instr, 5, 3);
        return(CRm == 0x4 & [op2[0]] == 0b0)
    } else {
        return(false)
    }
}

val AArch64_ExecutingBROrBLROrRetInstr : unit -> bool effect {rreg, undef}

function AArch64_ExecutingBROrBLROrRetInstr () = {
    if ~(HaveBTIExt()) then {
        return(false)
    };
    let instr = ThisInstr();
    opc : bits(4) = undefined : bits(4);
    if slice(instr, 25, 7) == 0b1101011 & slice(instr, 16, 5) == 0b11111 then {
        opc = slice(instr, 21, 4);
        return(opc != 0x5)
    } else {
        return(false)
    }
}

val BranchTargetCheck : unit -> unit effect {escape, rreg, undef, wreg}

function BranchTargetCheck () = {
    assert(HaveBTIExt() & ~(UsingAArch32()));
    if ((InGuardedPage & PSTATE.BTYPE != 0b00) & ~(BTypeCompatible)) & ~(Halted()) then {
        let pc : bits(64) = ThisInstrAddr();
        AArch64_BranchTargetException(slice(pc, 0, 52))
    };
    let branch_instr = AArch64_ExecutingBROrBLROrRetInstr();
    let bti_instr = AArch64_ExecutingBTIInstr();
    if ~(branch_instr | bti_instr) then {
        BTypeNext = 0b00
    }
}

