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


/* Intact source extraction; explicit impure callee boundaries; selected decoder only. */
default Order dec
$include <flow.sail>
$include "scalar_execution_vector.sail"
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

overload operator ^ = {xor_vec}
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

register _R : vector(31, dec, bits(64))

register PSTATE : ProcState

register InGuardedPage : bool

register BTypeNext : bits(2)

register __unconditional : bool

register SEE : int

val ZeroExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0.
  (bits('M), int('N)) -> bits('N) effect {escape}

function ZeroExtend__0 (x, N) = {
    assert(N >= 'M);
    Zeros(N - 'M) @ x
}

overload ZeroExtend = {ZeroExtend__0}

val aget_X : forall 'width 'n,
  ('n >= 0 & 'n <= 31 & 'width in {8, 16, 32, 64}).
  (implicit('width), int('n)) -> bits('width) effect {rreg}

function aget_X (width, n) = if n != 31 then slice(_R[n], 0, width) else Zeros(width)

val aset_X : forall ('width : Int) ('n : Int), ('n >= 0 & 'n <= 31).
  (int('n), bits('width)) -> unit effect {escape, wreg}

function aset_X (n, value_name) = {
    assert('width == 32 | 'width == 64);
    if n != 31 then _R[n] = ZeroExtend(value_name, 64)
    else ();
    return()
}

overload X = {aget_X, aset_X}

val LSL_C = impure { lean: "boundaries.LSL_C" } : forall ('N : Int) ('shift : Int), 'N >= 0.
  (bits('N), int('shift)) -> (bits('N), bits(1)) effect {escape}

val LSL : forall ('N : Int) ('shift : Int), ('shift >= 0 & 'N >= 0).
  (bits('N), int('shift)) -> bits('N) effect {escape, undef}

function LSL (x, shift) = {
    assert(shift >= 0);
    __anon1 : bits(1) = undefined : bits(1);
    result : bits('N) = undefined : bits('N);
    if shift == 0 then result = x
    else (result, __anon1) = LSL_C(x, shift);
    result
}

val LSR = impure { lean: "boundaries.LSR" } : forall ('N : Int) ('shift : Int), ('shift >= 0 & 'N >= 0).
  (bits('N), int('shift)) -> bits('N) effect {escape, undef}

val ASR = impure { lean: "boundaries.ASR" } : forall ('N : Int) ('shift : Int), ('shift >= 0 & 'N >= 0).
  (bits('N), int('shift)) -> bits('N) effect {escape, undef}

val ROR = impure { lean: "boundaries.ROR" } : forall ('N : Int) ('shift : Int), ('N >= 0 & 'shift >= 0).
  (bits('N), int('shift)) -> bits('N) effect {escape, undef}

val HaveBTIExt = impure { lean: "boundaries.HaveBTIExt" } : unit -> bool

val UsingAArch32 = impure { lean: "boundaries.UsingAArch32" } : unit -> bool effect {escape, rreg}

val BranchTargetCheck = impure { lean: "boundaries.BranchTargetCheck" } : unit -> unit effect {escape, rreg, undef, wreg}

val HavePACExt = impure { lean: "boundaries.HavePACExt" } : unit -> bool

val aget_SP = impure { lean: "boundaries.aget_SP" } : forall ('width : Int).
  implicit('width) -> bits('width) effect {escape, rreg}

val AuthIA = impure { lean: "boundaries.AuthIA" } : (bits(64), bits(64)) -> bits(64) effect {escape, rreg, undef, wreg}

val AuthIB = impure { lean: "boundaries.AuthIB" } : (bits(64), bits(64)) -> bits(64) effect {escape, rreg, undef, wreg}

val aget_PC = impure { lean: "boundaries.aget_PC" } : unit -> bits(64) effect {rreg}

val BranchTo = impure { lean: "boundaries.BranchTo" } : forall ('N : Int), 'N >= 0.
  (bits('N), BranchType) -> unit effect {escape, rreg, undef, wreg}

overload SP = {aget_SP}
overload PC = {aget_PC}

val IsZero : forall ('N : Int), 'N >= 0. bits('N) -> bool

function IsZero x = {
    x == Zeros('N)
}

val IsZeroBit : forall ('N : Int), 'N >= 0. bits('N) -> bits(1)

function IsZeroBit x = {
    if IsZero(x) then 0b1 else 0b0
}

val DecodeShift : bits(2) -> ShiftType

function DecodeShift op = {
    match op {
      0b00 => {
          return(ShiftType_LSL)
      },
      0b01 => {
          return(ShiftType_LSR)
      },
      0b10 => {
          return(ShiftType_ASR)
      },
      0b11 => {
          return(ShiftType_ROR)
      }
    }
}

val ShiftReg : forall 'N 'reg 'amount,
  ('reg >= 0 & 'reg <= 31 & 'N in {8, 16, 32, 64}) & 'amount >= 0.
  (implicit('N), int('reg), ShiftType, int('amount)) -> bits('N) effect {escape, rreg, undef}

function ShiftReg (N, reg, typ, amount) = {
    result : bits('N) = X(reg);
    match typ {
      ShiftType_LSL => {
          result = LSL(result, amount)
      },
      ShiftType_LSR => {
          result = LSR(result, amount)
      },
      ShiftType_ASR => {
          result = ASR(result, amount)
      },
      ShiftType_ROR => {
          result = ROR(result, amount)
      }
    };
    result
}

val __PostDecode : unit -> unit effect {escape, rreg, undef, wreg}

function __PostDecode () = {
    if HaveBTIExt() & ~(UsingAArch32()) then {
        BranchTargetCheck()
    }
}

val integer_logical_shiftedreg : forall 'd 'datasize ('invert : Bool) 'm 'n ('setflags : Bool) 'shift_amount,
  ('n >= 0 & 'n <= 31 & 'datasize in {8, 16, 32, 64}) & ('m >= 0 & 'm <= 31) & 'shift_amount >= 0 & ('d >= 0 & 'd <= 31).
  (int('d), int('datasize), bool('invert), int('m), int('n), LogicalOp, bool('setflags), int('shift_amount), ShiftType) -> unit effect {escape, rreg, undef, wreg}

function integer_logical_shiftedreg (d, datasize, invert, m, n, op, setflags, shift_amount, shift_type) = {
    let operand1 : bits('datasize) = X(n);
    operand2 : bits('datasize) = ShiftReg(m, shift_type, shift_amount);
    if invert then {
        operand2 = ~(operand2)
    };
    result : bits('datasize) = undefined : bits('datasize);
    match op {
      LogicalOp_AND => {
          result = operand1 & operand2
      },
      LogicalOp_ORR => {
          result = operand1 | operand2
      },
      LogicalOp_EOR => {
          result = operand1 ^ operand2
      }
    };
    let result = result;
    if setflags then {
        (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = ([result[datasize - 1]] @ IsZeroBit(result)) @ 0b00
    };
    X(d) = result
}

val integer_logical_shiftedreg_decode : (bits(5), bits(5), bits(6), bits(5), bits(1), bits(2), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function integer_logical_shiftedreg_decode (Rd, Rn, imm6, Rm, N, shift, opc, sf) = {
    __unconditional = true;
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'datasize = if sf == 0b1 then 64 else 32;
    setflags : bool = undefined : bool;
    op : LogicalOp = undefined : LogicalOp;
    match opc {
      0b00 => {
          op = LogicalOp_AND;
          setflags = false
      },
      0b01 => {
          op = LogicalOp_ORR;
          setflags = false
      },
      0b10 => {
          op = LogicalOp_EOR;
          setflags = false
      },
      0b11 => {
          op = LogicalOp_AND;
          setflags = true
      }
    };
    let op = op;
    let setflags = setflags;
    if sf == 0b0 & [imm6[5]] == 0b1 then {
        throw(Error_Undefined())
    };
    let shift_type = DecodeShift(shift);
    let 'shift_amount = UInt(imm6);
    let invert = N == 0b1;
    __PostDecode();
    integer_logical_shiftedreg(d, datasize, invert, m, n, op, setflags, shift_amount, shift_type)
}

val branch_unconditional_register : forall 'm 'n ('pac : Bool) ('source_is_sp : Bool) ('use_key_a : Bool),
  ('n >= 0 & 'n <= 31) & ('m >= 0 & 'm <= 31 | not(not('source_is_sp)) | not('pac)).
  (BranchType, int('m), int('n), bool('pac), bool('source_is_sp), bool('use_key_a)) -> unit effect {escape, rreg, undef, wreg}

function branch_unconditional_register (branch_type, m, n, pac, source_is_sp, use_key_a) = {
    target : bits(64) = X(n);
    match branch_type {
      BranchType_INDIR => {
          if InGuardedPage then {
              if n == 16 | n == 17 then {
                  BTypeNext = 0b01
              } else {
                  BTypeNext = 0b11
              }
          } else {
              BTypeNext = 0b01
          }
      },
      BranchType_INDCALL => {
          BTypeNext = 0b10
      },
      BranchType_RET => {
          BTypeNext = 0b00
      }
    };
    if pac then {
        let modifier : bits(64) = if source_is_sp then SP() else X(m);
        if use_key_a then {
            target = AuthIA(target, modifier)
        } else {
            target = AuthIB(target, modifier)
        }
    };
    if branch_type == BranchType_INDCALL then {
        X(30) = PC() + 4
    };
    BranchTo(target, branch_type)
}

val branch_unconditional_register_decode : (bits(5), bits(5), bits(1), bits(1), bits(5), bits(2), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function branch_unconditional_register_decode (Rm, Rn, M, A, op2, op, Z) = {
    __unconditional = true;
    n : int = UInt(Rn);
    branch_type : BranchType = undefined : BranchType;
    let 'm = UInt(Rm);
    let pac : bool = A == 0b1;
    let use_key_a : bool = M == 0b0;
    source_is_sp : bool = Z == 0b1 & m == 31;
    if ~(pac) & m != 0 then {
        throw(Error_Undefined())
    } else {
        if pac & ~(HavePACExt()) then {
            throw(Error_Undefined())
        }
    };
    match op {
      0b00 => {
          branch_type = BranchType_INDIR
      },
      0b01 => {
          branch_type = BranchType_INDCALL
      },
      0b10 => {
          branch_type = BranchType_RET
      },
      _ => {
          throw(Error_Undefined())
      }
    };
    if pac then {
        if Z == 0b0 & m != 31 then {
            throw(Error_Undefined())
        };
        if branch_type == BranchType_RET then {
            if n != 31 then {
                throw(Error_Undefined())
            };
            n = 30;
            source_is_sp = true
        }
    };
    __PostDecode();
    let 'n = n;
    assert(constraint((0 <= 'n & 'n <= 31)));
    branch_unconditional_register(branch_type, m, n, pac, source_is_sp, use_key_a)
}

val decode64 : bits(32) -> unit effect {configuration, escape, undef, wreg, rreg, rmem, wmem}

function clause decode64 ((_ : bits(1) @ 0b0001010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1845) = {
    SEE = 1845;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}


function clause decode64 ((_ : bits(1) @ 0b0101010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1858) = {
    SEE = 1858;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}


function clause decode64 ((_ : bits(1) @ 0b1001010 @ _ : bits(2) @ 0b0 @ _ : bits(21) as op_code) if SEE < 1788) = {
    SEE = 1788;
    Rd : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    imm6 : bits(6) = op_code[15 .. 10];
    Rm : bits(5) = op_code[20 .. 16];
    N : bits(1) = [op_code[21]];
    shift : bits(2) = op_code[23 .. 22];
    opc : bits(2) = op_code[30 .. 29];
    sf : bits(1) = [op_code[31]];
    integer_logical_shiftedreg_decode(Rd, Rn, imm6, Rm, N, shift, opc, sf)
}


function clause decode64 ((0b1101011001011111000000 @ _ : bits(5) @ 0b00000 as op_code) if SEE < 1522) = {
    SEE = 1522;
    Rm : bits(5) = op_code[4 .. 0];
    Rn : bits(5) = op_code[9 .. 5];
    M : bits(1) = [op_code[10]];
    A : bits(1) = [op_code[11]];
    op2 : bits(5) = op_code[20 .. 16];
    op : bits(2) = op_code[22 .. 21];
    Z : bits(1) = [op_code[24]];
    branch_unconditional_register_decode(Rm, Rn, M, A, op2, op, Z)
}


function clause decode64 _ = throw(Error_Undefined())
