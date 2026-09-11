/*
 * Arm's ASL primitives behind the Oak assembler's semantics, as Sail
 * (docs/spec/94-assembler.md §8, grounding stage 3).
 *
 * Every function body below is copied from the Sail model of Armv8.5-A that
 * Arm and the REMS group generated from Arm's ASL (`sail-arm`,
 * arm-v8.5-a/model/aarch64.sail and aarch_mem.sail; BSD-3-Clause-Clear,
 * copyright Arm Limited and the authors named in its LICENSE). This file
 * exists so Sail's Lean backend can produce Lean definitions of these
 * functions mechanically, against which the hand transliteration in
 * `spec/lean/Oak/ArmASL.lean` is proved equal.
 *
 * The adaptations, all listed here, make the fragment self-contained and
 * pure; none changes a computed value:
 *   - `UInt`/`SInt`/`__GetSlice_int`/`IsZero`/`Zeros` come from Arm's
 *     prelude, written against Sail 0.8; they are restated over the Sail
 *     standard library's `unsigned`/`signed`/`get_slice_int`/`sail_zeros`.
 *   - `ConditionHolds` reads `PSTATE.{N,Z,C,V}`, a register; here the four
 *     flags arrive as a `bits(4)` parameter `nzcv` in the order N, Z, C, V
 *     (the order `AddWithCarry` returns them in). Its `result` local is
 *     initialized `undefined` in Arm's text and assigned on every match
 *     arm before it is read; the initializer is `false` here.
 *   - `integer_conditional_select` and
 *     `integer_conditional_compare_register` read `X(n)`/`X(m)` and write
 *     `X(d)`/`PSTATE`; here the operands are parameters and the result is
 *     returned. The flags they consult arrive as `nzcv`.
 */

default Order dec

$include <prelude.sail>

/* Arm prelude functions, restated over the standard library; Arm's
 * prelude overloads `~` for booleans as well as bitvectors. */

overload ~ = {not_bool, not_vec}

val UInt : forall 'n. bits('n) -> {'m, 0 <= 'm <= 2 ^ 'n - 1. int('m)}
function UInt(x) = unsigned(x)

val SInt : forall 'n, 'n >= 1. bits('n) -> {'m, - (2 ^ ('n - 1)) <= 'm <= 2 ^ ('n - 1) - 1. int('m)}
function SInt(x) = signed(x)

val __GetSlice_int : forall 'n, 'n >= 0. (int('n), int, int) -> bits('n)
function __GetSlice_int(n, m, o) = get_slice_int(n, m, o)

val Zeros : forall 'n, 'n >= 0. int('n) -> bits('n)
function Zeros(n) = sail_zeros(n)

/* aarch_mem.sail */
val IsZero : forall ('N : Int), 'N >= 0. bits('N) -> bool

function IsZero x = {
    x == Zeros('N)
}

/* aarch64.sail: AddWithCarry — the flag-setting arithmetic of cmp, cmn,
 * adds, subs, adcs, sbcs, ccmp, ccmn. */
val AddWithCarry : forall ('N : Int), ('N >= 1).
  (bits('N), bits('N), bits(1)) -> (bits('N), bits(4))

function AddWithCarry (x, y, carry_in) = {
    let 'unsigned_sum = UInt(x) + UInt(y) + UInt(carry_in);
    let 'signed_sum = SInt(x) + SInt(y) + UInt(carry_in);
    let result : bits('N) = __GetSlice_int('N, unsigned_sum, 0);
    let n : bits(1) = [result['N - 1]];
    let z : bits(1) = if IsZero(result) then 0b1 else 0b0;
    let c : bits(1) = if UInt(result) == unsigned_sum then 0b0 else 0b1;
    let v : bits(1) = if SInt(result) == signed_sum then 0b0 else 0b1;
    return((result, ((n @ z) @ c) @ v))
}

/* aarch64.sail: ConditionHolds, over the flags as a parameter. */
val ConditionHolds : (bits(4), bits(4)) -> bool

function ConditionHolds (cond, nzcv) = {
    result : bool = false;
    match slice(cond, 1, 3) {
      0b000 => {
          result = nzcv[2] == bitone
      },
      0b001 => {
          result = nzcv[1] == bitone
      },
      0b010 => {
          result = nzcv[3] == bitone
      },
      0b011 => {
          result = nzcv[0] == bitone
      },
      0b100 => {
          result = nzcv[1] == bitone & nzcv[2] == bitzero
      },
      0b101 => {
          result = nzcv[3] == nzcv[0]
      },
      0b110 => {
          result = nzcv[3] == nzcv[0] & nzcv[2] == bitzero
      },
      0b111 => {
          result = true
      }
    };
    if [cond[0]] == 0b1 & cond != 0xF then {
        result = ~(result)
    };
    result
}

/* aarch64.sail: integer_conditional_select — csel, csinc, csinv, csneg
 * (and their aliases cset, csetm, cinc, cinv, cneg), with the operands as
 * parameters and the result returned. */
val integer_conditional_select : forall 'datasize, 'datasize in {32, 64}.
  (bits(4), bits(4), bool, bool, bits('datasize), bits('datasize)) -> bits('datasize)

function integer_conditional_select (condition, nzcv, else_inc, else_inv, operand1, operand2) = {
    result : bits('datasize) = operand2;
    if ConditionHolds(condition, nzcv) then {
        result = operand1
    } else {
        result = operand2;
        if else_inv then {
            result = ~(result)
        };
        if else_inc then {
            result = result + 1
        }
    };
    result
}

/* aarch64.sail: integer_conditional_compare_register — ccmp, ccmn, with
 * the operands as parameters and the new flags returned. */
val integer_conditional_compare_register : forall 'datasize, 'datasize in {32, 64}.
  (bits(4), bits(4), bits(4), bits('datasize), bits('datasize), bool) -> bits(4)

function integer_conditional_compare_register (condition, nzcv, flags__arg, operand1, operand2__arg, sub_op) = {
    flags : bits(4) = flags__arg;
    operand2 : bits('datasize) = operand2__arg;
    carry_in : bits(1) = 0b0;
    __anon1 : bits('datasize) = operand1;
    if ConditionHolds(condition, nzcv) then {
        if sub_op then {
            operand2 = ~(operand2);
            carry_in = 0b1
        };
        (__anon1, flags) = AddWithCarry(operand1, operand2, carry_in)
    };
    flags
}

/* aarch64.sail: HighestSetBit and CountLeadingZeroBits — clz. */
val HighestSetBit : forall ('N : Int), 'N >= 0.
  bits('N) -> {'n, (-1 <= 'n & 'n <= 'N - 1). int('n)}

function HighestSetBit x = {
    foreach (i from ('N - 1) to 0 by 1 in dec) {
        if [x[i]] == 0b1 then {
            return(i)
        }
    };
    negate(1)
}

val CountLeadingZeroBits : forall ('N : Int), 'N >= 0. bits('N) -> int

function CountLeadingZeroBits x = {
    'N - (HighestSetBit(x) + 1)
}
