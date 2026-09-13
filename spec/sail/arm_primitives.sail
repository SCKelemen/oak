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
overload operator - = {sub_bits}
overload operator ^ = {xor_vec}

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

/* ---------------------------------------------------------------------
 * The vector file (docs/spec/94-assembler.md §8, the vector increment).
 *
 * The Advanced SIMD instructions the native backend emits
 * (nativegen/simd.go), copied from aarch64_vector.sail and aarch64.sail of
 * the same model with the same kind of adaptations, all listed here:
 *   - the register operands `V(n)`, `V(m)`, `X(n)` are parameters and the
 *     result is returned instead of written to `V(d)`;
 *   - `CheckFPAdvSIMDEnabled64()` (a trap check) is dropped;
 *   - `result : bits('datasize) = undefined` is initialized to zeros — every
 *     element is assigned before the result is read;
 *   - the saturating subtract returns its result and drops the FPSR.QC
 *     write that records saturation;
 *   - `Ones`, `__SetSlice_bits`, `asl_Int`, `min`/`max` over integers are
 *     restated over the Sail standard library;
 *   - the assertions of `Elem[]` and `tbl` that restate the type-level
 *     bounds are dropped, so the functions are pure (no escape effect);
 *   - `Reduce` (addv) is recursive on the halves of its input and Sail's
 *     Lean backend cannot discharge its termination; it stays with the
 *     hand transliteration (spec/sail/lean/Bridge.lean);
 *   - `vector_transfer_vector_table` takes its single table register as a
 *     parameter (the backend emits `tbl` with one register).
 */

val __SetSlice_bits : forall 'n 'm, 'm >= 0. (int('n), int('m), bits('n), int, bits('m)) -> bits('n)
function __SetSlice_bits (n, m, v, pos, x) = set_slice_bits(n, m, v, pos, x)

val Ones : forall ('N : Int), 'N >= 0. int('N) -> bits('N)
function Ones (n) = replicate_bits(0b1, n)

/* aarch64.sail: asl_Int — an element as the integer its signedness gives. */
val asl_Int : forall ('N : Int) ('unsigned : Bool), 'N >= 1. (bits('N), bool('unsigned)) -> int
function asl_Int (x, is_unsigned) = {
    let result = if is_unsigned then UInt(x) else SInt(x);
    result
}

/* aarch64.sail: Elem[] — the element accessors of a vector register. */
val aget_Elem : forall 'N 'e 'size, ('size >= 1 & 'e >= 0 & ('e + 1) * 'size <= 'N).
  (bits('N), int('e), int('size)) -> bits('size)
function aget_Elem (vector_name, e, size) = {
    slice(vector_name, e * size, size)
}

val aset_Elem : forall 'N 'e 'size, ('size >= 1 & 'e >= 0 & ('e + 1) * 'size <= 'N).
  (bits('N), int('e), int('size), bits('size)) -> bits('N)
function aset_Elem (vector_name, e, size, value_name) = {
    let vector_name = __SetSlice_bits('N, size, vector_name, e * size, value_name);
    vector_name
}

/* aarch64_vector.sail: BitCount — cnt. */
val BitCount : forall ('N : Int), 'N >= 0. bits('N) -> int
function BitCount x = {
    result : int = 0;
    foreach (i from 0 to ('N - 1) by 1 in inc) {
        if [x[i]] == 0b1 then {
            result = result + 1
        }
    };
    result
}

/* aarch64_float.sail: UnsignedSatQ, SignedSatQ, SatQ — uqsub. */
val UnsignedSatQ : forall ('N : Int) ('i : Int), 'N >= 0. (int('i), int('N)) -> (bits('N), bool)
function UnsignedSatQ (i, N) = {
    result : int = 0;
    saturated : bool = false;
    if i > 2 ^ N - 1 then {
        result = 2 ^ N - 1;
        saturated = true
    } else {
        if i < 0 then {
            result = 0;
            saturated = true
        } else {
            result = i;
            saturated = false
        }
    };
    return((__GetSlice_int(N, result, 0), saturated))
}

val SignedSatQ : forall ('N : Int) ('i : Int), 'N >= 1. (int('i), int('N)) -> (bits('N), bool)
function SignedSatQ (i, N) = {
    result : int = 0;
    saturated : bool = false;
    if i > 2 ^ (N - 1) - 1 then {
        result = 2 ^ (N - 1) - 1;
        saturated = true
    } else {
        if i < negate(2 ^ (N - 1)) then {
            result = negate(2 ^ (N - 1));
            saturated = true
        } else {
            result = i;
            saturated = false
        }
    };
    return((__GetSlice_int(N, result, 0), saturated))
}

val SatQ : forall ('N : Int) ('i : Int) ('unsigned : Bool), 'N >= 1. (int('i), int('N), bool('unsigned)) -> (bits('N), bool)
function SatQ (i, N, is_unsigned) = {
    result : bits('N) = Zeros(N);
    sat : bool = false;
    (result, sat) = if is_unsigned then UnsignedSatQ(i, N) else SignedSatQ(i, N);
    return((result, sat))
}

/* aarch64_vector.sail: dup (from a general register). */
val vector_transfer_integer_dup : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('esize)) -> bits('datasize)
function vector_transfer_integer_dup (datasize, elements, esize, element) = {
    result : bits('datasize) = Zeros(datasize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        result = aset_Elem(result, e, esize, element)
    };
    result
}

/* aarch64_vector.sail: add, sub. */
val vector_arithmetic_binary_uniform_add_wrapping_single : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bool) -> bits('datasize)
function vector_arithmetic_binary_uniform_add_wrapping_single (datasize, elements, esize, operand1, operand2, sub_op) = {
    result : bits('datasize) = Zeros(datasize);
    element1 : bits('esize) = Zeros(esize);
    element2 : bits('esize) = Zeros(esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        if sub_op then {
            result = aset_Elem(result, e, esize, element1 - element2)
        } else {
            result = aset_Elem(result, e, esize, element1 + element2)
        }
    };
    result
}

/* aarch64_vector.sail: umax, umin (smax, smin with is_unsigned false). */
val vector_arithmetic_binary_uniform_maxmin_single : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bool, bool) -> bits('datasize)
function vector_arithmetic_binary_uniform_maxmin_single (datasize, elements, esize, operand1, operand2, minimum, is_unsigned) = {
    result : bits('datasize) = Zeros(datasize);
    element1 : int = 0;
    element2 : int = 0;
    maxmin : int = 0;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), is_unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), is_unsigned);
        maxmin = if minimum then min_int(element1, element2) else max_int(element1, element2);
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, maxmin, 0))
    };
    result
}

/* aarch64_vector.sail: cmhs (cmp_eq), cmhi (not cmp_eq); cmge/cmgt with is_unsigned false. */
val vector_arithmetic_binary_uniform_cmp_int : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (bool, int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bool) -> bits('datasize)
function vector_arithmetic_binary_uniform_cmp_int (cmp_eq, datasize, elements, esize, operand1, operand2, is_unsigned) = {
    result : bits('datasize) = Zeros(datasize);
    element1 : int = 0;
    element2 : int = 0;
    test_passed : bool = false;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), is_unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), is_unsigned);
        test_passed = if cmp_eq then element1 >= element2 else element1 > element2;
        result = aset_Elem(result, e, esize, if test_passed then Ones(esize) else Zeros(esize))
    };
    result
}

/* aarch64_vector.sail: cmeq (register form; cmtst with and_test). */
val vector_arithmetic_binary_uniform_cmp_bitwise : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (bool, int('datasize), int('elements), int('esize), bits('datasize), bits('datasize)) -> bits('datasize)
function vector_arithmetic_binary_uniform_cmp_bitwise (and_test, datasize, elements, esize, operand1, operand2) = {
    result : bits('datasize) = Zeros(datasize);
    element1 : bits('esize) = Zeros(esize);
    element2 : bits('esize) = Zeros(esize);
    test_passed : bool = false;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        if and_test then {
            test_passed = ~(IsZero(element1 & element2))
        } else {
            test_passed = element1 == element2
        };
        result = aset_Elem(result, e, esize, if test_passed then Ones(esize) else Zeros(esize))
    };
    result
}

/* aarch64_vector.sail: cmeq #0 (and the other compares with zero). */
enum CompareOp = {CompareOp_GT, CompareOp_GE, CompareOp_EQ, CompareOp_LE, CompareOp_LT}

val vector_arithmetic_unary_cmp_int_bulk : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (CompareOp, int('datasize), int('elements), int('esize), bits('datasize)) -> bits('datasize)
function vector_arithmetic_unary_cmp_int_bulk (comparison, datasize, elements, esize, operand) = {
    result : bits('datasize) = Zeros(datasize);
    element : int = 0;
    test_passed : bool = false;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = SInt(aget_Elem(operand, e, esize));
        match comparison {
          CompareOp_GT => {
              test_passed = element > 0
          },
          CompareOp_GE => {
              test_passed = element >= 0
          },
          CompareOp_EQ => {
              test_passed = element == 0
          },
          CompareOp_LE => {
              test_passed = element <= 0
          },
          CompareOp_LT => {
              test_passed = element < 0
          }
        };
        result = aset_Elem(result, e, esize, if test_passed then Ones(esize) else Zeros(esize))
    };
    result
}

/* aarch64_vector.sail: uqsub (sqsub with is_unsigned false); the FPSR.QC write is dropped. */
val vector_arithmetic_binary_uniform_sub_saturating : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bool) -> bits('datasize)
function vector_arithmetic_binary_uniform_sub_saturating (datasize, elements, esize, operand1, operand2, is_unsigned) = {
    result : bits('datasize) = Zeros(datasize);
    element1 : int = 0;
    element2 : int = 0;
    diff : int = 0;
    sat : bool = false;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), is_unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), is_unsigned);
        diff = element1 - element2;
        __tc1 : bits('esize) = Zeros(esize);
        (__tc1, sat) = SatQ(diff, esize, is_unsigned);
        result = aset_Elem(result, e, esize, __tc1)
    };
    result
}

/* aarch64_vector.sail: ushr, sshr (round and accumulate false; the
 * accumulator operand is the register the accumulating forms add to). */
val vector_shift_right : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (bool, int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bool, int, bool) -> bits('datasize)
function vector_shift_right (accumulate, datasize, elements, esize, operand, accumulator, round, shift, is_unsigned) = {
    result : bits('datasize) = Zeros(datasize);
    let round_const : int = if round then shl_int(1, shift - 1) else 0;
    element : int = 0;
    let operand2 : bits('datasize) = if accumulate then accumulator else Zeros(datasize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = shr_int(asl_Int(aget_Elem(operand, e, esize), is_unsigned) + round_const, shift);
        result = aset_Elem(result, e, esize, aget_Elem(operand2, e, esize) + __GetSlice_int(esize, element, 0))
    };
    result
}

/* aarch64_vector.sail: tbl with one table register (tbx with is_tbl false). */
val vector_transfer_vector_table : forall 'datasize 'elements, ('elements >= 1 & 'elements * 8 == 'datasize & 'datasize <= 128).
  (int('datasize), int('elements), bool, bits('datasize), bits(128), bits('datasize)) -> bits('datasize)
function vector_transfer_vector_table (datasize, elements, is_tbl, indices, table, dst) = {
    result : bits('datasize) = if is_tbl then Zeros(datasize) else dst;
    foreach (i from 0 to (elements - 1) by 1 in inc) {
        let index = UInt(aget_Elem(indices, i, 8));
        if index < 16 then {
            result = aset_Elem(result, i, 8, aget_Elem(table, index, 8))
        }
    };
    result
}

/* aarch64_vector.sail: ext. */
val vector_transfer_vector_extract : forall 'datasize, 'datasize >= 1.
  (int('datasize), bits('datasize), bits('datasize), int) -> bits('datasize)
function vector_transfer_vector_extract (datasize, hi, lo, position) = {
    let concat : bits(2 * 'datasize) = hi @ lo;
    slice(concat, position, datasize)
}

/* aarch64_vector.sail: umaxv, uminv (smaxv, sminv with is_unsigned false). */
val vector_reduce_intmax : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bool, bool) -> bits('esize)
function vector_reduce_intmax (datasize, elements, esize, operand, min, is_unsigned) = {
    maxmin : int = 0;
    element : int = 0;
    maxmin = asl_Int(aget_Elem(operand, 0, esize), is_unsigned);
    foreach (e from 1 to (elements - 1) by 1 in inc) {
        element = asl_Int(aget_Elem(operand, e, esize), is_unsigned);
        maxmin = if min then min_int(maxmin, element) else max_int(maxmin, element)
    };
    __GetSlice_int(esize, maxmin, 0)
}

/* aarch64_vector.sail: Reduce (addv) is recursive on the halves of its
 * input; Sail's Lean backend cannot discharge that recursion's termination,
 * so the tree stays in the hand transliteration (spec/sail/lean/Bridge.lean
 * states it and proves it equal to the fold Oak.NeonSemantics.addv uses). */

/* aarch64_vector.sail: cnt. */
val vector_arithmetic_unary_cnt : forall 'datasize 'elements 'esize, ('esize >= 1 & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize)) -> bits('datasize)
function vector_arithmetic_unary_cnt (datasize, elements, esize, operand) = {
    result : bits('datasize) = Zeros(datasize);
    count : int = 0;
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        count = BitCount(aget_Elem(operand, e, esize));
        result = aset_Elem(result, e, esize, __GetSlice_int(esize, count, 0))
    };
    result
}

/* aarch64_vector.sail: and, orr (bic, orn with invert). */
enum LogicalOp = {LogicalOp_AND, LogicalOp_EOR, LogicalOp_ORR}

val vector_arithmetic_binary_uniform_logical_andorr : forall 'datasize, 'datasize >= 1.
  (int('datasize), bool, bits('datasize), bits('datasize), LogicalOp) -> bits('datasize)
function vector_arithmetic_binary_uniform_logical_andorr (datasize, invert, operand1, operand2__arg, op) = {
    operand2 : bits('datasize) = operand2__arg;
    result : bits('datasize) = Zeros(datasize);
    if invert then {
        operand2 = ~(operand2)
    };
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
    result
}

/* aarch64_vector.sail: eor (bsl, bit, bif with the other operators); the
 * destination register the bit-select forms read is the parameter dst. */
enum VBitOp = {VBitOp_VBIF, VBitOp_VBIT, VBitOp_VBSL, VBitOp_VEOR}

val vector_arithmetic_binary_uniform_logical_bsleor : forall 'datasize, 'datasize >= 1.
  (int('datasize), bits('datasize), bits('datasize), bits('datasize), VBitOp) -> bits('datasize)
function vector_arithmetic_binary_uniform_logical_bsleor (datasize, vm, vn, dst, op) = {
    operand1 : bits('datasize) = Zeros(datasize);
    operand2 : bits('datasize) = Zeros(datasize);
    operand3 : bits('datasize) = Zeros(datasize);
    let operand4 : bits('datasize) = vn;
    match op {
      VBitOp_VEOR => {
          operand1 = vm;
          operand2 = Zeros(datasize);
          operand3 = Ones(datasize)
      },
      VBitOp_VBSL => {
          operand1 = vm;
          operand2 = operand1;
          operand3 = dst
      },
      VBitOp_VBIT => {
          operand1 = dst;
          operand2 = operand1;
          operand3 = vm
      },
      VBitOp_VBIF => {
          operand1 = dst;
          operand2 = operand1;
          operand3 = ~(vm)
      }
    };
    let operand3 = operand3;
    let operand2 = operand2;
    let operand1 = operand1;
    operand1 ^ (operand2 ^ operand4 & operand3)
}
