/*
 * Arm's ASL primitives behind the Oak assembler's semantics, as Sail
 * (docs/spec/94-assembler.md §8, grounding stage 3).
 *
 * The instruction-semantic function bodies below are copied from the Sail
 * model of Armv8.5-A that
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
 *   - the final barrier and TLBI decoder/dispatch projections preserve the
 *     official decoded fields or named call target as pure return values;
 *     access checks and architecture state effects are explicitly erased.
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
 *   - the tuple assignments `(result, sat) = SatQ(...)` to declared locals
 *     are `let` bindings: Sail's Lean backend drops a tuple assignment to
 *     mutable locals (it generated a unit-typed `let` and returned the
 *     initial values), so the text is written the way the backend keeps;
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
    let (result, sat) = if is_unsigned then UnsignedSatQ(i, N) else SignedSatQ(i, N);
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
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = asl_Int(aget_Elem(operand1, e, esize), is_unsigned);
        element2 = asl_Int(aget_Elem(operand2, e, esize), is_unsigned);
        diff = element1 - element2;
        let (__tc1, sat) = SatQ(diff, esize, is_unsigned);
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

/* aarch64_float.sail: FPNeg, FPAbs — the sign operations (the width
 * assertion dropped: the verifier's views are 32 and 64 bits). */
val FPNeg : forall ('N : Int), 'N >= 1. bits('N) -> bits('N)
function FPNeg op = {
    ~([op['N - 1]]) @ slice(op, 0, 'N - 1)
}

val FPAbs : forall ('N : Int), 'N >= 1. bits('N) -> bits('N)
function FPAbs op = {
    0b0 @ slice(op, 0, 'N - 1)
}

/* aarch64_float.sail: the IEEE operations behind the floating-point
 * instructions — FPAdd, FPSub, FPMul, FPMulAdd, FPMin, FPMax, FPMinNum,
 * FPMaxNum, FPSqrt — are defined there over reals (FPRoundBase). Here they
 * are declared without bodies and mapped to the uninterpreted constants of
 * the same names in the Sail support library (spec/sail/lean-sail-4.33.patch),
 * exactly as the assembler's verifier leaves them uninterpreted
 * (asm/floats_ops.go, Oak.Uninterpreted): the bridge states how each
 * instruction applies them, lane for lane, and the differentials check the
 * operations themselves against the hardware. FPCR is a parameter (the
 * model reads the register). */
val FPAdd = pure { lean: "Sail.FPAdd" } : forall 'N, 'N in {32, 64}. (bits('N), bits('N), bits(32)) -> bits('N)
val FPSub = pure { lean: "Sail.FPSub" } : forall 'N, 'N in {32, 64}. (bits('N), bits('N), bits(32)) -> bits('N)
val FPMul = pure { lean: "Sail.FPMul" } : forall 'N, 'N in {32, 64}. (bits('N), bits('N), bits(32)) -> bits('N)
val FPMulAdd = pure { lean: "Sail.FPMulAdd" } : forall 'N, 'N in {32, 64}. (bits('N), bits('N), bits('N), bits(32)) -> bits('N)
val FPMin = pure { lean: "Sail.FPMin" } : forall 'N, 'N in {32, 64}. (bits('N), bits('N), bits(32)) -> bits('N)
val FPMax = pure { lean: "Sail.FPMax" } : forall 'N, 'N in {32, 64}. (bits('N), bits('N), bits(32)) -> bits('N)
val FPMinNum = pure { lean: "Sail.FPMinNum" } : forall 'N, 'N in {32, 64}. (bits('N), bits('N), bits(32)) -> bits('N)
val FPMaxNum = pure { lean: "Sail.FPMaxNum" } : forall 'N, 'N in {32, 64}. (bits('N), bits('N), bits(32)) -> bits('N)
val FPSqrt = pure { lean: "Sail.FPSqrt" } : forall 'N, 'N in {32, 64}. (bits('N), bits(32)) -> bits('N)

/* aarch64_vector.sail: fadd (pair false), faddp (pair true: adjacent pairs
 * of operand2 @ operand1). */
val vector_arithmetic_binary_uniform_add_fp : forall 'datasize 'elements 'esize, ('esize in {32, 64} & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bits(32), bool) -> bits('datasize)
function vector_arithmetic_binary_uniform_add_fp (datasize, elements, esize, operand1, operand2, fpcr, pair) = {
    result : bits('datasize) = Zeros(datasize);
    let concat : bits(2 * 'datasize) = operand2 @ operand1;
    element1 : bits('esize) = Zeros(esize);
    element2 : bits('esize) = Zeros(esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        if pair then {
            element1 = aget_Elem(concat, 2 * e, esize);
            element2 = aget_Elem(concat, 2 * e + 1, esize)
        } else {
            element1 = aget_Elem(operand1, e, esize);
            element2 = aget_Elem(operand2, e, esize)
        };
        result = aset_Elem(result, e, esize, FPAdd(element1, element2, fpcr))
    };
    result
}

/* aarch64_vector.sail: fsub (abs false; fabd with abs). */
val vector_arithmetic_binary_uniform_sub_fp : forall 'datasize 'elements 'esize, ('esize in {32, 64} & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bits(32), bool) -> bits('datasize)
function vector_arithmetic_binary_uniform_sub_fp (datasize, elements, esize, operand1, operand2, fpcr, abs) = {
    result : bits('datasize) = Zeros(datasize);
    element1 : bits('esize) = Zeros(esize);
    element2 : bits('esize) = Zeros(esize);
    diff : bits('esize) = Zeros(esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        diff = FPSub(element1, element2, fpcr);
        result = aset_Elem(result, e, esize, if abs then FPAbs(diff) else diff)
    };
    result
}

/* aarch64_vector.sail: fmul. */
val vector_arithmetic_binary_uniform_mul_fp_product : forall 'datasize 'elements 'esize, ('esize in {32, 64} & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bits(32)) -> bits('datasize)
function vector_arithmetic_binary_uniform_mul_fp_product (datasize, elements, esize, operand1, operand2, fpcr) = {
    result : bits('datasize) = Zeros(datasize);
    element1 : bits('esize) = Zeros(esize);
    element2 : bits('esize) = Zeros(esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        result = aset_Elem(result, e, esize, FPMul(element1, element2, fpcr))
    };
    result
}

/* aarch64_vector.sail: fmla (sub_op false), fmls (sub_op true); the
 * accumulator V(d) the instruction reads is the parameter operand3. */
val vector_arithmetic_binary_uniform_mul_fp_fused : forall 'datasize 'elements 'esize, ('esize in {32, 64} & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bits('datasize), bits(32), bool) -> bits('datasize)
function vector_arithmetic_binary_uniform_mul_fp_fused (datasize, elements, esize, operand1, operand2, operand3, fpcr, sub_op) = {
    result : bits('datasize) = Zeros(datasize);
    element1 : bits('esize) = Zeros(esize);
    element2 : bits('esize) = Zeros(esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element1 = aget_Elem(operand1, e, esize);
        element2 = aget_Elem(operand2, e, esize);
        if sub_op then {
            element1 = FPNeg(element1)
        };
        result = aset_Elem(result, e, esize, FPMulAdd(aget_Elem(operand3, e, esize), element1, element2, fpcr))
    };
    result
}

/* aarch64_vector.sail: fmin, fmax (IEEE 754-1985 semantics: a NaN operand
 * propagates; pair for fminp/fmaxp). */
val vector_arithmetic_binary_uniform_maxmin_fp_1985 : forall 'datasize 'elements 'esize, ('esize in {32, 64} & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bits(32), bool, bool) -> bits('datasize)
function vector_arithmetic_binary_uniform_maxmin_fp_1985 (datasize, elements, esize, operand1, operand2, fpcr, minimum, pair) = {
    result : bits('datasize) = Zeros(datasize);
    let concat : bits(2 * 'datasize) = operand2 @ operand1;
    element1 : bits('esize) = Zeros(esize);
    element2 : bits('esize) = Zeros(esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        if pair then {
            element1 = aget_Elem(concat, 2 * e, esize);
            element2 = aget_Elem(concat, 2 * e + 1, esize)
        } else {
            element1 = aget_Elem(operand1, e, esize);
            element2 = aget_Elem(operand2, e, esize)
        };
        if minimum then {
            result = aset_Elem(result, e, esize, FPMin(element1, element2, fpcr))
        } else {
            result = aset_Elem(result, e, esize, FPMax(element1, element2, fpcr))
        }
    };
    result
}

/* aarch64_vector.sail: fminnm, fmaxnm (IEEE 754-2008 minNum/maxNum). */
val vector_arithmetic_binary_uniform_maxmin_fp_2008 : forall 'datasize 'elements 'esize, ('esize in {32, 64} & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits('datasize), bits(32), bool, bool) -> bits('datasize)
function vector_arithmetic_binary_uniform_maxmin_fp_2008 (datasize, elements, esize, operand1, operand2, fpcr, minimum, pair) = {
    result : bits('datasize) = Zeros(datasize);
    let concat : bits(2 * 'datasize) = operand2 @ operand1;
    element1 : bits('esize) = Zeros(esize);
    element2 : bits('esize) = Zeros(esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        if pair then {
            element1 = aget_Elem(concat, 2 * e, esize);
            element2 = aget_Elem(concat, 2 * e + 1, esize)
        } else {
            element1 = aget_Elem(operand1, e, esize);
            element2 = aget_Elem(operand2, e, esize)
        };
        if minimum then {
            result = aset_Elem(result, e, esize, FPMinNum(element1, element2, fpcr))
        } else {
            result = aset_Elem(result, e, esize, FPMaxNum(element1, element2, fpcr))
        }
    };
    result
}

/* aarch64_vector.sail: fsqrt. */
val vector_arithmetic_unary_special_sqrt : forall 'datasize 'elements 'esize, ('esize in {32, 64} & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bits(32)) -> bits('datasize)
function vector_arithmetic_unary_special_sqrt (datasize, elements, esize, operand, fpcr) = {
    result : bits('datasize) = Zeros(datasize);
    element : bits('esize) = Zeros(esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        result = aset_Elem(result, e, esize, FPSqrt(element, fpcr))
    };
    result
}

/* aarch64_vector.sail: fneg (neg true), fabs (neg false). */
val vector_arithmetic_unary_diffneg_fp : forall 'datasize 'elements 'esize, ('esize in {32, 64} & 'elements >= 1 & 'elements * 'esize == 'datasize).
  (int('datasize), int('elements), int('esize), bits('datasize), bool) -> bits('datasize)
function vector_arithmetic_unary_diffneg_fp (datasize, elements, esize, operand, neg) = {
    result : bits('datasize) = Zeros(datasize);
    element : bits('esize) = Zeros(esize);
    foreach (e from 0 to (elements - 1) by 1 in inc) {
        element = aget_Elem(operand, e, esize);
        if neg then {
            element = FPNeg(element)
        } else {
            element = FPAbs(element)
        };
        result = aset_Elem(result, e, esize, element)
    };
    result
}

/* ---------------------------------------------------------------------
 * The A64 STR (unsigned immediate), 64-bit, normal-store request.
 *
 * The pinned aarch_decode.sail SEE-1277 clause extracts Rt/Rn/imm12/opc/V/
 * size and calls the (historically misnamed) signed_postidx decoder.  For
 * size=11, V=0, opc=00 that decoder fixes wback=false, postindex=false,
 * scale=3, AccType_NORMAL, MemOp_STORE, regsize=datasize=64, signed=false.
 * The instruction body then reads Xn (SP only for Rn=31), reads Xt (zero for
 * Rt=31), and requests Mem(address, 8, AccType_NORMAL) = data.
 *
 * These pure functions expose only that decoder result and the request made
 * immediately before Mem.  They erase __PostDecode admission, syndrome
 * writes, alignment and endian handling, translation and faults, permissions,
 * MTE/tag checks, exclusive clearing, MMIO/trickbox paths, physical-memory
 * writes, CAT events, execution/occurrence, and descriptor classification.
 */

val decode64_str64_unsigned_pure :
  bits(32) -> (bool, bits(5), bits(5), bits(12))

function decode64_str64_unsigned_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let Rn : bits(5) = slice(op_code, 5, 5);
    let imm12 : bits(12) = slice(op_code, 10, 12);
    if (op_code & 0xFFC00000) == 0xF9000000 then {
        (true, Rt, Rn, imm12)
    } else {
        (false, Rt, Rn, imm12)
    }
}

val str64_unsigned_store_request_pure :
  (bits(5), bits(5), bits(12), bits(64), bits(64), bits(64)) ->
    (bits(64), bits(64))

function str64_unsigned_store_request_pure (Rt, Rn, imm12, rn_value, rt_value, sp_value) = {
    let base : bits(64) = if Rn == 0b11111 then sp_value else rn_value;
    let data : bits(64) = if Rt == 0b11111 then Zeros(64) else rt_value;
    let offset : bits(64) = sail_shiftleft(sail_zero_extend(imm12, 64), 3);
    (base + offset, data)
}

/* ---------------------------------------------------------------------
 * The A64 STP (signed offset), 64-bit, two normal-store requests.
 *
 * The pinned aarch_decode.sail SEE-1357 clause extracts Rt/Rn/Rt2/imm7/L/V/
 * opc and calls memory_pair_general_offset_memory_pair_general_postidx__decode.
 * For opc=10, V=0, L=0 that decoder fixes wback=false, postindex=false,
 * scale=3, AccType_NORMAL, MemOp_STORE, datasize=64, signed=false.  The
 * instruction body reads Xn (SP only for Rn=31), independently reads Xt and
 * Xt2 (zero for register 31), and supplies two size-eight Mem requests at the
 * selected address and address+8.
 *
 * These pure functions expose only the decoder fields and those pre-Mem
 * address/data arguments.  A returned four-tuple is not a claim that either
 * request occurs or that observers order them.  The projection erases
 * __PostDecode admission, alignment and endian handling, translation and
 * faults, permissions, MTE/tag checks, exclusives, MMIO/device paths,
 * physical-memory writes, CAT events, atomicity, non-tearing, single-copy
 * atomicity, page-table publication, and every other architectural effect.
 */

val decode64_stp64_offset_pure :
  bits(32) -> (bool, bits(5), bits(5), bits(5), bits(7))

function decode64_stp64_offset_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let Rn : bits(5) = slice(op_code, 5, 5);
    let Rt2 : bits(5) = slice(op_code, 10, 5);
    let imm7 : bits(7) = slice(op_code, 15, 7);
    if (op_code & 0xFFC00000) == 0xA9000000 then {
        (true, Rt, Rn, Rt2, imm7)
    } else {
        (false, Rt, Rn, Rt2, imm7)
    }
}

val stp64_offset_store_requests_pure :
  (bits(5), bits(5), bits(5), bits(7), bits(64), bits(64), bits(64), bits(64)) ->
    (bits(64), bits(64), bits(64), bits(64))

function stp64_offset_store_requests_pure
  (Rt, Rn, Rt2, imm7, rn_value, rt_value, rt2_value, sp_value) = {
    let base : bits(64) = if Rn == 0b11111 then sp_value else rn_value;
    let data1 : bits(64) = if Rt == 0b11111 then Zeros(64) else rt_value;
    let data2 : bits(64) = if Rt2 == 0b11111 then Zeros(64) else rt2_value;
    let offset : bits(64) = sail_shiftleft(sail_sign_extend(imm7, 64), 3);
    let address1 : bits(64) = base + offset;
    let address2 : bits(64) = address1 + 0x0000000000000008;
    (address1, data1, address2, data2)
}

/* The next conditional projection covers only the arguments selected by the
 * ordinary aligned size-8 route after Mem.  In the pinned model, aset_Mem
 * performs BigEndianReverse before AArch64_aset_MemSingle; successful
 * translation supplies a 52-bit desc.paddress.address; and aset__Mem's
 * non-trickbox, non-counter, non-size-16 arm calls
 * __WriteMemory(8, ZeroExtend(paddress), value_name).
 *
 * Reachability of that route is deliberately not represented by a caller-
 * supplied Boolean.  It remains an external premise covering alignment,
 * normally returning fault-free translation, exclusive clearing, access-
 * descriptor construction, MTE/tag continuation, and special-route
 * exclusion.  The result is not a RAM write or a CAT event.
 */

val big_endian_reverse64_pure : bits(64) -> bits(64)

function big_endian_reverse64_pure (value_name) = {
    slice(value_name, 0, 8) @
    slice(value_name, 8, 8) @
    slice(value_name, 16, 8) @
    slice(value_name, 24, 8) @
    slice(value_name, 32, 8) @
    slice(value_name, 40, 8) @
    slice(value_name, 48, 8) @
    slice(value_name, 56, 8)
}

val str64_aligned_normal_write_memory_arguments_pure :
  (bool, bits(52), bits(64)) -> (bits(56), bits(64))

function str64_aligned_normal_write_memory_arguments_pure
  (big_endian, paddress, pre_mem_data) = {
    let write_data : bits(64) = if big_endian then
        big_endian_reverse64_pure(pre_mem_data)
      else
        pre_mem_data;
    (sail_zero_extend(paddress, 56), write_data)
}

/* The no-device model's next two wrappers preserve these arguments:
 * __WriteMemory calls __WriteRAM(56, N, __defaultRAM, address, val_name),
 * and __WriteRAM forwards them to external write_ram.  This pure projection
 * specializes N to the ordinary STR64 size of eight bytes and makes the
 * register value an explicit input.  It proves neither that either wrapper
 * is dynamically invoked nor that external memory changes.
 */

val str64_no_device_write_ram_call_arguments_pure :
  (bits(56), bits(56), bits(64)) ->
    (int, int, bits(56), bits(56), bits(64))

function str64_no_device_write_ram_call_arguments_pure
  (default_ram, address, data) = {
    (56, 8, default_ram, address, data)
}

/* ---------------------------------------------------------------------
 * The A64 barrier decoder (docs/spec/94-assembler.md §9).
 *
 * The three word patterns below are the DSB, DMB, and ISB clauses of
 * aarch_decode.sail's decode64.  system_barriers_decode is copied from
 * aarch64.sail.  This pure projection makes the decoder result explicit:
 * architectural state updates and the final barrier call are replaced by
 * the returned valid/op/domain/types tuple.  Invalid opc is recorded by the
 * first component instead of throwing Error_Undefined.  No decoded value is
 * otherwise changed.
 */

enum MemBarrierOp = {
  MemBarrierOp_DSB,
  MemBarrierOp_DMB,
  MemBarrierOp_ISB,
  MemBarrierOp_SSBB,
  MemBarrierOp_PSSBB,
  MemBarrierOp_SB
}

enum MBReqDomain = {
  MBReqDomain_Nonshareable,
  MBReqDomain_InnerShareable,
  MBReqDomain_OuterShareable,
  MBReqDomain_FullSystem
}

enum MBReqTypes = {MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All}

/* The call targets of the pinned official system_barriers dispatch.  This
 * projection records which named architecture primitive is selected while
 * deliberately leaving that primitive's state effect outside this pure
 * model.  In the pinned sail-arm model InstructionSynchronizationBarrier and
 * SynchronizeContext are both unit-returning stubs, so target identity is not
 * evidence of context synchronization by itself. */
enum BarrierExecutionTarget = {
  BarrierExecutionTarget_DataSynchronizationBarrier,
  BarrierExecutionTarget_DataMemoryBarrier,
  BarrierExecutionTarget_InstructionSynchronizationBarrier,
  BarrierExecutionTarget_SpeculativeSynchronizationBarrierToVA,
  BarrierExecutionTarget_SpeculativeSynchronizationBarrierToPA,
  BarrierExecutionTarget_SpeculationBarrier
}

val system_barriers_target_pure :
  (MBReqDomain, MemBarrierOp, MBReqTypes) -> BarrierExecutionTarget

function system_barriers_target_pure (domain, op, types) =
  match op {
    MemBarrierOp_DSB => BarrierExecutionTarget_DataSynchronizationBarrier,
    MemBarrierOp_DMB => BarrierExecutionTarget_DataMemoryBarrier,
    MemBarrierOp_ISB => BarrierExecutionTarget_InstructionSynchronizationBarrier,
    MemBarrierOp_SSBB => BarrierExecutionTarget_SpeculativeSynchronizationBarrierToVA,
    MemBarrierOp_PSSBB => BarrierExecutionTarget_SpeculativeSynchronizationBarrierToPA,
    MemBarrierOp_SB => BarrierExecutionTarget_SpeculationBarrier
  }

val system_barriers_decode_pure :
  (bits(2), bits(4)) -> (bool, MemBarrierOp, MBReqDomain, MBReqTypes)

function system_barriers_decode_pure (opc, CRm) = {
    valid : bool = true;
    op : MemBarrierOp = MemBarrierOp_DSB;
    domain : MBReqDomain = MBReqDomain_FullSystem;
    types : MBReqTypes = MBReqTypes_All;
    match opc {
      0b00 => {
          op = MemBarrierOp_DSB
      },
      0b01 => {
          op = MemBarrierOp_DMB
      },
      0b10 => {
          op = MemBarrierOp_ISB
      },
      _ => {
          valid = false
      }
    };
    match slice(CRm, 2, 2) {
      0b00 => {
          domain = MBReqDomain_OuterShareable
      },
      0b01 => {
          domain = MBReqDomain_Nonshareable
      },
      0b10 => {
          domain = MBReqDomain_InnerShareable
      },
      0b11 => {
          domain = MBReqDomain_FullSystem
      }
    };
    match slice(CRm, 0, 2) {
      0b01 => {
          types = MBReqTypes_Reads
      },
      0b10 => {
          types = MBReqTypes_Writes
      },
      0b11 => {
          types = MBReqTypes_All
      },
      _ => {
          if slice(CRm, 2, 2) == 0b01 then {
              op = MemBarrierOp_PSSBB
          } else {
              if slice(CRm, 2, 2) == 0b00 & opc == 0b00 then {
                  op = MemBarrierOp_SSBB
              } else {
                  types = MBReqTypes_All;
                  domain = MBReqDomain_FullSystem
              }
          }
      }
    };
    (valid, op, domain, types)
}

val decode64_barrier_pure :
  bits(32) -> (bool, MemBarrierOp, MBReqDomain, MBReqTypes)

function decode64_barrier_pure op_code = {
    let CRm : bits(4) = slice(op_code, 8, 4);
    if (op_code & 0xFFFFF0FF) == 0xD503309F then {
        system_barriers_decode_pure(0b00, CRm)
    } else if (op_code & 0xFFFFF0FF) == 0xD50330BF then {
        system_barriers_decode_pure(0b01, CRm)
    } else if (op_code & 0xFFFFF0FF) == 0xD50330DF then {
        system_barriers_decode_pure(0b10, CRm)
    } else {
        (false, MemBarrierOp_DSB, MBReqDomain_FullSystem, MBReqTypes_All)
    }
}

/* ---------------------------------------------------------------------
 * The A64 TLBI VMALLS12E1IS SYS-field dispatch.
 *
 * aarch_decode.sail's generic SYS-write clause extracts op0/op1/CRn/CRm/
 * op2/Rt and the pinned aarch64.sail AArch64_AutoGen_SysOpsWrite function
 * selects TLBI_VMALLS12E1IS for op0=01, op1=100, CRn=8, op2=110, CRm=3.
 * This pure projection records
 * only that named call target. It erases the execution-level access/trap
 * checks and every invalidation, shareability, broadcast, visibility, and
 * completion effect. Rt is irrelevant to this target dispatch; Oak's
 * canonical nullary encoding uses Rt = 31.
 */

enum TLBIOperationTarget = {TLBIOperationTarget_VMALLS12E1IS}

val aarch64_sysops_write_tlbi_target_pure :
  (bits(2), bits(3), bits(4), bits(3), bits(4)) ->
    (bool, TLBIOperationTarget)

function aarch64_sysops_write_tlbi_target_pure (op0, op1, CRn, op2, CRm) = {
    if op0 == 0b01 & op1 == 0b100 & CRn == 0x8 &
        op2 == 0b110 & CRm == 0x3 then {
        (true, TLBIOperationTarget_VMALLS12E1IS)
    } else {
        (false, TLBIOperationTarget_VMALLS12E1IS)
    }
}

val decode64_tlbi_target_pure :
  bits(32) -> (bool, TLBIOperationTarget)

function decode64_tlbi_target_pure (op_code) = {
    let op0 : bits(2) = slice(op_code, 19, 2);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let op2 : bits(3) = slice(op_code, 5, 3);
    if (op_code & 0xFFF80000) == 0xD5080000 then {
        aarch64_sysops_write_tlbi_target_pure(op0, op1, CRn, op2, CRm)
    } else {
        (false, TLBIOperationTarget_VMALLS12E1IS)
    }
}

/* ---------------------------------------------------------------------
 * The A64 PSTATE-immediate DAIFSet dispatch and state body.
 *
 * The pinned aarch_decode.sail PSTATE-immediate clause extracts op1/CRm/op2
 * and system_register_cpsr_decode selects PSTATEField_DAIFSet when
 * op1 @ op2 = 0b011110. system_register_cpsr then ORs operand[3:0] into
 * PSTATE.{D,A,I,F}. These pure functions preserve that target and body only.
 * They erase AArch64_CheckSystemAccess, EL/feature trap checks, PostDecode,
 * dynamic execution occurrence, all other PSTATE fields, and interrupt
 * recognition or delivery. Interpreting a true result as an executed state
 * transition therefore requires those erased checks to admit execution.
 */

enum PSTATEWriteTarget = {PSTATEWriteTarget_DAIFSet}

val system_register_cpsr_daifset_target_pure :
  (bits(3), bits(4), bits(3)) -> (bool, PSTATEWriteTarget, bits(4))

function system_register_cpsr_daifset_target_pure (op2, CRm, op1) = {
    if op1 @ op2 == 0b011110 then {
        (true, PSTATEWriteTarget_DAIFSet, CRm)
    } else {
        (false, PSTATEWriteTarget_DAIFSet, CRm)
    }
}

val decode64_pstate_write_target_pure :
  bits(32) -> (bool, PSTATEWriteTarget, bits(4))

function decode64_pstate_write_target_pure (op_code) = {
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    if (op_code & 0xFFF8F01F) == 0xD500401F then {
        system_register_cpsr_daifset_target_pure(op2, CRm, op1)
    } else {
        (false, PSTATEWriteTarget_DAIFSet, CRm)
    }
}

val system_register_cpsr_daifset_pure :
  (bits(1), bits(1), bits(1), bits(1), bits(4)) ->
    (bits(1), bits(1), bits(1), bits(1))

function system_register_cpsr_daifset_pure (d, a, i, f, operand) = {
    let d_out : bits(1) = d | [operand[3]];
    let a_out : bits(1) = a | [operand[2]];
    let i_out : bits(1) = i | [operand[1]];
    let f_out : bits(1) = f | [operand[0]];
    (d_out, a_out, i_out, f_out)
}

/* ---------------------------------------------------------------------
 * General system-register MSR dispatch to selected cold-entry registers and
 * component updates from the pinned AArch64_AutoGen_SysRegWrite body.
 *
 * This pure projection erases AArch64_CheckSystemAccess, PostDecode, the
 * X-register read, dynamic occurrence, traps, and every state component other
 * than the selected register. Nested-virtualization redirects are retained as
 * a flag plus unchanged selected-register component; NVMem itself is erased.
 * Interpreting a direct update as execution requires separate access/trap
 * admission and an architectural proof for the projected predicate inputs.
 */

enum SystemRegisterWriteTarget = {
  SystemRegisterWriteTarget_VTTBR_EL2,
  SystemRegisterWriteTarget_VTCR_EL2,
  SystemRegisterWriteTarget_CNTHCTL_EL2,
  SystemRegisterWriteTarget_CNTVOFF_EL2,
  SystemRegisterWriteTarget_SP_EL1,
  SystemRegisterWriteTarget_ELR_EL2,
  SystemRegisterWriteTarget_SPSR_EL2,
  SystemRegisterWriteTarget_HCR_EL2
}

/* Plain ERET's exact decode/call target. Authenticated ERETAA/ERETAB are
 * deliberately not members of this projection. */
enum ExceptionReturnExecutionTarget = {
  ExceptionReturnExecutionTarget_ERET
}

struct PlainERETDecode = {
  encoding_valid : bool,
  pre_postdecode_checks_pass : bool,
  target : ExceptionReturnExecutionTarget,
  op4 : bits(5),
  Rn : bits(5),
  M : bits(1),
  A : bits(1),
  op2 : bits(5),
  pac : bool,
  use_key_a : bool
}

val decode64_plain_eret_pure : (bits(32), bool) -> PlainERETDecode

function decode64_plain_eret_pure (op_code, at_el0) = {
    let op4 : bits(5) = slice(op_code, 0, 5);
    let Rn : bits(5) = slice(op_code, 5, 5);
    let M : bits(1) = slice(op_code, 10, 1);
    let A : bits(1) = slice(op_code, 11, 1);
    let op2 : bits(5) = slice(op_code, 16, 5);
    let pac : bool = A == 0b1;
    let use_key_a : bool = M == 0b0;
    let encoding_valid : bool = op_code == 0xD69F03E0;
    let pre_postdecode_checks_pass : bool = encoding_valid & ~(at_el0) & ~(pac) &
      op4 == 0b00000 & Rn == 0b11111;
    struct {
      encoding_valid = encoding_valid,
      pre_postdecode_checks_pass = pre_postdecode_checks_pass,
      target = ExceptionReturnExecutionTarget_ERET,
      op4 = op4,
      Rn = Rn,
      M = M,
      A = A,
      op2 = op2,
      pac = pac,
      use_key_a = use_key_a
    }
}

/* One parsing pass for the eight register tuples in Oak's cold-entry prefix.
 * As in the per-register projections below, Rt is preserved rather than fixed
 * here; the bridge separately proves the exact X0 through X7 words. */
val system_register_cold_entry_target_pure :
  (bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) ->
    (bool, SystemRegisterWriteTarget, bits(5))

function system_register_cold_entry_target_pure (o0, op1, CRn, CRm, op2, Rt) = {
    if o0 == 0b1 & op1 == 0b100 & CRn == 0x1 & CRm == 0x1 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_HCR_EL2, Rt)
    } else if o0 == 0b1 & op1 == 0b100 & CRn == 0x2 & CRm == 0x1 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_VTTBR_EL2, Rt)
    } else if o0 == 0b1 & op1 == 0b100 & CRn == 0x2 & CRm == 0x1 &
        op2 == 0b010 then {
        (true, SystemRegisterWriteTarget_VTCR_EL2, Rt)
    } else if o0 == 0b1 & op1 == 0b100 & CRn == 0xE & CRm == 0x1 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_CNTHCTL_EL2, Rt)
    } else if o0 == 0b1 & op1 == 0b100 & CRn == 0xE & CRm == 0x0 &
        op2 == 0b011 then {
        (true, SystemRegisterWriteTarget_CNTVOFF_EL2, Rt)
    } else if o0 == 0b1 & op1 == 0b100 & CRn == 0x4 & CRm == 0x1 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_SP_EL1, Rt)
    } else if o0 == 0b1 & op1 == 0b100 & CRn == 0x4 & CRm == 0x0 &
        op2 == 0b001 then {
        (true, SystemRegisterWriteTarget_ELR_EL2, Rt)
    } else if o0 == 0b1 & op1 == 0b100 & CRn == 0x4 & CRm == 0x0 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_SPSR_EL2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_HCR_EL2, Rt)
    }
}

val decode64_cold_entry_system_write_pure :
  bits(32) -> (bool, SystemRegisterWriteTarget, bits(5))

function decode64_cold_entry_system_write_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let o0 : bits(1) = slice(op_code, 19, 1);
    if (op_code & 0xFFF00000) == 0xD5100000 then {
        system_register_cold_entry_target_pure(o0, op1, CRn, CRm, op2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_HCR_EL2, Rt)
    }
}

val system_register_vttbr_el2_target_pure :
  (bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) ->
    (bool, SystemRegisterWriteTarget, bits(5))

function system_register_vttbr_el2_target_pure (o0, op1, CRn, CRm, op2, Rt) = {
    if o0 == 0b1 & op1 == 0b100 & CRn == 0x2 & CRm == 0x1 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_VTTBR_EL2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_VTTBR_EL2, Rt)
    }
}

val decode64_system_write_vttbr_el2_pure :
  bits(32) -> (bool, SystemRegisterWriteTarget, bits(5))

function decode64_system_write_vttbr_el2_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let o0 : bits(1) = slice(op_code, 19, 1);
    if (op_code & 0xFFF00000) == 0xD5100000 then {
        system_register_vttbr_el2_target_pure(o0, op1, CRn, CRm, op2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_VTTBR_EL2, Rt)
    }
}

val aarch64_sysregwrite_vttbr_el2_pure :
  (bool, bool, bool, bool, bool, bool, bits(64), bits(64)) ->
    (bool, bits(64))

function aarch64_sysregwrite_vttbr_el2_pure (at_el1, hcr_nv, hcr_nv2,
    hcr_tge, scr_ns, scr_eel2, old_value, val_name) = {
    let redirected : bool = at_el1 & hcr_nv & hcr_nv2 & ~(hcr_tge) &
      (scr_ns | scr_eel2);
    if redirected then {
        (true, old_value)
    } else {
        (false, val_name)
    }
}

val system_register_vtcr_el2_target_pure :
  (bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) ->
    (bool, SystemRegisterWriteTarget, bits(5))

function system_register_vtcr_el2_target_pure (o0, op1, CRn, CRm, op2, Rt) = {
    if o0 == 0b1 & op1 == 0b100 & CRn == 0x2 & CRm == 0x1 &
        op2 == 0b010 then {
        (true, SystemRegisterWriteTarget_VTCR_EL2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_VTCR_EL2, Rt)
    }
}

val decode64_system_write_vtcr_el2_pure :
  bits(32) -> (bool, SystemRegisterWriteTarget, bits(5))

function decode64_system_write_vtcr_el2_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let o0 : bits(1) = slice(op_code, 19, 1);
    if (op_code & 0xFFF00000) == 0xD5100000 then {
        system_register_vtcr_el2_target_pure(o0, op1, CRn, CRm, op2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_VTCR_EL2, Rt)
    }
}

val aarch64_sysregwrite_vtcr_el2_pure :
  (bool, bool, bool, bool, bool, bool, bits(32), bits(64)) ->
    (bool, bits(32))

function aarch64_sysregwrite_vtcr_el2_pure (at_el1, hcr_nv, hcr_nv2,
    hcr_tge, scr_ns, scr_eel2, old_value, val_name) = {
    let redirected : bool = at_el1 & hcr_nv & hcr_nv2 & ~(hcr_tge) &
      (scr_ns | scr_eel2);
    if redirected then {
        (true, old_value)
    } else {
        (false, slice(val_name, 0, 32))
    }
}

val system_register_cnthctl_el2_target_pure :
  (bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) ->
    (bool, SystemRegisterWriteTarget, bits(5))

function system_register_cnthctl_el2_target_pure (o0, op1, CRn, CRm, op2, Rt) = {
    if o0 == 0b1 & op1 == 0b100 & CRn == 0xE & CRm == 0x1 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_CNTHCTL_EL2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_CNTHCTL_EL2, Rt)
    }
}

val decode64_system_write_cnthctl_el2_pure :
  bits(32) -> (bool, SystemRegisterWriteTarget, bits(5))

function decode64_system_write_cnthctl_el2_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let o0 : bits(1) = slice(op_code, 19, 1);
    if (op_code & 0xFFF00000) == 0xD5100000 then {
        system_register_cnthctl_el2_target_pure(o0, op1, CRn, CRm, op2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_CNTHCTL_EL2, Rt)
    }
}

val aarch64_sysregwrite_cnthctl_el2_pure : bits(64) -> bits(32)

function aarch64_sysregwrite_cnthctl_el2_pure (val_name) = {
    slice(val_name, 0, 32)
}

val system_register_cntvoff_el2_target_pure :
  (bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) ->
    (bool, SystemRegisterWriteTarget, bits(5))

function system_register_cntvoff_el2_target_pure (o0, op1, CRn, CRm, op2, Rt) = {
    if o0 == 0b1 & op1 == 0b100 & CRn == 0xE & CRm == 0x0 &
        op2 == 0b011 then {
        (true, SystemRegisterWriteTarget_CNTVOFF_EL2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_CNTVOFF_EL2, Rt)
    }
}

val decode64_system_write_cntvoff_el2_pure :
  bits(32) -> (bool, SystemRegisterWriteTarget, bits(5))

function decode64_system_write_cntvoff_el2_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let o0 : bits(1) = slice(op_code, 19, 1);
    if (op_code & 0xFFF00000) == 0xD5100000 then {
        system_register_cntvoff_el2_target_pure(o0, op1, CRn, CRm, op2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_CNTVOFF_EL2, Rt)
    }
}

val aarch64_sysregwrite_cntvoff_el2_pure :
  (bool, bool, bool, bool, bool, bool, bits(64), bits(64)) ->
    (bool, bits(64))

function aarch64_sysregwrite_cntvoff_el2_pure (at_el1, hcr_nv, hcr_nv2,
    hcr_tge, scr_ns, scr_eel2, old_value, val_name) = {
    let redirected : bool = at_el1 & hcr_nv & hcr_nv2 & ~(hcr_tge) &
      (scr_ns | scr_eel2);
    if redirected then {
        (true, old_value)
    } else {
        (false, val_name)
    }
}

val system_register_sp_el1_target_pure :
  (bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) ->
    (bool, SystemRegisterWriteTarget, bits(5))

function system_register_sp_el1_target_pure (o0, op1, CRn, CRm, op2, Rt) = {
    if o0 == 0b1 & op1 == 0b100 & CRn == 0x4 & CRm == 0x1 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_SP_EL1, Rt)
    } else {
        (false, SystemRegisterWriteTarget_SP_EL1, Rt)
    }
}

val decode64_system_write_sp_el1_pure :
  bits(32) -> (bool, SystemRegisterWriteTarget, bits(5))

function decode64_system_write_sp_el1_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let o0 : bits(1) = slice(op_code, 19, 1);
    if (op_code & 0xFFF00000) == 0xD5100000 then {
        system_register_sp_el1_target_pure(o0, op1, CRn, CRm, op2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_SP_EL1, Rt)
    }
}

val aarch64_sysregwrite_sp_el1_pure :
  (bool, bool, bool, bool, bool, bool, bits(64), bits(64)) ->
    (bool, bits(64))

function aarch64_sysregwrite_sp_el1_pure (at_el1, hcr_nv, hcr_nv2,
    hcr_tge, scr_ns, scr_eel2, old_value, val_name) = {
    let redirected : bool = at_el1 & hcr_nv & hcr_nv2 & ~(hcr_tge) &
      (scr_ns | scr_eel2);
    if redirected then {
        (true, old_value)
    } else {
        (false, val_name)
    }
}

val system_register_elr_el2_target_pure :
  (bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) ->
    (bool, SystemRegisterWriteTarget, bits(5))

function system_register_elr_el2_target_pure (o0, op1, CRn, CRm, op2, Rt) = {
    if o0 == 0b1 & op1 == 0b100 & CRn == 0x4 & CRm == 0x0 &
        op2 == 0b001 then {
        (true, SystemRegisterWriteTarget_ELR_EL2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_ELR_EL2, Rt)
    }
}

val decode64_system_write_elr_el2_pure :
  bits(32) -> (bool, SystemRegisterWriteTarget, bits(5))

function decode64_system_write_elr_el2_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let o0 : bits(1) = slice(op_code, 19, 1);
    if (op_code & 0xFFF00000) == 0xD5100000 then {
        system_register_elr_el2_target_pure(o0, op1, CRn, CRm, op2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_ELR_EL2, Rt)
    }
}

val aarch64_sysregwrite_elr_el2_pure : bits(64) -> bits(64)

function aarch64_sysregwrite_elr_el2_pure (val_name) = {
    val_name
}

val system_register_spsr_el2_target_pure :
  (bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) ->
    (bool, SystemRegisterWriteTarget, bits(5))

function system_register_spsr_el2_target_pure (o0, op1, CRn, CRm, op2, Rt) = {
    if o0 == 0b1 & op1 == 0b100 & CRn == 0x4 & CRm == 0x0 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_SPSR_EL2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_SPSR_EL2, Rt)
    }
}

val decode64_system_write_spsr_el2_pure :
  bits(32) -> (bool, SystemRegisterWriteTarget, bits(5))

function decode64_system_write_spsr_el2_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let o0 : bits(1) = slice(op_code, 19, 1);
    if (op_code & 0xFFF00000) == 0xD5100000 then {
        system_register_spsr_el2_target_pure(o0, op1, CRn, CRm, op2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_SPSR_EL2, Rt)
    }
}

val aarch64_sysregwrite_spsr_el2_pure : bits(64) -> bits(32)

function aarch64_sysregwrite_spsr_el2_pure (val_name) = {
    slice(val_name, 0, 32)
}

val system_register_hcr_el2_target_pure :
  (bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) ->
    (bool, SystemRegisterWriteTarget, bits(5))

function system_register_hcr_el2_target_pure (o0, op1, CRn, CRm, op2, Rt) = {
    if o0 == 0b1 & op1 == 0b100 & CRn == 0x1 & CRm == 0x1 &
        op2 == 0b000 then {
        (true, SystemRegisterWriteTarget_HCR_EL2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_HCR_EL2, Rt)
    }
}

val decode64_system_write_hcr_el2_pure :
  bits(32) -> (bool, SystemRegisterWriteTarget, bits(5))

function decode64_system_write_hcr_el2_pure (op_code) = {
    let Rt : bits(5) = slice(op_code, 0, 5);
    let op2 : bits(3) = slice(op_code, 5, 3);
    let CRm : bits(4) = slice(op_code, 8, 4);
    let CRn : bits(4) = slice(op_code, 12, 4);
    let op1 : bits(3) = slice(op_code, 16, 3);
    let o0 : bits(1) = slice(op_code, 19, 1);
    if (op_code & 0xFFF00000) == 0xD5100000 then {
        system_register_hcr_el2_target_pure(o0, op1, CRn, CRm, op2, Rt)
    } else {
        (false, SystemRegisterWriteTarget_HCR_EL2, Rt)
    }
}

val aarch64_sysregwrite_hcr_el2_pure :
  (bool, bool, bool, bool, bool, bool, bits(64), bits(64)) ->
    (bool, bits(64))

function aarch64_sysregwrite_hcr_el2_pure (at_el1, old_hcr_nv,
    old_hcr_nv2, old_hcr_tge, scr_ns, scr_eel2, old_value, val_name) = {
    let redirected : bool = at_el1 & old_hcr_nv & old_hcr_nv2 &
      ~(old_hcr_tge) & (scr_ns | scr_eel2);
    if redirected then {
        (true, old_value)
    } else {
        (false, val_name)
    }
}

/* The selected register-component state and X-register inputs for Oak's
 * ordered EL2 cold-entry prefix. These are projections, not Arm's full state. */
struct ColdEntryRegisterState = {
  hcr_el2 : bits(64),
  vttbr_el2 : bits(64),
  vtcr_el2 : bits(32),
  cnthctl_el2 : bits(32),
  cntvoff_el2 : bits(64),
  sp_el1 : bits(64),
  elr_el2 : bits(64),
  spsr_el2 : bits(32)
}

struct ColdEntryRegisterInputs = {
  hcr_el2 : bits(64),
  vttbr_el2 : bits(64),
  vtcr_el2 : bits(64),
  cnthctl_el2 : bits(64),
  cntvoff_el2 : bits(64),
  sp_el1 : bits(64),
  elr_el2 : bits(64),
  spsr_el2 : bits(64)
}

/* The eight fixed-position fields are an ordered log, avoiding any claim that
 * the final projected record alone witnesses dynamic program order. */
struct ColdEntryRegisterSequenceResult = {
  state : ColdEntryRegisterState,
  write0 : SystemRegisterWriteTarget,
  write1 : SystemRegisterWriteTarget,
  write2 : SystemRegisterWriteTarget,
  write3 : SystemRegisterWriteTarget,
  write4 : SystemRegisterWriteTarget,
  write5 : SystemRegisterWriteTarget,
  write6 : SystemRegisterWriteTarget,
  write7 : SystemRegisterWriteTarget
}

/* The dedicated AArch64_CheckForERetTrap NV predicate after projecting its
 * feature/EL/HCR reads to Booleans. False is not a global trap-freedom claim. */
val eret_nv_trap_route_pure : (bool, bool, bool, bool) -> bool

function eret_nv_trap_route_pure (have_nv_ext, el2_enabled, at_el1, hcr_nv) = {
    ((have_nv_ext & el2_enabled) & at_el1) & hcr_nv
}

struct PlainERETInputsAtEL2 = {
  dedicated_nv_trap : bool,
  target : bits(64),
  spsr : bits(32)
}

/* At AArch64 EL2, ELR() and SPSR() select ELR_EL2 and SPSR_EL2. This returns
 * those projected inputs to AArch64_ExceptionReturn; it does not execute it. */
val aarch64_plain_eret_at_el2_inputs_pure :
  (bool, bool, ColdEntryRegisterState) -> PlainERETInputsAtEL2

function aarch64_plain_eret_at_el2_inputs_pure (have_nv_ext, el2_enabled, state) = {
    let hcr_nv : bool = state.hcr_el2[42] == bitone;
    struct {
      dedicated_nv_trap = eret_nv_trap_route_pure(
        have_nv_ext, el2_enabled, false, hcr_nv),
      target = state.elr_el2,
      spsr = state.spsr_el2
    }
}

val aarch64_cold_entry_register_sequence_at_el2_pure :
  (ColdEntryRegisterState, ColdEntryRegisterInputs, bool, bool) ->
    ColdEntryRegisterSequenceResult

function aarch64_cold_entry_register_sequence_at_el2_pure (old_state, inputs, scr_ns, scr_eel2) = {
    let old_hcr_nv : bool = old_state.hcr_el2[42] == bitone;
    let old_hcr_nv2 : bool = old_state.hcr_el2[45] == bitone;
    let old_hcr_tge : bool = old_state.hcr_el2[27] == bitone;
    let (_, hcr_el2) = aarch64_sysregwrite_hcr_el2_pure(false,
      old_hcr_nv, old_hcr_nv2, old_hcr_tge, scr_ns, scr_eel2,
      old_state.hcr_el2, inputs.hcr_el2);
    let hcr_nv : bool = hcr_el2[42] == bitone;
    let hcr_nv2 : bool = hcr_el2[45] == bitone;
    let hcr_tge : bool = hcr_el2[27] == bitone;
    let (_, vttbr_el2) = aarch64_sysregwrite_vttbr_el2_pure(false,
      hcr_nv, hcr_nv2, hcr_tge, scr_ns, scr_eel2,
      old_state.vttbr_el2, inputs.vttbr_el2);
    let (_, vtcr_el2) = aarch64_sysregwrite_vtcr_el2_pure(false,
      hcr_nv, hcr_nv2, hcr_tge, scr_ns, scr_eel2,
      old_state.vtcr_el2, inputs.vtcr_el2);
    let cnthctl_el2 = aarch64_sysregwrite_cnthctl_el2_pure(inputs.cnthctl_el2);
    let (_, cntvoff_el2) = aarch64_sysregwrite_cntvoff_el2_pure(false,
      hcr_nv, hcr_nv2, hcr_tge, scr_ns, scr_eel2,
      old_state.cntvoff_el2, inputs.cntvoff_el2);
    let (_, sp_el1) = aarch64_sysregwrite_sp_el1_pure(false,
      hcr_nv, hcr_nv2, hcr_tge, scr_ns, scr_eel2,
      old_state.sp_el1, inputs.sp_el1);
    let elr_el2 = aarch64_sysregwrite_elr_el2_pure(inputs.elr_el2);
    let spsr_el2 = aarch64_sysregwrite_spsr_el2_pure(inputs.spsr_el2);
    struct {
      state = struct {
        hcr_el2 = hcr_el2,
        vttbr_el2 = vttbr_el2,
        vtcr_el2 = vtcr_el2,
        cnthctl_el2 = cnthctl_el2,
        cntvoff_el2 = cntvoff_el2,
        sp_el1 = sp_el1,
        elr_el2 = elr_el2,
        spsr_el2 = spsr_el2
      },
      write0 = SystemRegisterWriteTarget_HCR_EL2,
      write1 = SystemRegisterWriteTarget_VTTBR_EL2,
      write2 = SystemRegisterWriteTarget_VTCR_EL2,
      write3 = SystemRegisterWriteTarget_CNTHCTL_EL2,
      write4 = SystemRegisterWriteTarget_CNTVOFF_EL2,
      write5 = SystemRegisterWriteTarget_SP_EL1,
      write6 = SystemRegisterWriteTarget_ELR_EL2,
      write7 = SystemRegisterWriteTarget_SPSR_EL2
    }
}

/* Ordinary RET's pure decoder and BranchType_RET call target. Pointer
 * authentication, the X-register read, PostDecode, BTypeNext, and BranchTo
 * are deliberately not members of this projection. */
enum BranchRegisterExecutionTarget = {
  BranchRegisterExecutionTarget_RET
}

struct OrdinaryRETDecode = {
  encoding_valid : bool,
  pre_postdecode_checks_pass : bool,
  target : BranchRegisterExecutionTarget,
  Rm : bits(5),
  Rn : bits(5),
  M : bits(1),
  A : bits(1),
  op2 : bits(5),
  op : bits(2),
  Z : bits(1),
  pac : bool,
  source_is_sp : bool,
  use_key_a : bool
}

val decode64_ordinary_ret_pure : bits(32) -> OrdinaryRETDecode

function decode64_ordinary_ret_pure (op_code) = {
    let Rm : bits(5) = slice(op_code, 0, 5);
    let Rn : bits(5) = slice(op_code, 5, 5);
    let M : bits(1) = slice(op_code, 10, 1);
    let A : bits(1) = slice(op_code, 11, 1);
    let op2 : bits(5) = slice(op_code, 16, 5);
    let op : bits(2) = slice(op_code, 21, 2);
    let Z : bits(1) = slice(op_code, 24, 1);
    let pac : bool = A == 0b1;
    let source_is_sp : bool = Z == 0b1 & Rm == 0b11111;
    let use_key_a : bool = M == 0b0;
    let encoding_valid : bool = (op_code & 0xFFFFFC1F) == 0xD65F0000;
    let pre_postdecode_checks_pass : bool = encoding_valid & ~(pac) &
      Rm == 0b00000 & op == 0b10;
    struct {
      encoding_valid = encoding_valid,
      pre_postdecode_checks_pass = pre_postdecode_checks_pass,
      target = BranchRegisterExecutionTarget_RET,
      Rm = Rm,
      Rn = Rn,
      M = M,
      A = A,
      op2 = op2,
      op = op,
      Z = Z,
      pac = pac,
      source_is_sp = source_is_sp,
      use_key_a = use_key_a
    }
}

/* Ordinary B/BL-immediate pure decoder fields and static branch-class target.
 * The architectural PC read, PostDecode, BranchTo, target validation, and
 * observation of a transfer are deliberately not members of this projection.
 * BL's architectural X30 write is also excluded. Conditional branches are a
 * separate instruction class. */
enum DirectBranchImmediateExecutionTarget = {
  DirectBranchImmediateExecutionTarget_DIR,
  DirectBranchImmediateExecutionTarget_DIRCALL
}

struct OrdinaryBImmediateDecode = {
  encoding_valid : bool,
  target : DirectBranchImmediateExecutionTarget,
  imm26 : bits(26),
  op : bits(1),
  offset : bits(64)
}

val branch26_offset_pure : bits(26) -> bits(64)

function branch26_offset_pure (imm26) = {
    let scaled : bits(28) = imm26 @ 0b00;
    if imm26[25] == bitone then 0xFFFFFFFFF @ scaled
    else 0x000000000 @ scaled
}

val decode64_ordinary_b_immediate_pure : bits(32) -> OrdinaryBImmediateDecode

function decode64_ordinary_b_immediate_pure (op_code) = {
    let imm26 : bits(26) = slice(op_code, 0, 26);
    let op : bits(1) = slice(op_code, 31, 1);
    let encoding_valid : bool = (op_code & 0xFC000000) == 0x14000000;
    struct {
      encoding_valid = encoding_valid,
      target = DirectBranchImmediateExecutionTarget_DIR,
      imm26 = imm26,
      op = op,
      offset = branch26_offset_pure(imm26)
    }
}

val decode64_ordinary_bl_immediate_pure : bits(32) -> OrdinaryBImmediateDecode

function decode64_ordinary_bl_immediate_pure (op_code) = {
    let imm26 : bits(26) = slice(op_code, 0, 26);
    let op : bits(1) = slice(op_code, 31, 1);
    let encoding_valid : bool = (op_code & 0xFC000000) == 0x94000000;
    struct {
      encoding_valid = encoding_valid,
      target = DirectBranchImmediateExecutionTarget_DIRCALL,
      imm26 = imm26,
      op = op,
      offset = branch26_offset_pure(imm26)
    }
}
