package asm

import (
	"fmt"
	"math"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// Floating point at the bit level (docs/spec/125-verification.md section
// 3). The decider models an f32 or f64 as its IEEE 754 bit pattern and
// lowers the total operations to bit operations: negation flips the sign,
// abs clears it, copysign mixes sign and magnitude, the classifiers test
// the exponent and mantissa fields, the comparisons are the sign-magnitude
// order with NaN below nothing, min and max are the backend's helpers
// (docs/spec/20-types.md section 11.3.5: a NaN operand yields a NaN whose
// bits the platform's addition chooses, so here it yields a fresh symbol
// no law can pin down; equal operands pick by sign; the rest by order),
// and total_order compares the backend's total keys signed. Arithmetic,
// rounding, sqrt, fma, min_num/max_num, and width conversions are not bit
// operations and fail closed.

// floatWidthOf reports the width of a floating-point expression, or false.
// A literal has no width of its own (the context decides).
func (lo *oakLowering) floatWidthOf(expr ast.Expression) (int, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		w, isFloat := lo.floats[e.Value]
		return w, isFloat
	case *ast.FloatLiteral:
		return 0, true
	case *ast.PrefixExpression:
		if e.Operator == "-" {
			return lo.floatWidthOf(e.Right)
		}
	case *ast.InfixExpression:
		switch e.Operator {
		case "+", "-", "*", "/":
			if w, isFloat := lo.floatWidthOf(e.Left); isFloat {
				return w, true
			}
			return lo.floatWidthOf(e.Right)
		}
	case *ast.MatchExpression:
		if whenTrue, _, isBool := boolConditional(e); isBool {
			return lo.floatWidthOf(whenTrue)
		}
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return 0, false
		}
		if _, shadowed := lo.functions[ident.Value]; shadowed {
			return 0, false
		}
		switch ident.Value {
		case "f32":
			return 32, true
		case "f64":
			return 64, true
		}
		if target, _, _, isConv := typechecker.ConversionParts(ident.Value); isConv {
			switch target {
			case "f32":
				return 32, true
			case "f64":
				return 64, true
			}
			return 0, false
		}
		if typechecker.FloatIntrinsicName(ident.Value) {
			switch ident.Value {
			case "is_nan", "is_finite", "is_infinite", "is_normal", "total_order":
				return 0, false
			}
			for _, arg := range e.Arguments {
				if w, isFloat := lo.floatWidthOf(arg); isFloat && w != 0 {
					return w, true
				}
			}
			return 0, true
		}
	}
	return 0, false
}

func floatMasks(w int) (sign, magnitude, exponent, mantissa uint64) {
	sign = uint64(1) << uint(w-1)
	magnitude = sign - 1
	if w == 32 {
		exponent = 0x7F800000
	} else {
		exponent = 0x7FF0000000000000
	}
	mantissa = magnitude &^ exponent
	return
}

func bit(t *term) *term          { return truncate(t, 1) }
func notBit(t *term) *term       { return binaryTerm("xor", bit(t), constTerm(1, 1)) }
func andBit(a, b *term) *term    { return binaryTerm("and", bit(a), bit(b)) }
func orBit(a, b *term) *term     { return binaryTerm("or", bit(a), bit(b)) }
func isBits(a, b *term) *term    { return bit(cmpTerm("eq", a, b)) }
func isNotBits(a, b *term) *term { return bit(cmpTerm("ne", a, b)) }

// floatIsNaN: exponent all ones and a nonzero mantissa.
func floatIsNaN(x *term, w int) *term {
	_, _, exponent, mantissa := floatMasks(w)
	return andBit(isBits(binaryTerm("and", x, constTerm(exponent, w)), constTerm(exponent, w)),
		isNotBits(binaryTerm("and", x, constTerm(mantissa, w)), constTerm(0, w)))
}

// floatCompare lowers an IEEE comparison of two w-bit patterns to a 1-bit
// term: NaN compares false to everything, the zeros are equal, and the
// rest is the sign-magnitude order.
func floatCompare(op string, a, b *term, w int) (*term, bool) {
	sign, magnitude, _, _ := floatMasks(w)
	nan := orBit(floatIsNaN(a, w), floatIsNaN(b, w))
	sa := bit(binaryTerm("shr", a, constTerm(uint64(w-1), w)))
	sb := bit(binaryTerm("shr", b, constTerm(uint64(w-1), w)))
	_ = sign
	magA := binaryTerm("and", a, constTerm(magnitude, w))
	magB := binaryTerm("and", b, constTerm(magnitude, w))
	bothZero := isBits(binaryTerm("or", magA, magB), constTerm(0, w))
	eq := andBit(notBit(nan), orBit(isBits(a, b), bothZero))
	less := func(x, y, sx, sy, magX, magY *term) *term {
		negOnly := andBit(sx, notBit(sy))
		bothNeg := andBit(andBit(sx, sy), bit(cmpTerm("hi", magX, magY)))
		bothPos := andBit(andBit(notBit(sx), notBit(sy)), bit(cmpTerm("lo", magX, magY)))
		return andBit(notBit(nan), andBit(notBit(bothZero), orBit(negOnly, orBit(bothNeg, bothPos))))
	}
	switch op {
	case "==":
		return eq, true
	case "!=":
		return notBit(eq), true
	case "<":
		return less(a, b, sa, sb, magA, magB), true
	case ">":
		return less(b, a, sb, sa, magB, magA), true
	case "<=":
		return orBit(less(a, b, sa, sb, magA, magB), eq), true
	case ">=":
		return orBit(less(b, a, sb, sa, magB, magA), eq), true
	}
	return nil, false
}

// floatArgumentWidth picks the operand width of a float intrinsic call:
// a typed argument's, else the context's.
func (lo *oakLowering) floatArgumentWidth(call *ast.InvocationExpression, width int) int {
	for _, arg := range call.Arguments {
		if w, isFloat := lo.floatWidthOf(arg); isFloat && w != 0 {
			return w
		}
	}
	if width == 64 {
		return 64
	}
	return 32
}

// lowerFloatIntrinsic lowers a float intrinsic to bit operations, or fails
// closed for the ones that are not.
func (lo *oakLowering) lowerFloatIntrinsic(name string, call *ast.InvocationExpression, width int) (*term, string, bool) {
	w := lo.floatArgumentWidth(call, width)
	sign, magnitude, exponent, mantissa := floatMasks(w)
	args := make([]*term, len(call.Arguments))
	for i, arg := range call.Arguments {
		value, reason, ok := lo.lower(arg, w)
		if !ok {
			return nil, reason, false
		}
		args[i] = value
	}
	asBool := func(t *term) (*term, string, bool) { return zeroExtend(bit(t), width), "", true }
	asFloat := func(t *term) (*term, string, bool) {
		if w < width {
			return zeroExtend(t, width), "", true
		}
		return truncate(t, width), "", true
	}
	switch name {
	case "abs":
		return asFloat(binaryTerm("and", args[0], constTerm(magnitude, w)))
	case "copysign":
		return asFloat(binaryTerm("or", binaryTerm("and", args[0], constTerm(magnitude, w)), binaryTerm("and", args[1], constTerm(sign, w))))
	case "is_nan":
		return asBool(floatIsNaN(args[0], w))
	case "is_finite":
		return asBool(isNotBits(binaryTerm("and", args[0], constTerm(exponent, w)), constTerm(exponent, w)))
	case "is_infinite":
		return asBool(andBit(isBits(binaryTerm("and", args[0], constTerm(exponent, w)), constTerm(exponent, w)),
			isBits(binaryTerm("and", args[0], constTerm(mantissa, w)), constTerm(0, w))))
	case "is_normal":
		field := binaryTerm("and", args[0], constTerm(exponent, w))
		return asBool(andBit(isNotBits(field, constTerm(0, w)), isNotBits(field, constTerm(exponent, w))))
	case "total_order":
		key := func(x *term) *term {
			negative := bit(binaryTerm("shr", x, constTerm(uint64(w-1), w)))
			return iteTerm(negative, binaryTerm("xor", x, constTerm(magnitude, w)), x)
		}
		return asBool(cmpTerm("le", key(args[0]), key(args[1])))
	case "min", "max":
		a, b := args[0], args[1]
		nan := orBit(floatIsNaN(a, w), floatIsNaN(b, w))
		eq, _ := floatCompare("==", a, b, w)
		lt, _ := floatCompare("<", a, b, w)
		sa := bit(binaryTerm("shr", a, constTerm(uint64(w-1), w)))
		var ordered *term
		if name == "min" {
			ordered = iteTerm(eq, iteTerm(sa, a, b), iteTerm(lt, a, b))
		} else {
			ordered = iteTerm(eq, iteTerm(sa, b, a), iteTerm(lt, b, a))
		}
		// A NaN operand: the backend returns a + b, whose payload the
		// platform chooses — a value no law may rely on.
		lo.freshFloats++
		fresh := fmt.Sprintf("%s#nan%d", name, lo.freshFloats)
		lo.fresh[fresh] = w
		return asFloat(iteTerm(nan, paramTerm(fresh, w), ordered))
	}
	return nil, fmt.Sprintf("the float intrinsic %s (not a bit operation)", name), false
}

// floatLiteralBits is a literal at the context's width.
func floatLiteralBits(value float64, width int) (*term, bool) {
	switch width {
	case 32:
		return constTerm(uint64(math.Float32bits(float32(value))), 32), true
	case 64:
		return constTerm(math.Float64bits(value), 64), true
	}
	return nil, false
}
