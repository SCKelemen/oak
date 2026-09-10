package codegen

// C backend lowering for floating point (docs/spec/20-types.md section
// 11.3.8 and 90-backend.md section 7a): f32/f64 are float/double, every
// translation unit starts with `#pragma STDC FP_CONTRACT OFF`, literals are
// emitted as exact hexadecimal constants of the right width, `+ - * /` and
// comparisons are the plain C operators (their rounding is fixed by the
// pragma and by never passing fast-math flags), intrinsics lower to the C99
// <math.h> functions that are correctly rounded, and min/max/total_order
// lower to helpers with the IEEE 754-2019 semantics <math.h> lacks.

import (
	"fmt"
	"reflect"
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// floatPreamble is emitted once per translation unit, after the typedefs.
// It is all `static inline`, so unused helpers cost nothing and warn nothing.
const floatPreamble = `/* floating point (docs/spec/20-types.md section 11.3): IEEE 754 binary32/64,
   round to nearest even, no contraction (see the FP_CONTRACT pragma above),
   no fast-math. min/max take the IEEE 754-2019 minimum/maximum semantics:
   a NaN operand yields NaN and -0.0 orders below +0.0; min_num/max_num are
   fmin/fmax. total_order is IEEE 754-2019 totalOrder over the bit patterns. */
static inline f32 oak_fmin_f32(f32 a, f32 b) { if (a != a || b != b) { return a + b; } if (a == b) { return signbit(a) ? a : b; } return a < b ? a : b; }
static inline f32 oak_fmax_f32(f32 a, f32 b) { if (a != a || b != b) { return a + b; } if (a == b) { return signbit(a) ? b : a; } return a > b ? a : b; }
static inline f64 oak_fmin_f64(f64 a, f64 b) { if (a != a || b != b) { return a + b; } if (a == b) { return signbit(a) ? a : b; } return a < b ? a : b; }
static inline f64 oak_fmax_f64(f64 a, f64 b) { if (a != a || b != b) { return a + b; } if (a == b) { return signbit(a) ? b : a; } return a > b ? a : b; }
static inline int32_t oak_total_key_f32(f32 x) { union { f32 f; int32_t i; } pun; pun.f = x; return pun.i < 0 ? (int32_t)(pun.i ^ 0x7FFFFFFF) : pun.i; }
static inline int64_t oak_total_key_f64(f64 x) { union { f64 f; int64_t i; } pun; pun.f = x; return pun.i < 0 ? (int64_t)(pun.i ^ 0x7FFFFFFFFFFFFFFFLL) : pun.i; }
static inline int oak_total_order_f32(f32 a, f32 b) { return oak_total_key_f32(a) <= oak_total_key_f32(b); }
static inline int oak_total_order_f64(f64 a, f64 b) { return oak_total_key_f64(a) <= oak_total_key_f64(b); }

`

// floatCType maps an Oak float type to its C spelling (the typedefs in the
// header).
func floatCType(name string) (string, bool) {
	switch name {
	case "f32":
		return "f32", true
	case "f64":
		return "f64", true
	}
	return "", false
}

// emitFloatLiteral writes a literal as an exact C99 hexadecimal floating
// constant of the width the checker recorded (f64 when it recorded none),
// so the C compiler performs no decimal conversion of its own.
func (cg *CodeGenerator) emitFloatLiteral(lit *ast.FloatLiteral, tc *typechecker.TypeChecker) {
	name := "f64"
	if recorded, ok := tc.ArithmeticType(lit.Token); ok && typechecker.IsFloatName(recorded) {
		name = recorded
	}
	value, ok := typechecker.FloatLiteralValue(lit.Text, name)
	if !ok {
		cg.output.WriteString("OAK_FLOAT_LITERAL_OUT_OF_RANGE")
		return
	}
	if name == "f32" {
		cg.output.WriteString("((f32)" + strconv.FormatFloat(value, 'x', -1, 32) + "f)")
		return
	}
	cg.output.WriteString("((f64)" + strconv.FormatFloat(value, 'x', -1, 64) + ")")
}

// floatIntrinsicSpelling maps an Oak intrinsic to its C99 realization for
// one width. Every function named here is correctly rounded (C99 F.9) or a
// total bit operation, which is what makes the three-witness rule
// satisfiable; the helpers supply the 2019 NaN semantics.
func floatIntrinsicSpelling(name, width string) (string, bool) {
	suffix := ""
	if width == "f32" {
		suffix = "f"
	}
	switch name {
	case "fma", "sqrt", "floor", "ceil", "trunc", "round", "copysign":
		return name + suffix, true
	case "abs":
		return "fabs" + suffix, true
	case "round_even":
		// rint under the default (and only) rounding mode: ties to even.
		return "rint" + suffix, true
	case "min_num":
		return "fmin" + suffix, true
	case "max_num":
		return "fmax" + suffix, true
	case "min":
		return "oak_fmin_" + width, true
	case "max":
		return "oak_fmax_" + width, true
	case "total_order":
		return "oak_total_order_" + width, true
	case "is_nan":
		return "isnan", true
	case "is_finite":
		return "isfinite", true
	case "is_infinite":
		return "isinf", true
	case "is_normal":
		return "isnormal", true
	}
	return "", false
}

// emitFloatIntrinsicCall lowers a call the checker resolved as a float
// intrinsic (its width is recorded by the call's position). Reports whether
// the call was one.
func (cg *CodeGenerator) emitFloatIntrinsicCall(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || !typechecker.FloatIntrinsicName(ident.Value) {
		return false
	}
	if cg.programFunctions[ident.Value] != nil {
		return false // a program function of the same name shadows the intrinsic
	}
	width, recorded := tc.ArithmeticType(call.Token)
	if !recorded || !typechecker.IsFloatName(width) {
		return false
	}
	spelling, ok := floatIntrinsicSpelling(ident.Value, width)
	if !ok {
		cg.output.WriteString("OAK_UNSUPPORTED_FLOAT_INTRINSIC")
		return true
	}
	cType, _ := floatCType(width)
	cg.output.WriteString(fmt.Sprintf("%s( ", spelling))
	for i, arg := range call.Arguments {
		// Operands of a narrower width widen exactly to the call's width.
		cg.output.WriteString(fmt.Sprintf("(%s)( ", cType))
		cg.emitExpressionFragment(arg, tc)
		cg.output.WriteString(" )")
		if i < len(call.Arguments)-1 {
			cg.output.WriteString(", ")
		}
	}
	cg.output.WriteString(" )")
	return true
}

// expressionToken returns the position-carrying token of the expression
// shapes whose float width the checker records (literals, intrinsic calls,
// arithmetic), so a declaration without a type annotation can still be
// declared with the right C type.
func expressionToken(expr ast.Expression) (token.Token, bool) {
	switch e := expr.(type) {
	case *ast.FloatLiteral:
		return e.Token, true
	case *ast.InvocationExpression:
		return e.Token, true
	case *ast.InfixExpression:
		return e.Token, true
	case *ast.PrefixExpression:
		if e.Operator == "-" {
			return expressionToken(e.Right)
		}
	}
	return token.Token{}, false
}

// inferFloatLocalType reports the C type of an untyped local whose
// initializer the checker typed as a float.
func (cg *CodeGenerator) inferFloatLocalType(value ast.Expression, tc *typechecker.TypeChecker) (string, bool) {
	tok, ok := expressionToken(value)
	if !ok {
		return "", false
	}
	if name, recorded := tc.ArithmeticType(tok); recorded {
		if cType, isFloat := floatCType(name); isFloat {
			return cType, true
		}
	}
	return "", false
}

// floatConversionHelperSource builds the helper for a conversion row with a
// float on either side (docs/spec/20-types.md section 11.3.4). Float to
// integer never performs C's undefined out-of-range cast: trunc range-checks
// and traps, saturating clamps (NaN to 0), checked is emitted by the
// Result-returning path.
func floatConversionHelperSource(oakName, target, op, source string) string {
	helper := conversionHelperName(oakName)
	switch op {
	case "round":
		// int -> float and f64 -> f32: one correctly rounded C conversion.
		return fmt.Sprintf("static inline %s %s( %s x ) { return (%s)x; }\n", target, helper, source, target)
	case "bits":
		return fmt.Sprintf("static inline %s %s( %s x ) { union { %s from; %s to; } pun; pun.from = x; return pun.to; }\n", target, helper, source, source, target)
	case "trunc":
		low, high := floatIntegerBounds(target)
		return fmt.Sprintf("static inline %s %s( %s x ) {\n  if (!(x %s && x %s)) { __builtin_trap(); }\n  return (%s)x;\n}\n",
			target, helper, source, low, high, target)
	case "saturating":
		low, high := floatIntegerBounds(target)
		minC, maxC := integerExtremes(target)
		return fmt.Sprintf("static inline %s %s( %s x ) {\n  if (x != x) { return 0; }\n  if (!(x %s)) { return %s; }\n  if (!(x %s)) { return %s; }\n  return (%s)x;\n}\n",
			target, helper, source, low, minC, high, maxC, target)
	}
	return "OAK_UNSUPPORTED_CONVERSION\n"
}

// floatIntegerBounds returns the two comparisons a float must satisfy to
// truncate into the integer type: written against double constants that are
// exactly representable, so the check itself is exact. For the 64-bit types
// the exclusive lower bound (MIN - 1) is not representable, so the inclusive
// form against MIN (exactly representable) is used; the exclusive upper
// bound MAX + 1 is a power of two and exact for every width.
func floatIntegerBounds(target string) (low, high string) {
	bits := typechecker.PrimitiveBits(target)
	signed := target[0] == 'i'
	switch {
	case signed && bits == 64:
		return ">= -9223372036854775808.0", "< 9223372036854775808.0"
	case signed:
		min := -(int64(1) << uint(bits-1))
		max := int64(1) << uint(bits-1)
		return fmt.Sprintf("> %d.0", min-1), fmt.Sprintf("< %d.0", max)
	case bits == 64:
		return "> -1.0", "< 18446744073709551616.0"
	default:
		return "> -1.0", fmt.Sprintf("< %d.0", uint64(1)<<uint(bits))
	}
}

// integerExtremes spells the minimum and maximum of an integer type in C.
func integerExtremes(target string) (minC, maxC string) {
	bits := typechecker.PrimitiveBits(target)
	if target[0] == 'i' {
		return fmt.Sprintf("INT%d_MIN", bits), fmt.Sprintf("INT%d_MAX", bits)
	}
	return "0", fmt.Sprintf("UINT%d_MAX", bits)
}

// programUsesFloats reports whether any floating-point type, literal, or
// conversion appears in the program. The math header and the float helper
// block are emitted only then, so programs without floats stay
// freestanding (they include nothing but <stdint.h> and <stddef.h>).
func programUsesFloats(program *ast.Program) bool {
	found := false
	visit := func(value reflect.Value) {}
	visit = func(value reflect.Value) {
		if found || !value.IsValid() {
			return
		}
		switch value.Kind() {
		case reflect.Ptr, reflect.Interface:
			if value.IsNil() {
				return
			}
			if ptr, ok := value.Interface().(*ast.FloatLiteral); ok && ptr != nil {
				found = true
				return
			}
			if ident, ok := value.Interface().(*ast.Identifier); ok && ident != nil {
				if typechecker.IsFloatName(ident.Value) {
					found = true
					return
				}
				if target, _, source, isConversion := typechecker.ConversionParts(ident.Value); isConversion &&
					(typechecker.IsFloatName(target) || typechecker.IsFloatName(source)) {
					found = true
					return
				}
			}
			visit(value.Elem())
		case reflect.Struct:
			if value.Type() == reflect.TypeOf(token.Token{}) {
				return
			}
			for i := 0; i < value.NumField(); i++ {
				field := value.Field(i)
				if field.CanInterface() {
					visit(field)
				}
			}
		case reflect.Slice:
			for i := 0; i < value.Len(); i++ {
				visit(value.Index(i))
			}
		case reflect.Map:
			for _, key := range value.MapKeys() {
				visit(value.MapIndex(key))
			}
		}
	}
	visit(reflect.ValueOf(program))
	return found
}
