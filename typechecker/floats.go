package typechecker

// Floating-point types (docs/spec/20-types.md section 11.3): f32 and f64 as
// arithmetic types with contextual literals, implicit widening f32 -> f64
// only, explicit {target}_{op}_{source} conversions, and the correctly
// rounded intrinsic set. Everything here is the first increment: f16/bf16
// storage types, hexadecimal literals, and float SIMD are recorded gaps.

import (
	"math"
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// floatTypeBits are the arithmetic floating-point types and their widths.
var floatTypeBits = map[string]int{"f32": 32, "f64": 64}

// storageFloatNames are the storage-only formats (section 11.3.1): load,
// store, exact widening to f32, and rounding from f32 — no arithmetic,
// comparison, or literals. f16 and bf16 are the 16-bit ones; f8e4m3 and
// f8e5m2 are the OCP FP8 formats (8 bits: E4M3 without infinities and
// E5M2 with them), the storage the tensor emitters spelled by hand.
var storageFloatNames = map[string]bool{"f16": true, "bf16": true, "f8e4m3": true, "f8e5m2": true}

// storageCarrier is the unsigned integer a storage format reinterprets
// with (`bits`) and crosses the boundary as.
var storageCarrier = map[string]string{"f16": "u16", "bf16": "u16", "f8e4m3": "u8", "f8e5m2": "u8"}

// StorageCarrier reports the carrier integer type of a storage format.
func StorageCarrier(name string) string { return storageCarrier[name] }

// saturatingStorage are the formats with a saturating narrowing: the 8-bit
// formats, whose range is small enough that clamping is a common contract.
var saturatingStorage = map[string]bool{"f8e4m3": true, "f8e5m2": true}

// IsFloatName reports whether name is a floating-point arithmetic type.
func IsFloatName(name string) bool {
	_, ok := floatTypeBits[name]
	return ok
}

// IsStorageFloatName reports whether name is a storage-only float format.
func IsStorageFloatName(name string) bool { return storageFloatNames[name] }

func (tc *TypeChecker) isStorageFloatType(typ Type) bool {
	prim, ok := typ.(*PrimitiveType)
	return ok && storageFloatNames[prim.Name]
}

// isFloatLike reports an arithmetic or storage floating-point type, so the
// operator sites route both to the float rules (where storage types are
// rejected with a message naming the widening).
func (tc *TypeChecker) isFloatLike(typ Type) bool {
	return tc.isFloatType(typ) || tc.isStorageFloatType(typ)
}

// rejectStorageFloatOperand reports the use of a storage-only format in an
// operation and returns true when one was present.
func (tc *TypeChecker) rejectStorageFloatOperand(node ast.Node, what string, types ...Type) bool {
	for _, typ := range types {
		if prim, ok := typ.(*PrimitiveType); ok && storageFloatNames[prim.Name] {
			tc.addError(node, "%s is a storage format with no %s (docs/spec/20-types.md section 11.3.1); widen it first: f32(x)", prim.Name, what)
			return true
		}
	}
	return false
}

// FloatBits is the width of a floating-point type name (0 otherwise).
func FloatBits(name string) int { return floatTypeBits[name] }

func (tc *TypeChecker) isFloatType(typ Type) bool {
	prim, ok := typ.(*PrimitiveType)
	return ok && IsFloatName(prim.Name)
}

// promoteFloatTypes is the one implicit floating-point move: f32 widens to
// f64 (section 11.3.4); equal widths stay.
func promoteFloatTypes(left, right *PrimitiveType) *PrimitiveType {
	if floatTypeBits[left.Name] >= floatTypeBits[right.Name] {
		return left
	}
	return right
}

// FloatLiteralValue rounds a literal's text once to the named width,
// correctly rounded from the exact decimal value (section 11.3.2). ok is
// false when the value overflows the format; underflow to a subnormal or
// zero is the IEEE result and accepted.
func FloatLiteralValue(text, name string) (float64, bool) {
	bits := floatTypeBits[name]
	if bits == 0 {
		bits = 64
	}
	value, err := strconv.ParseFloat(text, bits)
	if err != nil {
		numErr, isNum := err.(*strconv.NumError)
		if !isNum || numErr.Err != strconv.ErrRange || math.IsInf(value, 0) {
			return 0, false
		}
	}
	return value, true
}

// checkFloatLiteral types a floating-point literal from its context: the
// expected float type, else f64. A float literal in an integer context is an
// error at the literal, as is one that overflows its format.
func (tc *TypeChecker) checkFloatLiteral(lit *ast.FloatLiteral, expected Type) Type {
	name := "f64"
	if prim, ok := expected.(*PrimitiveType); ok {
		switch {
		case IsFloatName(prim.Name):
			name = prim.Name
		case storageFloatNames[prim.Name]:
			tc.addError(lit, "%s has no literals (docs/spec/20-types.md section 11.3.1); write %s_round_f32(%s)", prim.Name, prim.Name, lit.Text)
			return prim
		case tc.isNumericType(prim):
			tc.addError(lit, "floating-point literal %s in integer context %s; an integer literal has no fraction or exponent", lit.Text, prim.Name)
			return prim
		}
	}
	if _, ok := FloatLiteralValue(lit.Text, name); !ok {
		tc.addError(lit, "floating-point literal %s does not fit in type %s", lit.Text, name)
		return &PrimitiveType{Name: name}
	}
	tc.recordFloatWidth(lit.Token, name)
	return &PrimitiveType{Name: name}
}

// recordFloatWidth notes the float type of a literal or intrinsic call by
// position, in the same oracle the backend and interpreter already consult
// for integer widths (ArithmeticType): "f32" or "f64" instead of u8..i64.
func (tc *TypeChecker) recordFloatWidth(tok token.Token, name string) {
	if tc.arithmeticTypes == nil {
		tc.arithmeticTypes = make(map[string]string)
	}
	tc.arithmeticTypes[positionKey(tok)] = name
}

// checkFloatArithmetic types + - * / over floats: both operands must be
// floats, f32 widening to f64. `%` is not defined on floats.
func (tc *TypeChecker) checkFloatArithmetic(expr *ast.InfixExpression, left, right Type) Type {
	if tc.rejectStorageFloatOperand(expr, "arithmetic", left, right) {
		return nil
	}
	leftPrim, leftOk := left.(*PrimitiveType)
	rightPrim, rightOk := right.(*PrimitiveType)
	if !leftOk || !rightOk || !IsFloatName(leftPrim.Name) || !IsFloatName(rightPrim.Name) {
		tc.addError(expr, "operator %s requires two floating-point operands, got %s and %s; conversions between integers and floats are explicit (docs/spec/20-types.md section 11.3.4)", expr.Operator, left, right)
		return nil
	}
	if expr.Operator == "%" {
		tc.addError(expr, "operator %% is not defined on floating-point types (docs/spec/20-types.md section 11.3.5)")
		return nil
	}
	return tc.recordArithmetic(expr, promoteFloatTypes(leftPrim, rightPrim))
}

// checkFloatComparison types == != < <= > >= over floats: both operands
// floats; the result is Bool with IEEE semantics at runtime (NaN compares
// false, +0.0 == -0.0).
func (tc *TypeChecker) checkFloatComparison(expr *ast.InfixExpression, left, right Type) Type {
	if tc.rejectStorageFloatOperand(expr, "comparison", left, right) {
		return nil
	}
	if !tc.isFloatType(left) || !tc.isFloatType(right) {
		tc.addError(expr, "operator %s requires two floating-point operands, got %s and %s; conversions between integers and floats are explicit (docs/spec/20-types.md section 11.3.4)", expr.Operator, left, right)
		return nil
	}
	return &BoolType{}
}

// checkFloatConstructor types f32(x) / f64(x): a float literal takes the
// width, a float value may widen (f32 -> f64) or stay; everything else is
// spelled as an explicit conversion (section 11.3.4).
func (tc *TypeChecker) checkFloatConstructor(typeName string, arg ast.Expression, call *ast.InvocationExpression) Type {
	target := &PrimitiveType{Name: typeName}
	if storageFloatNames[typeName] {
		tc.addError(arg, "%s has no constructor: it is a storage format (docs/spec/20-types.md section 11.3.1); write %s_round_f32(x)", typeName, typeName)
		return nil
	}
	switch lit := arg.(type) {
	case *ast.FloatLiteral:
		return tc.checkFloatLiteral(lit, target)
	case *ast.IntegerLiteral:
		tc.addError(lit, "%s(%d) is not a floating-point literal; spell it %d.0", typeName, lit.Value, lit.Value)
		return nil
	}
	argType := tc.checkExpression(arg)
	if argType == nil {
		return nil
	}
	// c.Float / c.Double convert back bit-preservingly (docs/spec/92-ffi.md
	// section 2.2).
	if cConversionToOak(typeName, argType) {
		return target
	}
	prim, isPrim := argType.(*PrimitiveType)
	switch {
	case isPrim && storageFloatNames[prim.Name]:
		// Exact widening of a storage format; only f32 receives it
		// (section 11.3.1). The source format is recorded at the call so
		// the backend selects the widening helper.
		if typeName != "f32" {
			tc.addError(arg, "%s widens to f32 only; write f64(f32(x))", prim.Name)
			return nil
		}
		if call != nil {
			tc.recordFloatWidth(call.Token, "widen_"+prim.Name)
		}
		return target
	case isPrim && IsFloatName(prim.Name):
		if floatTypeBits[prim.Name] > floatTypeBits[typeName] {
			tc.addError(arg, "cannot narrow %s to %s implicitly; spell the rounding: %s_round_%s(x)", prim.Name, typeName, typeName, prim.Name)
			return nil
		}
		return target
	case isPrim && tc.isNumericType(prim):
		source := tc.FixedWidthName(prim.Name)
		if source == "" {
			source = prim.Name
		}
		tc.addError(arg, "%s(x) does not convert integers; spell the rounding: %s_round_%s(x) (docs/spec/20-types.md section 11.3.4)", typeName, typeName, source)
		return nil
	}
	tc.addError(arg, "primitive constructor %s requires a floating-point argument, got %s", typeName, argType)
	return nil
}

// checkFloatConversion types the float rows of the {target}_{op}_{source}
// family (section 11.3.4). Called when either side is a float.
func (tc *TypeChecker) checkFloatConversion(funcName, target, op, source string, arg ast.Expression) Type {
	targetFloat, sourceFloat := IsFloatName(target), IsFloatName(source)
	targetStorage, sourceStorage := storageFloatNames[target], storageFloatNames[source]
	valid := false
	switch op {
	case "round":
		switch {
		case targetStorage:
			// f16_round_f32 / bf16_round_f32: the one way into a storage
			// format (section 11.3.1).
			valid = source == "f32"
		case targetFloat && sourceFloat:
			// Wider float to narrower float: one rounding.
			valid = floatTypeBits[source] > floatTypeBits[target]
			if !valid {
				tc.addError(arg, "%s widens; write %s(x) (widening between floating-point types is implicit)", funcName, target)
				return nil
			}
		case targetFloat && sourceStorage:
			tc.addError(arg, "%s widens exactly; write %s(x)", funcName, target)
			return nil
		case targetFloat:
			valid = true // integer to float
		}
	case "bits":
		// Reinterpretation with the unsigned integer of the same width.
		valid = (targetFloat && source == "u"+strconv.Itoa(floatTypeBits[target])) ||
			(sourceFloat && target == "u"+strconv.Itoa(floatTypeBits[source])) ||
			(targetStorage && source == storageCarrier[target]) || (sourceStorage && target == storageCarrier[source])
	case "saturating":
		// f8e4m3_saturating_f32 / f8e5m2_saturating_f32 clamp finite values
		// to the format's largest finite magnitude (section 11.3.1);
		// otherwise the float-to-integer row.
		valid = (targetStorage && saturatingStorage[target] && source == "f32") ||
			(sourceFloat && !targetFloat && !targetStorage)
	case "trunc", "checked":
		valid = sourceFloat && !targetFloat && !targetStorage
	}
	if !valid {
		tc.addError(arg, "%s is not a conversion the specification defines (docs/spec/20-types.md section 11.3.4)", funcName)
		return nil
	}
	sourcePrim := &PrimitiveType{Name: source}
	argType := tc.checkExpression(arg, sourcePrim)
	if argType == nil {
		return nil
	}
	argPrim, ok := argType.(*PrimitiveType)
	if !ok || normalizePrimitiveName(argPrim.Name) != source {
		tc.addError(arg, "%s expects argument of type %s, got %s", funcName, source, argType)
		return nil
	}
	if op == "checked" {
		targetPrim := &PrimitiveType{Name: target}
		overflow := &ADTType{Name: "Overflow"}
		tc.recordADTInstantiation("Result", []Type{targetPrim, overflow})
		return &GenericType{Name: "Result", TypeArgs: []Type{targetPrim, overflow}}
	}
	return &PrimitiveType{Name: target}
}

// floatIntrinsic describes one correctly rounded intrinsic (section 11.3.5):
// its arity and whether it yields Bool instead of the operand type.
type floatIntrinsic struct {
	arity int
	bool  bool
}

var floatIntrinsics = map[string]floatIntrinsic{
	"fma": {3, false}, "sqrt": {1, false}, "abs": {1, false}, "copysign": {2, false},
	"floor": {1, false}, "ceil": {1, false}, "trunc": {1, false}, "round": {1, false}, "round_even": {1, false},
	"min": {2, false}, "max": {2, false}, "min_num": {2, false}, "max_num": {2, false},
	"is_nan": {1, true}, "is_finite": {1, true}, "is_infinite": {1, true}, "is_normal": {1, true},
	"total_order": {2, true},
}

// FloatIntrinsicName reports whether name is a floating-point intrinsic.
// A user binding of the same name shadows the intrinsic; callers check the
// environment first.
func FloatIntrinsicName(name string) bool {
	_, ok := floatIntrinsics[name]
	return ok
}

// checkFloatIntrinsic types a call to a float intrinsic: every operand is a
// float of one width (a typed operand fixes it, literal-only operands take
// it, an all-literal call is f64), the result is that width or Bool. The
// width is recorded by the call's position for the backend and interpreter.
// Returns nil when name is not an intrinsic or a user binding shadows it.
func (tc *TypeChecker) checkFloatIntrinsic(name string, expr *ast.InvocationExpression) Type {
	sig, ok := floatIntrinsics[name]
	if !ok {
		return nil
	}
	if _, bound := tc.env.Get(name); bound {
		return nil
	}
	if len(expr.Arguments) != sig.arity {
		tc.addError(expr, "%s takes %d floating-point argument(s), got %d", name, sig.arity, len(expr.Arguments))
		return &PrimitiveType{Name: "f64"}
	}
	var width *PrimitiveType
	for _, arg := range expr.Arguments {
		if IsLiteralOnlyExpression(arg) {
			continue
		}
		argType := tc.checkExpression(arg)
		if argType == nil {
			return &PrimitiveType{Name: "f64"}
		}
		prim, isPrim := argType.(*PrimitiveType)
		if !isPrim || !IsFloatName(prim.Name) {
			tc.addError(arg, "%s requires floating-point operands, got %s (docs/spec/20-types.md section 11.3.5)", name, argType)
			return &PrimitiveType{Name: "f64"}
		}
		if width == nil || floatTypeBits[prim.Name] > floatTypeBits[width.Name] {
			width = prim
		}
	}
	if width == nil {
		width = &PrimitiveType{Name: "f64"}
	}
	for _, arg := range expr.Arguments {
		if !IsLiteralOnlyExpression(arg) {
			continue
		}
		if tc.checkExpression(arg, width) == nil {
			return width
		}
	}
	tc.recordFloatWidth(expr.Token, width.Name)
	if sig.bool {
		return &BoolType{}
	}
	return width
}
