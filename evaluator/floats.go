package evaluator

// Interpreter semantics for floating point (docs/spec/20-types.md section
// 11.3.8): f32 arithmetic is evaluated in Go float32 and f64 in float64,
// both correctly rounded for the operator set; the conversions and the
// intrinsic set match the C helpers bit for bit. The interpreter is the
// first witness of the three-witness rule.

import (
	"math"
	"math/big"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

// floatOf builds a Float of the given width, rounding the value once.
func floatOf(value float64, bits int) *object.Float {
	if bits == 32 {
		value = float64(float32(value))
	}
	return &object.Float{Value: value, Bits: bits}
}

// evalFloatLiteral rounds the literal to the width the checker recorded for
// its position (f64 without a record), exactly as the backend does.
func evalFloatLiteral(lit *ast.FloatLiteral, env *object.Environment) object.Object {
	name := "f64"
	if recorded, ok := env.ArithmeticWidth(lit.Token); ok && typechecker.IsFloatName(recorded) {
		name = recorded
	}
	value, ok := typechecker.FloatLiteralValue(lit.Text, name)
	if !ok {
		return newError("floating-point literal %s does not fit in %s", lit.Text, name)
	}
	return &object.Float{Value: value, Bits: typechecker.FloatBits(name)}
}

// evalFloatInfixExpression evaluates + - * / and the comparisons over two
// floats. The result width is the wider operand (f32 widens to f64); f32
// arithmetic rounds to float32 after each operation. Division by zero
// yields the IEEE result; comparisons are false on NaN.
func evalFloatInfixExpression(operator string, left, right *object.Float) object.Object {
	bits := left.Bits
	if right.Bits > bits {
		bits = right.Bits
	}
	a, b := left.Value, right.Value
	if bits == 32 {
		fa, fb := float32(a), float32(b)
		switch operator {
		case "+":
			return floatOf(float64(fa+fb), 32)
		case "-":
			return floatOf(float64(fa-fb), 32)
		case "*":
			return floatOf(float64(fa*fb), 32)
		case "/":
			return floatOf(float64(fa/fb), 32)
		}
	}
	switch operator {
	case "+":
		return floatOf(a+b, bits)
	case "-":
		return floatOf(a-b, bits)
	case "*":
		return floatOf(a*b, bits)
	case "/":
		return floatOf(a/b, bits)
	case "<":
		return nativeBoolToBooleanObject(a < b)
	case ">":
		return nativeBoolToBooleanObject(a > b)
	case "<=":
		return nativeBoolToBooleanObject(a <= b)
	case ">=":
		return nativeBoolToBooleanObject(a >= b)
	case "==":
		return nativeBoolToBooleanObject(a == b)
	case "!=":
		return nativeBoolToBooleanObject(a != b)
	}
	return newError("unknown operator: %s %s %s", left.Type(), operator, right.Type())
}

// evalFloatConstructor evaluates f32(x) / f64(x) over a float value: the
// one implicit move is widening; the checker has rejected everything else.
func evalFloatConstructor(typeName string, arg object.Object) object.Object {
	value, isFloat := arg.(*object.Float)
	if !isFloat {
		return newError("primitive constructor %s requires a floating-point argument, got %s", typeName, arg.Type())
	}
	return floatOf(value.Value, typechecker.FloatBits(typeName))
}

// evalFloatConversion evaluates the float rows of {target}_{op}_{source}.
func evalFloatConversion(name, target, op, source string, operand object.Object, env *object.Environment) object.Object {
	switch op {
	case "round":
		bits := typechecker.FloatBits(target)
		switch v := operand.(type) {
		case *object.Integer:
			if source[0] == 'u' {
				return floatOf(float64(uint64(v.Value)), bits)
			}
			return floatOf(float64(v.Value), bits)
		case *object.Float:
			return floatOf(v.Value, bits)
		}
	case "bits":
		switch v := operand.(type) {
		case *object.Integer:
			if target == "f32" {
				return &object.Float{Value: float64(math.Float32frombits(uint32(v.Value))), Bits: 32}
			}
			return &object.Float{Value: math.Float64frombits(uint64(v.Value)), Bits: 64}
		case *object.Float:
			if v.Bits == 32 {
				return &object.Integer{Value: int64(math.Float32bits(float32(v.Value)))}
			}
			return &object.Integer{Value: int64(math.Float64bits(v.Value))}
		}
	case "trunc", "saturating", "checked":
		v, isFloat := operand.(*object.Float)
		if !isFloat {
			break
		}
		value, inRange := truncateFloatToInteger(v.Value, target)
		switch op {
		case "trunc":
			if !inRange {
				return newError("%s: %v is outside the range of %s (the compiled program traps)", name, v.Value, target)
			}
			return &object.Integer{Value: value}
		case "saturating":
			return &object.Integer{Value: saturateFloatToInteger(v.Value, target)}
		case "checked":
			return checkedResult(name, target, value, inRange, env)
		}
	}
	return newError("%s requires a %s operand, got %s", name, source, operand.Type())
}

// truncateFloatToInteger truncates toward zero and reports whether the
// result lies in the target's range (NaN never does). The range test uses
// the same exact bounds as the C helper.
func truncateFloatToInteger(x float64, target string) (int64, bool) {
	bits := typechecker.PrimitiveBits(target)
	if x != x {
		return 0, false
	}
	if target[0] == 'i' {
		min := -math.Ldexp(1, bits-1)
		max := math.Ldexp(1, bits-1)
		if !(x > min-1 && x < max) && !(bits == 64 && x >= min && x < max) {
			return 0, false
		}
		return int64(x), true
	}
	max := math.Ldexp(1, bits)
	if !(x > -1 && x < max) {
		return 0, false
	}
	return int64(uint64(x)), true
}

// saturateFloatToInteger clamps to the target's range; NaN yields 0.
func saturateFloatToInteger(x float64, target string) int64 {
	if x != x {
		return 0
	}
	bits := typechecker.PrimitiveBits(target)
	if target[0] == 'i' {
		min := -math.Ldexp(1, bits-1)
		max := math.Ldexp(1, bits-1)
		if x >= max {
			return int64(1)<<uint(bits-1) - 1
		}
		if x <= min {
			return -(int64(1) << uint(bits-1))
		}
		return int64(x)
	}
	max := math.Ldexp(1, bits)
	if x >= max {
		return int64(widthMask(uint(bits)))
	}
	if x <= -1 {
		return 0
	}
	return int64(uint64(x))
}

// checkedResult builds Result[target, Overflow] like evalCheckedConversion.
func checkedResult(name, target string, value int64, inRange bool, env *object.Environment) object.Object {
	resultADT, hasResult := env.GetADTType("Result")
	overflowADT, hasOverflow := env.GetADTType("Overflow")
	if !hasResult || !hasOverflow || len(resultADT.Variants) < 2 || len(overflowADT.Variants) == 0 {
		return newError("%s requires declared Result[T, E] and Overflow types (docs/spec/20-types.md)", name)
	}
	if inRange {
		return &object.ADTValue{TypeName: "Result", Variant: resultADT.Variants[0].Name, Value: &object.Integer{Value: value}}
	}
	overflow := &object.ADTValue{TypeName: "Overflow", Variant: overflowADT.Variants[0].Name}
	return &object.ADTValue{TypeName: "Result", Variant: resultADT.Variants[1].Name, Value: overflow}
}

// evalFloatIntrinsic evaluates a float intrinsic (section 11.3.5) at the
// width the checker recorded for the call; f32 results round to float32.
// sqrt on f32 rounds the binary64 root once to binary32, which is correct
// (53 bits exceed the 2p+2 = 50 an innocuous double rounding needs); fma on
// f32 is formed exactly and rounded once (fma32).
func evalFloatIntrinsic(name string, call *ast.InvocationExpression, env *object.Environment) (object.Object, bool) {
	if !typechecker.FloatIntrinsicName(name) {
		return nil, false
	}
	if _, bound := env.Get(name); bound {
		return nil, false
	}
	width := 64
	if recorded, ok := env.ArithmeticWidth(call.Token); ok && recorded == "f32" {
		width = 32
	}
	values := make([]float64, 0, len(call.Arguments))
	for _, arg := range call.Arguments {
		evaluated := Eval(arg, env)
		if isError(evaluated) {
			return evaluated, true
		}
		f, isFloat := evaluated.(*object.Float)
		if !isFloat {
			return newError("%s requires floating-point operands, got %s", name, evaluated.Type()), true
		}
		values = append(values, f.Value)
	}
	num := func(v float64) object.Object { return floatOf(v, width) }
	boolean := func(b bool) object.Object { return nativeBoolToBooleanObject(b) }
	switch name {
	case "fma":
		if width == 32 {
			// One rounding, computed exactly: rounding a*b+c to binary64
			// first and to binary32 second can double-round (53 bits is
			// short of the 2p+2 = 50 needed only for p-bit *operands*, and
			// the exact product has 48 bits), so the sum is formed exactly
			// in arbitrary precision and rounded once to float32.
			return num(fma32(float32(values[0]), float32(values[1]), float32(values[2]))), true
		}
		return num(math.FMA(values[0], values[1], values[2])), true
	case "sqrt":
		if width == 32 {
			// Correct: a float32 square root is the float64 root rounded once
			// (the double result carries more than twice the precision).
			return num(float64(float32(math.Sqrt(float64(float32(values[0])))))), true
		}
		return num(math.Sqrt(values[0])), true
	case "abs":
		return num(math.Abs(values[0])), true
	case "copysign":
		return num(math.Copysign(values[0], values[1])), true
	case "floor":
		return num(math.Floor(values[0])), true
	case "ceil":
		return num(math.Ceil(values[0])), true
	case "trunc":
		return num(math.Trunc(values[0])), true
	case "round":
		return num(math.Round(values[0])), true
	case "round_even":
		return num(math.RoundToEven(values[0])), true
	case "min":
		return num(ieeeMinimum(values[0], values[1])), true
	case "max":
		return num(ieeeMaximum(values[0], values[1])), true
	case "min_num":
		return num(minNum(values[0], values[1])), true
	case "max_num":
		return num(maxNum(values[0], values[1])), true
	case "is_nan":
		return boolean(math.IsNaN(values[0])), true
	case "is_finite":
		return boolean(!math.IsNaN(values[0]) && !math.IsInf(values[0], 0)), true
	case "is_infinite":
		return boolean(math.IsInf(values[0], 0)), true
	case "is_normal":
		return boolean(isNormal(values[0], width)), true
	case "total_order":
		return boolean(totalOrder(values[0], values[1], width)), true
	}
	return newError("unknown floating-point intrinsic %s", name), true
}

// ieeeMinimum / ieeeMaximum are IEEE 754-2019 minimum/maximum: NaN wins,
// and -0.0 orders below +0.0.
func ieeeMinimum(a, b float64) float64 {
	if math.IsNaN(a) || math.IsNaN(b) {
		return math.NaN()
	}
	if a == b {
		if math.Signbit(a) {
			return a
		}
		return b
	}
	if a < b {
		return a
	}
	return b
}

func ieeeMaximum(a, b float64) float64 {
	if math.IsNaN(a) || math.IsNaN(b) {
		return math.NaN()
	}
	if a == b {
		if math.Signbit(a) {
			return b
		}
		return a
	}
	if a > b {
		return a
	}
	return b
}

// minNum / maxNum are the 2008 minNum/maxNum (C fmin/fmax): a NaN operand
// loses to a number.
func minNum(a, b float64) float64 {
	switch {
	case math.IsNaN(a):
		return b
	case math.IsNaN(b):
		return a
	}
	return ieeeMinimum(a, b)
}

func maxNum(a, b float64) float64 {
	switch {
	case math.IsNaN(a):
		return b
	case math.IsNaN(b):
		return a
	}
	return ieeeMaximum(a, b)
}

// isNormal reports a finite, nonzero, non-subnormal value at the width.
func isNormal(x float64, width int) bool {
	if math.IsNaN(x) || math.IsInf(x, 0) || x == 0 {
		return false
	}
	if width == 32 {
		exponent := (math.Float32bits(float32(x)) >> 23) & 0xFF
		return exponent != 0
	}
	exponent := (math.Float64bits(x) >> 52) & 0x7FF
	return exponent != 0
}

// totalOrder is IEEE 754-2019 totalOrder(a, b) over the bit patterns of the
// width, matching the C helper's key transform.
func totalOrder(a, b float64, width int) bool {
	key := func(x float64) int64 {
		if width == 32 {
			bits := int32(math.Float32bits(float32(x)))
			if bits < 0 {
				bits ^= 0x7FFFFFFF
			}
			return int64(bits)
		}
		bits := int64(math.Float64bits(x))
		if bits < 0 {
			bits ^= 0x7FFFFFFFFFFFFFFF
		}
		return bits
	}
	return key(a) <= key(b)
}

// fma32 is the correctly rounded binary32 fused multiply-add: the exact
// value of a*b + c is formed in arbitrary precision (the product needs 48
// bits and the alignment with c at most the exponent range more) and
// rounded once, to nearest even, to float32. Non-finite operands follow
// the IEEE rules through the double FMA, whose special-value behavior is
// the same and which cannot double-round on them.
func fma32(a, b, c float32) float64 {
	if math.IsNaN(float64(a)) || math.IsNaN(float64(b)) || math.IsNaN(float64(c)) ||
		math.IsInf(float64(a), 0) || math.IsInf(float64(b), 0) || math.IsInf(float64(c), 0) {
		return float64(float32(math.FMA(float64(a), float64(b), float64(c))))
	}
	const precision = 2048
	product := new(big.Float).SetPrec(precision).SetFloat64(float64(a))
	product.Mul(product, new(big.Float).SetPrec(precision).SetFloat64(float64(b)))
	sum := new(big.Float).SetPrec(precision).Add(product, new(big.Float).SetPrec(precision).SetFloat64(float64(c)))
	if sum.Sign() == 0 {
		// An exact zero takes the sign IEEE gives it: the sign of the
		// rounded product plus c under round to nearest, which the double
		// FMA reproduces exactly for zero results.
		return float64(float32(math.FMA(float64(a), float64(b), float64(c))))
	}
	rounded, _ := sum.Float32()
	return float64(rounded)
}
