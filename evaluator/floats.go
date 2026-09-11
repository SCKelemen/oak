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
	// A storage format widens exactly: its Value already is the widened
	// number (section 11.3.1).
	return floatOf(value.Value, typechecker.FloatBits(typeName))
}

// evalFloatConversion evaluates the float rows of {target}_{op}_{source}.
func evalFloatConversion(name, target, op, source string, operand object.Object, env *object.Environment) object.Object {
	switch op {
	case "round", "saturating":
		if typechecker.IsStorageFloatName(target) {
			// f16_round_f32 / bf16_round_f32 / f8e4m3_round_f32 /
			// f8e5m2_round_f32: nearest even into the storage format, kept
			// as its exact widened value; the 8-bit saturating forms clamp
			// finite overflow instead.
			if v, isFloat := operand.(*object.Float); isFloat {
				return storageFloat(target, storageRound(target, float32(v.Value), op == "saturating"))
			}
			break
		}
		if op == "saturating" {
			v, isFloat := operand.(*object.Float)
			if !isFloat {
				break
			}
			return &object.Integer{Value: saturateFloatToInteger(v.Value, target)}
		}
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
			switch target {
			case "f32":
				return &object.Float{Value: float64(math.Float32frombits(uint32(v.Value))), Bits: 32}
			case "f16", "bf16", "f8e4m3", "f8e5m2":
				return storageFloat(target, uint16(v.Value))
			}
			return &object.Float{Value: math.Float64frombits(uint64(v.Value)), Bits: 64}
		case *object.Float:
			switch v.Bits {
			case 8, 16:
				return &object.Integer{Value: int64(storageBits(v))}
			case 32:
				return &object.Integer{Value: int64(math.Float32bits(float32(v.Value)))}
			}
			return &object.Integer{Value: int64(math.Float64bits(v.Value))}
		}
	case "trunc", "checked":
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

// Storage formats (docs/spec/20-types.md section 11.3.1): binary16 and
// bfloat16 as bit patterns, widened exactly and rounded to nearest even —
// the same arithmetic as the C helpers, bit for bit.

// halfToFloat32 widens a binary16 bit pattern exactly.
func halfToFloat32(h uint16) float32 {
	sign := uint32(h&0x8000) << 16
	exp := uint32(h>>10) & 0x1F
	mant := uint32(h & 0x3FF)
	switch {
	case exp == 0x1F:
		return math.Float32frombits(sign | 0x7F800000 | mant<<13)
	case exp == 0:
		if mant == 0 {
			return math.Float32frombits(sign)
		}
		e := int32(1)
		for mant&0x400 == 0 {
			mant <<= 1
			e--
		}
		mant &= 0x3FF
		return math.Float32frombits(sign | uint32(e+112)<<23 | mant<<13)
	}
	return math.Float32frombits(sign | (exp+112)<<23 | mant<<13)
}

// float32ToHalf rounds a binary32 value to binary16, nearest even, with
// subnormals, overflow to infinity, and quiet NaN preserved.
func float32ToHalf(x float32) uint16 {
	u := math.Float32bits(x)
	sign := uint32(u>>16) & 0x8000
	exp := (u >> 23) & 0xFF
	mant := u & 0x7FFFFF
	if exp == 0xFF {
		if mant != 0 {
			return uint16(sign | 0x7C00 | 0x200 | mant>>13)
		}
		return uint16(sign | 0x7C00)
	}
	e := int32(exp) - 127 + 15
	if e >= 0x1F {
		return uint16(sign | 0x7C00)
	}
	if e <= 0 {
		if e < -10 {
			return uint16(sign)
		}
		mant |= 0x800000
		shift := uint32(14 - e)
		half := mant >> shift
		rem := mant & (1<<shift - 1)
		midpoint := uint32(1) << (shift - 1)
		if rem > midpoint || (rem == midpoint && half&1 == 1) {
			half++
		}
		return uint16(sign | half)
	}
	half := uint32(e)<<10 | mant>>13
	rem := mant & 0x1FFF
	if rem > 0x1000 || (rem == 0x1000 && half&1 == 1) {
		half++
	}
	return uint16(sign | half)
}

// bfloat16ToFloat32 widens a bfloat16 bit pattern exactly.
func bfloat16ToFloat32(h uint16) float32 { return math.Float32frombits(uint32(h) << 16) }

// float32ToBfloat16 rounds a binary32 value to bfloat16, nearest even,
// quiet NaN preserved.
func float32ToBfloat16(x float32) uint16 {
	u := math.Float32bits(x)
	if (u>>23)&0xFF == 0xFF && u&0x7FFFFF != 0 {
		return uint16(u>>16 | 0x40)
	}
	upper := u >> 16
	rem := u & 0xFFFF
	if rem > 0x8000 || (rem == 0x8000 && upper&1 == 1) {
		upper++
	}
	return uint16(upper)
}

// storageFloat builds the storage-format object for a bit pattern.
func storageFloat(format string, bits uint16) *object.Float {
	var value float32
	width := 16
	switch format {
	case "f16":
		value = halfToFloat32(bits)
	case "bf16":
		value = bfloat16ToFloat32(bits)
	case "f8e4m3":
		value, width = F8E4M3ToFloat32(uint8(bits)), 8
	case "f8e5m2":
		value, width = F8E5M2ToFloat32(uint8(bits)), 8
	}
	return &object.Float{Value: float64(value), Bits: width, Format: format}
}

// storageBits recovers the bit pattern of a storage-format value. A stored
// value is exactly representable in its format, so rounding it again is
// the identity; a NaN reproduces the format's quiet NaN.
func storageBits(f *object.Float) uint16 {
	switch f.Format {
	case "f16":
		return float32ToHalf(float32(f.Value))
	case "f8e4m3":
		return uint16(Float32ToF8E4M3(float32(f.Value)))
	case "f8e5m2":
		return uint16(Float32ToF8E5M2(float32(f.Value)))
	}
	return float32ToBfloat16(float32(f.Value))
}

// storageRound rounds an f32 into a storage format's bit pattern (nearest
// even; the format's own overflow rule), or clamps when saturating.
func storageRound(format string, x float32, saturating bool) uint16 {
	switch format {
	case "f16":
		return float32ToHalf(x)
	case "bf16":
		return float32ToBfloat16(x)
	case "f8e4m3":
		if saturating {
			return uint16(Float32ToF8E4M3Saturating(x))
		}
		return uint16(Float32ToF8E4M3(x))
	case "f8e5m2":
		if saturating {
			return uint16(Float32ToF8E5M2Saturating(x))
		}
		return uint16(Float32ToF8E5M2(x))
	}
	return 0
}

// OCP FP8 E4M3 (docs/spec/20-types.md section 11.3.1): bias 7, three
// fraction bits, no infinities, NaN is exponent and fraction all ones,
// largest finite 448. The interpreter and the C preamble are the same bit
// work, so they agree on every input.
func F8E4M3ToFloat32(h uint8) float32 {
	sign := uint32(h&0x80) << 24
	exp := uint32(h>>3) & 0xF
	mant := uint32(h & 0x7)
	if exp == 0xF && mant == 0x7 {
		return math.Float32frombits(sign | 0x7FC00000)
	}
	if exp == 0 {
		if mant == 0 {
			return math.Float32frombits(sign)
		}
		exp = 1
		for mant&0x8 == 0 {
			mant <<= 1
			exp--
		}
		mant &= 0x7
	}
	return math.Float32frombits(sign | (exp+120)<<23 | mant<<20)
}

func Float32ToF8E4M3(x float32) uint8 {
	u := math.Float32bits(x)
	sign := uint32(u>>24) & 0x80
	exp := (u >> 23) & 0xFF
	mant := u & 0x7FFFFF
	if exp == 0xFF {
		return uint8(sign | 0x7F)
	}
	e := int32(exp) - 127 + 7
	if e >= 16 {
		return uint8(sign | 0x7F)
	}
	var enc uint32
	if e <= 0 {
		if e < -3 {
			return uint8(sign)
		}
		mant |= 0x800000
		shift := uint32(21 - e)
		rem := mant & (1<<shift - 1)
		midpoint := uint32(1) << (shift - 1)
		enc = mant >> shift
		if rem > midpoint || (rem == midpoint && enc&1 == 1) {
			enc++
		}
	} else {
		rem := mant & 0xFFFFF
		enc = uint32(e)<<3 | mant>>20
		if rem > 0x80000 || (rem == 0x80000 && enc&1 == 1) {
			enc++
		}
	}
	if enc >= 0x7F {
		return uint8(sign | 0x7F)
	}
	return uint8(sign | enc)
}

func Float32ToF8E4M3Saturating(x float32) uint8 {
	r := Float32ToF8E4M3(x)
	if r&0x7F == 0x7F && x == x {
		return r&0x80 | 0x7E
	}
	return r
}

// OCP FP8 E5M2: bias 15, two fraction bits, infinities and NaN as IEEE,
// largest finite 57344; overflow is infinity.
func F8E5M2ToFloat32(h uint8) float32 {
	sign := uint32(h&0x80) << 24
	exp := uint32(h>>2) & 0x1F
	mant := uint32(h & 0x3)
	if exp == 0x1F {
		// NaN payloads widen quiet: a signaling f32 NaN would not survive
		// the interpreter's float64 value, and nothing reads the payload.
		quiet := uint32(0)
		if mant != 0 {
			quiet = 0x400000
		}
		return math.Float32frombits(sign | 0x7F800000 | quiet | mant<<21)
	}
	if exp == 0 {
		if mant == 0 {
			return math.Float32frombits(sign)
		}
		exp = 1
		for mant&0x4 == 0 {
			mant <<= 1
			exp--
		}
		mant &= 0x3
	}
	return math.Float32frombits(sign | (exp+112)<<23 | mant<<21)
}

func Float32ToF8E5M2(x float32) uint8 {
	u := math.Float32bits(x)
	sign := uint32(u>>24) & 0x80
	exp := (u >> 23) & 0xFF
	mant := u & 0x7FFFFF
	if exp == 0xFF {
		// Every NaN narrows to the quiet NaN without payload; infinity keeps
		// its sign.
		if mant != 0 {
			return uint8(sign | 0x7E)
		}
		return uint8(sign | 0x7C)
	}
	e := int32(exp) - 127 + 15
	if e >= 31 {
		return uint8(sign | 0x7C)
	}
	var enc uint32
	if e <= 0 {
		if e < -2 {
			return uint8(sign)
		}
		mant |= 0x800000
		shift := uint32(22 - e)
		rem := mant & (1<<shift - 1)
		midpoint := uint32(1) << (shift - 1)
		enc = mant >> shift
		if rem > midpoint || (rem == midpoint && enc&1 == 1) {
			enc++
		}
	} else {
		rem := mant & 0x1FFFFF
		enc = uint32(e)<<2 | mant>>21
		if rem > 0x100000 || (rem == 0x100000 && enc&1 == 1) {
			enc++
		}
	}
	return uint8(sign | enc)
}

func Float32ToF8E5M2Saturating(x float32) uint8 {
	r := Float32ToF8E5M2(x)
	if r&0x7F == 0x7C && x == x && !math.IsInf(float64(x), 0) {
		return r&0x80 | 0x7B
	}
	return r
}
