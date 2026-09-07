package evaluator

// Interpreter semantics for the explicit integer conversion family
// (docs/spec/20-types.md): total two's-complement trunc, saturating, and
// same-width cross-sign bits — matching the C helpers exactly.

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

// evalConversionCall evaluates {target}_{op}_{source}(x) when the name is a
// conversion function. Reports whether it was one.
func evalConversionCall(name string, args []ast.Expression, env *object.Environment) (object.Object, bool) {
	target, op, source, ok := typechecker.ConversionParts(name)
	if !ok {
		return nil, false
	}
	if op == "checked" {
		return newError("%s: checked conversions require Result[T, Overflow], which does not lower yet", name), true
	}
	if len(args) != 1 {
		return newError("%s takes exactly one argument", name), true
	}
	operandObject := Eval(args[0], env)
	if isError(operandObject) {
		return operandObject, true
	}
	operand, isInt := operandObject.(*object.Integer)
	if !isInt {
		return newError("%s requires an integer operand, got %s", name, operandObject.Type()), true
	}

	targetBits := uint(typechecker.PrimitiveBits(target))
	sourceSigned := source[0] == 'i'
	targetSigned := target[0] == 'i'
	value := operand.Value

	switch op {
	case "bits":
		// Same-width reinterpretation of the two's-complement pattern.
		mask := widthMask(targetBits)
		pattern := uint64(value) & mask
		if targetSigned {
			return &object.Integer{Value: signExtend(pattern, targetBits)}, true
		}
		return &object.Integer{Value: int64(pattern)}, true

	case "trunc":
		pattern := uint64(value) & widthMask(targetBits)
		if targetSigned {
			return &object.Integer{Value: signExtend(pattern, targetBits)}, true
		}
		return &object.Integer{Value: int64(pattern)}, true

	case "saturating":
		if targetSigned {
			max := int64(1)<<(targetBits-1) - 1
			min := -(int64(1) << (targetBits - 1))
			if value > max {
				value = max
			}
			if value < min {
				value = min
			}
			return &object.Integer{Value: value}, true
		}
		var maxUnsigned uint64 = widthMask(targetBits)
		unsignedValue := uint64(value)
		if sourceSigned && value < 0 {
			unsignedValue = 0 // saturating from a negative signed source clamps at zero
		}
		if unsignedValue > maxUnsigned {
			unsignedValue = maxUnsigned
		}
		return &object.Integer{Value: int64(unsignedValue)}, true
	}
	return newError("unknown conversion %s", name), true
}

func widthMask(bits uint) uint64 {
	if bits >= 64 {
		return ^uint64(0)
	}
	return (uint64(1) << bits) - 1
}

func signExtend(pattern uint64, bits uint) int64 {
	if bits >= 64 {
		return int64(pattern)
	}
	signBit := uint64(1) << (bits - 1)
	if pattern&signBit != 0 {
		return int64(pattern | ^widthMask(bits))
	}
	return int64(pattern)
}
