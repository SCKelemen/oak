package evaluator

// Interpreter semantics for checked and saturating integer arithmetic
// (docs/spec/20-types.md section 11.1a). The exact mathematical result is
// computed in arbitrary precision and compared with the type's range, so
// the interpreter and the C helpers agree at every boundary.

import (
	"math/big"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

// evalArithmeticCall evaluates {type}_{checked|saturating}_{add|sub|mul}(a, b)
// when the name is one; reports whether it was.
func evalArithmeticCall(name string, args []ast.Expression, env *object.Environment) (object.Object, bool) {
	prim, op, kind, ok := typechecker.ArithmeticParts(name)
	if !ok {
		return nil, false
	}
	if len(args) != 2 {
		return newError("%s takes exactly two arguments", name), true
	}
	bits := uint(typechecker.PrimitiveBits(prim))
	signed := prim[0] == 'i'
	operands := make([]*big.Int, 2)
	for i, arg := range args {
		value := Eval(arg, env)
		if isError(value) {
			return value, true
		}
		integer, isInt := value.(*object.Integer)
		if !isInt {
			return newError("%s requires integer operands, got %s", name, value.Type()), true
		}
		operands[i] = exactValue(integer.Value, bits, signed)
	}
	exact := new(big.Int)
	switch kind {
	case "add":
		exact.Add(operands[0], operands[1])
	case "sub":
		exact.Sub(operands[0], operands[1])
	case "mul":
		exact.Mul(operands[0], operands[1])
	}
	low, high := integerRange(bits, signed)
	inRange := exact.Cmp(low) >= 0 && exact.Cmp(high) <= 0

	if op == "saturating" {
		if exact.Cmp(low) < 0 {
			exact = low
		} else if exact.Cmp(high) > 0 {
			exact = high
		}
		return &object.Integer{Value: storedValue(exact)}, true
	}

	resultADT, hasResult := env.GetADTType("Result")
	overflowADT, hasOverflow := env.GetADTType("Overflow")
	if !hasResult || !hasOverflow || len(resultADT.Variants) < 2 || len(overflowADT.Variants) == 0 {
		return newError("%s requires declared Result[T, E] and Overflow types (docs/spec/20-types.md)", name), true
	}
	if inRange {
		return &object.ADTValue{TypeName: "Result", Variant: resultADT.Variants[0].Name, Value: &object.Integer{Value: storedValue(exact)}}, true
	}
	overflow := &object.ADTValue{TypeName: "Overflow", Variant: overflowADT.Variants[0].Name}
	return &object.ADTValue{TypeName: "Result", Variant: resultADT.Variants[1].Name, Value: overflow}, true
}

// exactValue reads an Integer's stored int64 as the mathematical value of a
// fixed-width type: unsigned values are the low bits as an unsigned number
// (u64 above 2^63 is stored as its two's-complement pattern), signed values
// are already sign-extended.
func exactValue(stored int64, bits uint, signed bool) *big.Int {
	if signed {
		return big.NewInt(signExtend(uint64(stored)&widthMask(bits), bits))
	}
	return new(big.Int).SetUint64(uint64(stored) & widthMask(bits))
}

// integerRange is the inclusive [min, max] of a fixed-width type.
func integerRange(bits uint, signed bool) (*big.Int, *big.Int) {
	if signed {
		high := new(big.Int).Lsh(big.NewInt(1), bits-1)
		low := new(big.Int).Neg(high)
		return low, high.Sub(high, big.NewInt(1))
	}
	high := new(big.Int).Lsh(big.NewInt(1), bits)
	return big.NewInt(0), high.Sub(high, big.NewInt(1))
}

// storedValue folds an in-range mathematical value back into the Integer's
// int64 storage (u64 values above 2^63 become their bit pattern).
func storedValue(value *big.Int) int64 {
	if value.IsInt64() {
		return value.Int64()
	}
	return int64(value.Uint64())
}
