package evaluator

// Interpreter semantics for the 128-bit unsigned integer type
// (docs/spec/20-types.md section 11): every operator computes the exact
// result and folds it into the width, so the interpreter and the C
// helpers (oak_add_u128 and friends) agree at every boundary. Values are
// object.U128; an untyped literal beside one is read as its unsigned
// pattern, which is what the checker admitted it as.

import (
	"math/big"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

func primitiveBitsOf(name string) int { return typechecker.PrimitiveBits(name) }

// asU128 reads an operand of the u128 type: a U128 value, or an Integer
// the checker typed as u128 (a literal, or a u64 pattern widened by the
// constructor), whose stored bits are the low half.
func asU128(obj object.Object) (*object.U128, bool) {
	switch v := obj.(type) {
	case *object.U128:
		return v, true
	case *object.Integer:
		return &object.U128{Lo: uint64(v.Value)}, true
	}
	return nil, false
}

// evalU128Infix is the operator table over two u128 operands.
func evalU128Infix(operator string, left, right *object.U128) object.Object {
	a, b := left.Big(), right.Big()
	switch operator {
	case "+":
		return object.U128FromBig(new(big.Int).Add(a, b))
	case "-":
		return object.U128FromBig(new(big.Int).Sub(a, b))
	case "*":
		return object.U128FromBig(new(big.Int).Mul(a, b))
	case "/":
		if right.IsZero() {
			return newError("division by zero")
		}
		return object.U128FromBig(new(big.Int).Quo(a, b))
	case "%":
		if right.IsZero() {
			return newError("modulo by zero")
		}
		return object.U128FromBig(new(big.Int).Rem(a, b))
	case "&":
		return &object.U128{Hi: left.Hi & right.Hi, Lo: left.Lo & right.Lo}
	case "|":
		return &object.U128{Hi: left.Hi | right.Hi, Lo: left.Lo | right.Lo}
	case "^":
		return &object.U128{Hi: left.Hi ^ right.Hi, Lo: left.Lo ^ right.Lo}
	case "<<", ">>":
		// A count reaching the width traps in the compiled program
		// (oak_shl_u128); here it is the interpreter's error.
		if right.Hi != 0 || right.Lo >= 128 {
			return newError("shift count out of range: %s", right.Inspect())
		}
		if operator == "<<" {
			return object.U128FromBig(new(big.Int).Lsh(a, uint(right.Lo)))
		}
		return object.U128FromBig(new(big.Int).Rsh(a, uint(right.Lo)))
	case "<":
		return nativeBoolToBooleanObject(left.Less(right))
	case ">":
		return nativeBoolToBooleanObject(right.Less(left))
	case "<=":
		return nativeBoolToBooleanObject(!right.Less(left))
	case ">=":
		return nativeBoolToBooleanObject(!left.Less(right))
	case "==":
		return nativeBoolToBooleanObject(left.Equal(right))
	case "!=":
		return nativeBoolToBooleanObject(!left.Equal(right))
	}
	return newError("unknown operator: %s %s %s", left.Type(), operator, right.Type())
}

// evalU128Narrowing is {u8..u64}_{trunc|saturating}_u128 (docs/spec/20-types.md
// section 11.1): the low bits, or the target's maximum when the value is
// above it.
func evalU128Narrowing(name, target, op string, value *object.U128) object.Object {
	bits := uint(primitiveBitsOf(target))
	if bits == 0 || bits > 64 {
		return newError("%s: %s is not a narrower unsigned type", name, target)
	}
	mask := widthMask(bits)
	switch op {
	case "trunc":
		return &object.Integer{Value: int64(value.Lo & mask)}
	case "saturating":
		if value.Hi != 0 || value.Lo > mask {
			return &object.Integer{Value: int64(mask)}
		}
		return &object.Integer{Value: int64(value.Lo)}
	}
	return newError("unknown conversion %s", name)
}

// u128InRange reports whether a u128 value fits the unsigned target width,
// for the checked conversion.
func u128InRange(value *object.U128, targetBits uint) bool {
	return value.Hi == 0 && value.Lo <= widthMask(targetBits)
}
