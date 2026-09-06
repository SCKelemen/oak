package evaluator

// Interpreter semantics for the compiler-known foreign-interface libraries
// (docs/spec/92-ffi.md section 4): every arm64 instruction function runs
// natively so interpreted and compiled programs agree; c conversions are
// value-preserving (nominal typing is enforced statically); extern bindings
// cannot be called, because the interpreter has no foreign world.

import (
	"math/bits"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

func evalLibraryCall(library, member string, args []ast.Expression, env *object.Environment) object.Object {
	switch library {
	case "arm64":
		return evalArm64Intrinsic(member, args, env)
	case "c":
		if member == "extern" {
			return newError("extern bindings require the native backend; the interpreter cannot call foreign code")
		}
		// A c.* conversion preserves the abstract value (Oak.CInterop);
		// the nominal boundary typing is enforced by the type checker.
		if len(args) != 1 {
			return newError("c.%s takes exactly one argument", member)
		}
		return Eval(args[0], env)
	}
	return newError("unknown library: %s", library)
}

// evalArm64Intrinsic implements the v1 catalog of docs/spec/92-ffi.md
// section 3.2 with the same total semantics as the Lean model
// (Oak.Intrinsics) and the C lowerings.
func evalArm64Intrinsic(member string, args []ast.Expression, env *object.Environment) object.Object {
	if len(args) != 1 {
		return newError("arm64.%s takes exactly one argument", member)
	}
	operandObject := Eval(args[0], env)
	if isError(operandObject) {
		return operandObject
	}
	operand, ok := operandObject.(*object.Integer)
	if !ok {
		return newError("arm64.%s requires an integer operand, got %s", member, operandObject.Type())
	}
	switch member {
	case "rev32":
		return &object.Integer{Value: int64(bits.ReverseBytes32(uint32(operand.Value)))}
	case "rev64":
		return &object.Integer{Value: int64(bits.ReverseBytes64(uint64(operand.Value)))}
	case "rbit32":
		return &object.Integer{Value: int64(bits.Reverse32(uint32(operand.Value)))}
	case "rbit64":
		return &object.Integer{Value: int64(bits.Reverse64(uint64(operand.Value)))}
	case "clz32":
		// Total: clz32(0) = 32, the ARM CLZ semantics (Oak.Intrinsics).
		return &object.Integer{Value: int64(bits.LeadingZeros32(uint32(operand.Value)))}
	case "clz64":
		// Total: clz64(0) = 64.
		return &object.Integer{Value: int64(bits.LeadingZeros64(uint64(operand.Value)))}
	}
	return newError("the arm64 library has no instruction function arm64.%s", member)
}
