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
	case "simd":
		return evalSimdOp(member, args, env)
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
	if arm64VectorMembers[member] {
		return evalArm64VectorIntrinsic(member, args, env)
	}
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

// arm64VectorMembers are the horizontal vector instruction functions
// (docs/spec/93-simd.md section 2).
var arm64VectorMembers = map[string]bool{
	"uaddlv_u8x16": true, "umaxv_u8x16": true, "uminv_u8x16": true, "cnt_u8x16": true,
}

// evalArm64VectorIntrinsic implements the horizontal vector instructions of
// docs/spec/93-simd.md section 2 with the same total semantics as the NEON
// and portable C lowerings.
func evalArm64VectorIntrinsic(member string, args []ast.Expression, env *object.Environment) object.Object {
	if len(args) != 1 {
		return newError("arm64.%s takes exactly one argument", member)
	}
	operandObject := Eval(args[0], env)
	if isError(operandObject) {
		return operandObject
	}
	vec, ok := operandObject.(*object.Vector)
	if !ok || vec.VectorKind != "U8x16" {
		return newError("arm64.%s requires a simd.U8x16 operand, got %s", member, operandObject.Type())
	}
	switch member {
	case "uaddlv_u8x16":
		sum := int64(0)
		for _, lane := range vec.Bytes {
			sum += int64(lane)
		}
		return &object.Integer{Value: sum}
	case "umaxv_u8x16":
		max := byte(0)
		for _, lane := range vec.Bytes {
			if lane > max {
				max = lane
			}
		}
		return &object.Integer{Value: int64(max)}
	case "uminv_u8x16":
		min := byte(255)
		for _, lane := range vec.Bytes {
			if lane < min {
				min = lane
			}
		}
		return &object.Integer{Value: int64(min)}
	case "cnt_u8x16":
		result := &object.Vector{VectorKind: "U8x16"}
		for i, lane := range vec.Bytes {
			result.Bytes[i] = byte(bits.OnesCount8(lane))
		}
		return result
	}
	return newError("the arm64 library has no instruction function arm64.%s", member)
}
