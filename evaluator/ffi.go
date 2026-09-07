package evaluator

// Interpreter semantics for the compiler-known foreign-interface libraries.
// Portable arm64 value-transforming instruction functions execute natively in
// the interpreter. Architectural barriers, MMIO, system registers, event
// control, and non-returning control transfers do not: their machine semantics
// cannot be faithfully represented by the sequential host evaluator, so
// execution fails explicitly rather than inventing state or control flow.

import (
	"math/bits"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/semir"
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
		if len(args) != 1 {
			return newError("c.%s takes exactly one argument", member)
		}
		return Eval(args[0], env)
	}
	return newError("unknown library: %s", library)
}

func evalArm64Intrinsic(member string, args []ast.Expression, env *object.Environment) object.Object {
	if _, controlTransfer := semir.LookupArm64ControlTransfer(member); controlTransfer {
		if len(args) != 0 {
			return newError("arm64.%s takes exactly zero arguments", member)
		}
		return newError("arm64.%s is a non-returning control-transfer machine operation and requires the native AArch64 backend", member)
	}
	if _, eventControl := semir.LookupArm64EventControl(member); eventControl {
		if len(args) != 0 {
			return newError("arm64.%s takes exactly zero arguments", member)
		}
		return newError("arm64.%s is an event-control machine operation and requires the native AArch64 backend", member)
	}
	if _, sysreg, write := semir.LookupArm64SysRegMember(member); sysreg {
		want := 0
		if write {
			want = 1
		}
		if len(args) != want {
			return newError("arm64.%s takes exactly %d argument(s)", member, want)
		}
		return newError("arm64.%s is a system-register machine operation and requires the native AArch64 backend", member)
	}
	if spec, mmio := semir.LookupArm64Mmio(member); mmio {
		if len(args) != int(spec.Arity) {
			return newError("arm64.%s takes exactly %d argument(s)", member, spec.Arity)
		}
		return newError("arm64.%s is an MMIO machine operation and requires the native AArch64 backend", member)
	}
	if _, barrier := semir.LookupArm64Barrier(member); barrier {
		if len(args) != 0 {
			return newError("arm64.%s takes exactly zero arguments", member)
		}
		return newError("arm64.%s is an architectural barrier and requires the native AArch64 backend", member)
	}
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
		return &object.Integer{Value: int64(bits.LeadingZeros32(uint32(operand.Value)))}
	case "clz64":
		return &object.Integer{Value: int64(bits.LeadingZeros64(uint64(operand.Value)))}
	}
	return newError("the arm64 library has no instruction function arm64.%s", member)
}

var arm64VectorMembers = map[string]bool{
	"uaddlv_u8x16": true, "umaxv_u8x16": true, "uminv_u8x16": true, "cnt_u8x16": true,
}

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
		return &object.Integer{Value: max}
	case "uminv_u8x16":
		min := byte(255)
		for _, lane := range vec.Bytes {
			if lane < min {
				min = lane
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
