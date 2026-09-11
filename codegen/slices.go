package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// emitBorrowedSlice handles view/span subslicing with one evaluation per operand.
// Helper definitions are inserted after typedefs and before function prototypes.
func (cg *CodeGenerator) emitBorrowedSlice(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	info := cg.localContainerOf(call.Arguments[0])
	if info.kind == containerOwnedArray {
		return cg.emitOwnedArraySlice(call, info, tc)
	}
	kind := "view"
	if info.kind == containerSpan {
		kind = "span"
	} else if info.kind != containerView {
		return false
	}
	ctype := fmt.Sprintf("oak_%s_%s", kind, info.element)
	name := fmt.Sprintf("oak_%s_slice_%s", kind, elementIdent(info.element))
	cg.sliceHelpers[name] = fmt.Sprintf(`static inline %s %s(%s value, u64 low, u64 high) {
  if (low > high || high > (u64)value.len) { __builtin_trap(); }
  %s result = { low == 0 ? value.base : value.base + low, (u32)(high - low) };
  return result;
}

`, ctype, name, ctype, ctype)
	cg.output.WriteString(name + "( ")
	cg.emitExpressionFragment(call.Arguments[0], tc)
	for _, bound := range call.Arguments[1:] {
		cg.output.WriteString(", (u64)( ")
		cg.emitExpressionFragment(bound, tc)
		cg.output.WriteString(" )")
	}
	cg.output.WriteString(" )")
	return true
}

// emitOwnedArraySlice lowers arr[lo:hi] over an owned array to a view over
// the wrapper's storage: a compound literal, so the slice is a value in any
// expression position (an argument, not only a declaration initializer).
// The bounds are checked against the static length before the pointer is
// formed; out of range traps, never a dangling or oversized view.
func (cg *CodeGenerator) emitOwnedArraySlice(call *ast.InvocationExpression, info localContainer, tc *typechecker.TypeChecker) bool {
	if len(call.Arguments) != 3 {
		return false
	}
	// The view typedef must already be placed (a slice flows into a []T
	// position, which the type pre-pass emitted); a body is no place for a
	// typedef, so an unplaced view type fails closed.
	viewType := fmt.Sprintf("oak_view_%s", elementIdent(info.element))
	if !cg.types[viewType] {
		cg.output.WriteString("OAK_UNSUPPORTED_SLICE_VIEW_TYPE")
		return true
	}
	name := "oak_arr_slice_low"
	cg.sliceHelpers[name] = `static inline u64 oak_arr_slice_low(u64 low, u64 high, u64 len) {
  if (low > high || high > len) { __builtin_trap(); }
  return low;
}

`
	cg.output.WriteString(fmt.Sprintf("(%s){ ( ", viewType))
	cg.emitExpressionFragment(call.Arguments[0], tc)
	cg.output.WriteString(fmt.Sprintf(" ).v + %s( (u64)( ", name))
	cg.emitExpressionFragment(call.Arguments[1], tc)
	cg.output.WriteString(" ), (u64)( ")
	cg.emitExpressionFragment(call.Arguments[2], tc)
	cg.output.WriteString(fmt.Sprintf(" ), %d ), (u32)( (u64)( ", info.length))
	cg.emitExpressionFragment(call.Arguments[2], tc)
	cg.output.WriteString(" ) - (u64)( ")
	cg.emitExpressionFragment(call.Arguments[1], tc)
	cg.output.WriteString(" ) ) }")
	return true
}
