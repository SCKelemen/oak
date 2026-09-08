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
	kind := "view"
	if info.kind == containerSpan {
		kind = "span"
	} else if info.kind != containerView {
		return false
	}
	ctype := fmt.Sprintf("oak_%s_%s", kind, info.element)
	name := fmt.Sprintf("oak_%s_slice_%s", kind, info.element)
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
