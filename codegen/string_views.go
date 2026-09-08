package codegen

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// Definitions are inserted with slice helpers after the runtime/types and before
// Oak functions. Function arguments evaluate once; neither bridge copies bytes.
func (cg *CodeGenerator) emitStringViewCall(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	name, ok := call.Function.(*ast.Identifier)
	if !ok || len(call.Arguments) != 1 {
		return false
	}
	switch name.Value {
	case "str_from_utf8":
		cg.sliceHelpers["oak_str_from_utf8"] = `static inline string oak_str_from_utf8(oak_view_u8 value) {
  if (!oak_is_valid_utf8(value)) { __builtin_trap(); }
  /* The legacy string field is u8*, but Oak exposes no mutable string access. */
  string result = { (u8*)value.base, value.len };
  return result;
}

`
	case "str_bytes":
		cg.sliceHelpers["oak_str_bytes"] = `static inline oak_view_u8 oak_str_bytes(string value) {
  oak_view_u8 result = { value.data, value.len };
  return result;
}

`
	default:
		return false
	}
	cg.output.WriteString("oak_" + name.Value + "( ")
	cg.emitExpressionFragment(call.Arguments[0], tc)
	cg.output.WriteString(" )")
	return true
}
