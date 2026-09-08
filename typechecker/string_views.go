package typechecker

import "github.com/SCKelemen/oak/ast"

func (tc *TypeChecker) checkStringViewBuiltin(name string, call *ast.InvocationExpression) Type {
	var result Type = &StringType{}
	if name == "str_bytes" {
		result = &ArrayType{IsSlice: true, Length: -1, ElementType: &PrimitiveType{Name: "u8"}}
	}
	if len(call.Arguments) != 1 {
		tc.addError(call, "%s expects exactly one argument", name)
		return result
	}
	input := tc.checkExpression(call.Arguments[0])
	if input == nil {
		return result
	}
	valid := false
	if name == "str_from_utf8" {
		if view, ok := input.(*ArrayType); ok && view.IsSlice {
			if unit, ok := view.ElementType.(*PrimitiveType); ok {
				valid = normalizePrimitiveName(unit.Name) == "u8"
			}
		}
		if !valid {
			tc.addError(call.Arguments[0], "str_from_utf8 requires a read-only []u8 view, got %s", input)
		}
	} else {
		if text, ok := input.(*StringType); ok {
			valid = text.encoding() == "Utf8"
		}
		if !valid {
			tc.addError(call.Arguments[0], "str_bytes requires string or Str[Utf8], got %s", input)
		}
	}
	return result
}
