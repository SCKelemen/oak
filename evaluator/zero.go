package evaluator

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// zeroValue is the interpreter's zero for a value-less typed declaration
// (`regs: [4]u64`), mirroring the backend's zero-initialized storage: fixed
// integers are 0, Bool is false, owned arrays are N zero elements, declared
// records zero every field. Unknown shapes report no value (the caller
// keeps the declaration unbound rather than inventing one).
func zeroValue(typeExpr ast.Expression, env *object.Environment) (object.Object, bool) {
	switch t := typeExpr.(type) {
	case *ast.Identifier:
		switch t.Value {
		case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "int", "uint", "byte", "rune":
			return &object.Integer{Value: 0}, true
		case "Bool":
			return FALSE, true
		}
		if decl, ok := env.GetRecordDecl(t.Value); ok {
			record := &object.Record{Fields: map[string]object.Object{}}
			for _, field := range decl.FieldOrder {
				value, known := zeroValue(field.Value, env)
				if !known {
					return nil, false
				}
				record.Fields[field.Name] = value
			}
			return record, true
		}
	case *ast.IndexExpression:
		length, isFixed := t.Index.(*ast.IntegerLiteral)
		if !isFixed || length.Value < 0 {
			return nil, false
		}
		elements := make([]object.Object, length.Value)
		for i := range elements {
			element, known := zeroValue(t.Left, env)
			if !known {
				return nil, false
			}
			elements[i] = element
		}
		return &object.Array{Elements: elements}, true
	}
	return nil, false
}
