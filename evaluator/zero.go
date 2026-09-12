package evaluator

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

// isRecordObject reports a record value.
func isRecordObject(obj object.Object) bool {
	_, ok := obj.(*object.Record)
	return ok
}

// copyValue realizes Oak's value semantics for aggregates: records and
// owned arrays copy on declaration, assignment, and argument passing
// (the backend copies structs and arrays by value); views and spans alias
// by design and atomic cells are storage identities, so both pass through.
func copyValue(obj object.Object) object.Object {
	switch v := obj.(type) {
	case *object.Record:
		fields := make(map[string]object.Object, len(v.Fields))
		for name, value := range v.Fields {
			fields[name] = copyValue(value)
		}
		return &object.Record{Fields: fields, Order: v.Order}
	case *object.Array:
		elements := make([]object.Object, len(v.Elements))
		for i, element := range v.Elements {
			elements[i] = copyValue(element)
		}
		return &object.Array{Elements: elements}
	}
	return obj
}

// flattenApplication decodes Name[A][B] into (Name, [A, B]).
func flattenApplication(expr ast.Expression) (string, []ast.Expression, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e.Value, nil, e.Value != ""
	case *ast.IndexExpression:
		if e.Dot {
			return "", nil, false
		}
		name, args, ok := flattenApplication(e.Left)
		if !ok {
			return "", nil, false
		}
		return name, append(args, e.Index), true
	}
	return "", nil, false
}

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
		case "u128":
			return &object.U128{}, true
		case "f32":
			return &object.Float{Value: 0, Bits: 32}, true
		case "f64":
			return &object.Float{Value: 0, Bits: 64}, true
		case "f16", "bf16":
			return &object.Float{Value: 0, Bits: 16, Format: t.Value}, true
		case "f8e4m3", "f8e5m2":
			return &object.Float{Value: 0, Bits: 8, Format: t.Value}, true
		case "Bool":
			return FALSE, true
		}
		// A refined type's zero is its base's zero (the checker admits the
		// declaration only when the predicate holds at zero).
		if base, ok := env.GetRefinementBase(t.Value); ok {
			return zeroValue(base, env)
		}
		if decl, ok := env.GetRecordDecl(t.Value); ok {
			record := &object.Record{Fields: map[string]object.Object{}}
			for _, field := range decl.FieldOrder {
				record.Order = append(record.Order, field.Name)
				value, known := zeroValue(field.Value, env)
				if !known {
					return nil, false
				}
				record.Fields[field.Name] = value
			}
			return record, true
		}
	case *ast.IndexExpression:
		// A generic record instantiation (Idx[Thread], Ring[u8, 4]) zeroes the
		// template's fields under the argument bindings; the template
		// registry disambiguates it from an owned array [4]Thread, which
		// shares the syntactic shape.
		if name, args, ok := flattenApplication(t); ok {
			if params, decl, isTemplate := env.GetRecordTemplate(name); isTemplate && len(params) == len(args) {
				bindings := make(map[string]ast.Expression, len(params))
				for i, param := range params {
					bindings[param] = args[i]
				}
				record := &object.Record{Fields: map[string]object.Object{}}
				for _, field := range decl.FieldOrder {
					substituted, ok := typechecker.SubstituteTypeAST(field.Value, bindings)
					if !ok {
						return nil, false
					}
					value, known := zeroValue(substituted, env)
					if !known {
						return nil, false
					}
					record.Fields[field.Name] = value
				}
				return record, true
			}
		}
		// A const-arithmetic length ([M*N]T inside a generic body) evaluates
		// under the const parameters bound as integers in the environment.
		var count int64
		if length, isFixed := t.Index.(*ast.IntegerLiteral); isFixed {
			count = length.Value
		} else if evaluated, isInt := Eval(t.Index, env).(*object.Integer); isInt {
			count = evaluated.Value
		} else {
			return nil, false
		}
		if count < 0 {
			return nil, false
		}
		elements := make([]object.Object, count)
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
