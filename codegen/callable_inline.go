package codegen

import (
	"reflect"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// functionValueUses distinguishes direct calls from use of a function's
// address as an ordinary value. An always_inline promise is invalid for an
// indirect call whose target the host C optimizer cannot determine.
// This only controls the C attribute; direct Oak source inlining remains
// available and ordinary C optimization may still inline known targets.
func functionValueUses(program *ast.Program) map[string]bool {
	used := make(map[string]bool)
	var walk func(reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Pointer, reflect.Interface:
			if v.IsNil() {
				return
			}
			switch node := v.Interface().(type) {
			case *ast.Identifier:
				used[node.Value] = true
				return
			case *ast.FunctionStatement:
				walk(reflect.ValueOf(node.Body))
				return
			case *ast.FunctionLiteral:
				walk(reflect.ValueOf(node.Body))
				return
			case *ast.VariableDeclaration:
				walk(reflect.ValueOf(node.Value))
				return
			case *ast.ADTType:
				return // type fields do not evaluate function addresses
			case *ast.InvocationExpression:
				if _, direct := node.Function.(*ast.Identifier); !direct {
					walk(reflect.ValueOf(node.Function))
				}
				for _, arg := range node.Arguments {
					walk(reflect.ValueOf(arg))
				}
				return
			}
			walk(v.Elem())
		case reflect.Struct:
			if v.Type() == reflect.TypeOf(token.Token{}) {
				return
			}
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice, reflect.Array:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
			}
		case reflect.Map:
			for _, key := range v.MapKeys() {
				walk(v.MapIndex(key))
			}
		}
	}
	walk(reflect.ValueOf(program))
	return used
}
