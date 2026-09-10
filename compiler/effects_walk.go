package compiler

import (
	"reflect"

	"github.com/SCKelemen/oak/ast"
)

var astNodeType = reflect.TypeOf((*ast.Node)(nil)).Elem()

// walkSyntaxNodes visits every ast.Node reachable from root through exported
// fields, slices, and maps, calling visit on each before descending.
func walkSyntaxNodes(root ast.Node, visit func(ast.Node)) {
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			if v.Type().Implements(astNodeType) {
				if node, ok := v.Interface().(ast.Node); ok && node != nil {
					visit(node)
				}
			}
			walk(v.Elem())
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
			}
		case reflect.Map:
			iter := v.MapRange()
			for iter.Next() {
				walk(iter.Value())
			}
		}
	}
	walk(reflect.ValueOf(root))
}
