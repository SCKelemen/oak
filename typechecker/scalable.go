package typechecker

import (
	"reflect"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// checkScalableLocality enforces docs/spec/93-simd.md section 4 item 7:
// scalable vectors and active extents are block-local values. They may
// not be a record field, a global, a parameter or result of any function,
// or an array element, because a backend may hold them in sizeless
// hardware registers whose width is not a type property. One diagnostic,
// OAK-S0401.
func (tc *TypeChecker) checkScalableLocality(program *ast.Program) {
	scalable := func(expr ast.Expression) bool {
		if expr == nil {
			return false
		}
		text := expr.String()
		return strings.Contains(text, "simd.Active") || strings.Contains(text, "simd.Scalable")
	}
	report := func(node ast.Node, what string) {
		tc.addError(node, "OAK-S0401: %s: scalable vectors and active extents are block-local (docs/spec/93-simd.md section 4); bind them in locals and pass their elements through views and spans", what)
	}
	for _, stmt := range program.Statements {
		if decl, isVar := stmt.(*ast.VariableDeclaration); isVar && decl.Type != nil && scalable(decl.Type) {
			report(decl, "global "+decl.Name.Value)
		}
	}
	var visit func(value reflect.Value)
	visit = func(value reflect.Value) {
		if !value.IsValid() {
			return
		}
		switch value.Kind() {
		case reflect.Ptr, reflect.Interface:
			if value.IsNil() {
				return
			}
			switch node := value.Interface().(type) {
			case *ast.FunctionStatement:
				for _, param := range node.Parameters {
					if param != nil && param.Name != nil && scalable(param.Type) {
						report(param.Name, "parameter "+param.Name.Value)
					}
				}
				if scalable(node.ReturnType) {
					report(node, "the result of "+node.Name.Value)
				}
			case *ast.ADTType:
				if node.Name != nil && (strings.Contains(node.String(), "simd.Active") || strings.Contains(node.String(), "simd.Scalable")) {
					report(node, "a field of "+node.Name.Value)
				}
			case *ast.VariableDeclaration:
				if index, isIndex := node.Type.(*ast.IndexExpression); isIndex && scalable(index.Left) {
					report(node, "an array of scalable vectors ("+node.Name.Value+")")
				}
			}
			if value.Kind() == reflect.Ptr {
				visit(value.Elem())
			} else {
				visit(reflect.ValueOf(value.Interface()))
			}
		case reflect.Struct:
			for i := 0; i < value.NumField(); i++ {
				if value.Type().Field(i).IsExported() {
					visit(value.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < value.Len(); i++ {
				visit(value.Index(i))
			}
		}
	}
	visit(reflect.ValueOf(program))
}
