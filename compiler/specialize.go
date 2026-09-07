package compiler

import (
	"fmt"
	"reflect"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// specializeFunctions implements explicit, first-order specialization before
// the ordinary type/borrow/discipline gates. Every concrete body is checked by
// those gates. Inferred applications, constraints, methods, const arguments and
// higher-order generic values are deliberately rejected by this first slice.
func specializeFunctions(program *ast.Program) error {
	templates := map[string]*ast.FunctionStatement{}
	names := map[string]bool{}
	types := map[string]bool{}
	for _, name := range []string{"u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "Bool"} {
		types[name] = true
	}
	var ordinary []ast.Statement
	for _, stmt := range program.Statements {
		name := declarationName(stmt)
		if name != "" {
			if names[name] {
				return fmt.Errorf("specialize: duplicate declaration %q", name)
			}
			names[name] = true
		}
		if adt, ok := stmt.(*ast.ADTType); ok && len(adt.TypeParams) == 0 {
			types[adt.Name.Value] = true
		}
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || len(fn.TypeParams) == 0 {
			ordinary = append(ordinary, stmt)
			continue
		}
		if fn.Receiver != nil || fn.ExternSymbol != "" {
			return fmt.Errorf("specialize: generic methods and externs are unsupported")
		}
		constrained := false
		for _, tp := range fn.TypeParams {
			if tp.Constraint != nil {
				constrained = true
			}
		}
		if constrained {
			ordinary = append(ordinary, stmt)
			continue
		}
		params := map[string]bool{}
		for _, tp := range fn.TypeParams {
			if tp.Constraint != nil {
				return fmt.Errorf("specialize: constrained/const parameter %s is not supported", tp.Name.Value)
			}
			if params[tp.Name.Value] {
				return fmt.Errorf("specialize: duplicate type parameter %s", tp.Name.Value)
			}
			params[tp.Name.Value] = true
		}
		// Substitution must not capture a value binder. Oak already forbids
		// shadowing, but templates disappear before concrete type checking.
		if err := inspectBinders(reflect.ValueOf(fn), func(name string) error {
			if params[name] {
				return fmt.Errorf("specialize: value binder %s shadows a type parameter", name)
			}
			return nil
		}); err != nil {
			return err
		}
		templates[name] = fn
	}
	if len(templates) == 0 {
		return nil
	}
	for _, stmt := range program.Statements {
		if err := inspectBinders(reflect.ValueOf(stmt), func(name string) error {
			if templates[name] != nil {
				return fmt.Errorf("specialize: value binder %s shadows a generic function", name)
			}
			return nil
		}); err != nil {
			return err
		}
	}
	generated := []*ast.FunctionStatement{}
	instances := map[string]string{}
	var rewrite func(ast.Expression) (ast.Expression, error)
	rewrite = func(expr ast.Expression) (ast.Expression, error) {
		if call, ok := expr.(*ast.InvocationExpression); ok {
			name, args, ok := genericApplication(call.Function)
			if ok && templates[name] != nil {
				fn := templates[name]
				if len(args) != len(fn.TypeParams) {
					return nil, fmt.Errorf("specialize: %s needs %d explicit type arguments", name, len(fn.TypeParams))
				}
				bindings := map[string]string{}
				parts := []string{name}
				for i, arg := range args {
					id, ok := arg.(*ast.Identifier)
					if !ok || !types[id.Value] {
						return nil, fmt.Errorf("specialize: %s requires concrete scalar or named type arguments", name)
					}
					bindings[fn.TypeParams[i].Name.Value] = id.Value
					parts = append(parts, id.Value)
				}
				key := strings.Join(parts, "/")
				mangled, exists := instances[key]
				if !exists {
					if len(instances) >= 256 {
						return nil, fmt.Errorf("specialize: program exceeds 256 function instantiations")
					}
					mangled = "oak_spec"
					for _, part := range parts {
						mangled += "_" + strconv.Itoa(len(part)) + "_" + part
					}
					if names[mangled] {
						return nil, fmt.Errorf("specialize: generated name %s collides with a declaration", mangled)
					}
					names[mangled] = true
					instances[key] = mangled // Register before visiting recursive calls.
					clone := cloneSyntax(reflect.ValueOf(fn)).Interface().(*ast.FunctionStatement)
					clone.Name.Value = mangled
					clone.TypeParams = nil
					if err := transformSyntax(reflect.ValueOf(clone), func(e ast.Expression) (ast.Expression, error) {
						switch node := e.(type) {
						case *ast.MatchExpression:
							node.Token.SemanticContext = mangled
						case *ast.VariantExpression:
							node.Token.SemanticContext = mangled
						}
						if id, ok := e.(*ast.Identifier); ok {
							if concrete, found := bindings[id.Value]; found {
								replacement := *id
								replacement.Value = concrete
								replacement.Token.Literal = concrete
								return &replacement, nil
							}
						}
						return e, nil
					}); err != nil {
						return nil, err
					}
					generated = append(generated, clone)
					if err := transformSyntax(reflect.ValueOf(clone), rewrite); err != nil {
						return nil, err
					}
				}
				replacement := *call
				replacement.Function = &ast.Identifier{Token: call.Token, Value: mangled}
				return &replacement, nil
			}
		}
		if id, ok := expr.(*ast.Identifier); ok && templates[id.Value] != nil {
			return nil, fmt.Errorf("specialize: %s requires an explicit call such as %s[u32](...); generic function values are unsupported", id.Value, id.Value)
		}
		return expr, nil
	}
	for _, stmt := range ordinary {
		if err := transformSyntax(reflect.ValueOf(stmt), rewrite); err != nil {
			return err
		}
	}
	// Concrete signatures are predeclared by the checker; C prototypes retain
	// order-independent direct calls.
	program.Statements = ordinary
	for _, fn := range generated {
		program.Statements = append(program.Statements, fn)
	}
	return nil
}

func genericApplication(expr ast.Expression) (string, []ast.Expression, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e.Value, nil, true
	case *ast.IndexExpression:
		if e.Dot {
			return "", nil, false
		}
		name, args, ok := genericApplication(e.Left)
		return name, append(args, e.Index), ok
	}
	return "", nil, false
}

// ASTs are trees of exported syntax data. Clone interface/map/slice members too:
// separate instantiations must never mutate a shared template or each other.
func cloneSyntax(v reflect.Value) reflect.Value {
	switch v.Kind() {
	case reflect.Interface:
		if v.IsNil() {
			return reflect.Zero(v.Type())
		}
		out := reflect.New(v.Type()).Elem()
		out.Set(cloneSyntax(v.Elem()))
		return out
	case reflect.Pointer:
		if v.IsNil() {
			return reflect.Zero(v.Type())
		}
		out := reflect.New(v.Type().Elem())
		out.Elem().Set(cloneSyntax(v.Elem()))
		return out
	case reflect.Struct:
		out := reflect.New(v.Type()).Elem()
		out.Set(v)
		for i := 0; i < v.NumField(); i++ {
			if out.Field(i).CanSet() && v.Type().Field(i).IsExported() {
				out.Field(i).Set(cloneSyntax(v.Field(i)))
			}
		}
		return out
	case reflect.Slice:
		if v.IsNil() {
			return reflect.Zero(v.Type())
		}
		out := reflect.MakeSlice(v.Type(), v.Len(), v.Len())
		for i := 0; i < v.Len(); i++ {
			out.Index(i).Set(cloneSyntax(v.Index(i)))
		}
		return out
	case reflect.Map:
		if v.IsNil() {
			return reflect.Zero(v.Type())
		}
		out := reflect.MakeMapWithSize(v.Type(), v.Len())
		iter := v.MapRange()
		for iter.Next() {
			out.SetMapIndex(iter.Key(), cloneSyntax(iter.Value()))
		}
		return out
	}
	return v
}

// Visit expression slots before their children. Member names after '.' are
// labels, not variable/type references. Map order is sorted for determinism.
func transformSyntax(v reflect.Value, visit func(ast.Expression) (ast.Expression, error)) error {
	if !v.IsValid() {
		return nil
	}
	if v.Kind() == reflect.Interface {
		if v.IsNil() {
			return nil
		}
		if e, ok := v.Interface().(ast.Expression); ok {
			replacement, err := visit(e)
			if err != nil {
				return err
			}
			v.Set(reflect.ValueOf(replacement))
		}
		return transformSyntax(v.Elem(), visit)
	}
	if v.Kind() == reflect.Pointer {
		if v.IsNil() {
			return nil
		}
		if index, ok := v.Interface().(*ast.IndexExpression); ok && index.Dot {
			return transformSyntax(reflect.ValueOf(&index.Left).Elem(), visit)
		}
		return transformSyntax(v.Elem(), visit)
	}
	switch v.Kind() {
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			if v.Type().Field(i).IsExported() {
				if err := transformSyntax(v.Field(i), visit); err != nil {
					return err
				}
			}
		}
	case reflect.Slice:
		for i := 0; i < v.Len(); i++ {
			if err := transformSyntax(v.Index(i), visit); err != nil {
				return err
			}
		}
	case reflect.Map:
		// AST expression maps have string keys. Sorting avoids randomized discovery
		// order changing specialization order and generated output.
		keys := v.MapKeys()
		for i := 1; i < len(keys); i++ {
			for j := i; j > 0 && keys[j].String() < keys[j-1].String(); j-- {
				keys[j], keys[j-1] = keys[j-1], keys[j]
			}
		}
		for _, key := range keys {
			value := reflect.New(v.Type().Elem()).Elem()
			value.Set(v.MapIndex(key))
			if err := transformSyntax(value, visit); err != nil {
				return err
			}
			v.SetMapIndex(key, value)
		}
	}
	return nil
}

func inspectBinders(v reflect.Value, check func(string) error) error {
	if !v.IsValid() {
		return nil
	}
	if v.Kind() == reflect.Interface || v.Kind() == reflect.Pointer {
		if v.IsNil() {
			return nil
		}
		if v.CanInterface() {
			switch n := v.Interface().(type) {
			case *ast.VariableDeclaration:
				if n.Name != nil {
					if err := check(n.Name.Value); err != nil {
						return err
					}
				}
			case *ast.FunctionParameter:
				if n.Name != nil {
					if err := check(n.Name.Value); err != nil {
						return err
					}
				}
			case *ast.BindingPattern:
				if n.Name != nil {
					if err := check(n.Name.Value); err != nil {
						return err
					}
				}
			}
		}
		return inspectBinders(v.Elem(), check)
	}
	if v.Kind() == reflect.Struct {
		for i := 0; i < v.NumField(); i++ {
			if v.Type().Field(i).IsExported() {
				if err := inspectBinders(v.Field(i), check); err != nil {
					return err
				}
			}
		}
	}
	if v.Kind() == reflect.Slice {
		for i := 0; i < v.Len(); i++ {
			if err := inspectBinders(v.Index(i), check); err != nil {
				return err
			}
		}
	}
	return nil
}
