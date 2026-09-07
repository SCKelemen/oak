package compiler

// Reflective syntax-tree utilities shared by the standard-library loader
// (token stamping) — generic-function specialization itself lives in the
// type checker (typechecker/genericfn.go), the single resolution authority.

import (
	"reflect"

	"github.com/SCKelemen/oak/ast"
)

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
