package evaluator

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/semir"
)

func isAtomicTypeExpression(expr ast.Expression) bool {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index == nil {
		return false
	}
	base, ok := index.Left.(*ast.Identifier)
	if !ok || base.Value != "Atomic" {
		return false
	}
	carrier, ok := index.Index.(*ast.Identifier)
	return ok && semir.AtomicCarrierAllowed(carrier.Value)
}

func evalAtomicInteger(name string, expr ast.Expression, env *object.Environment) (*object.Integer, object.Object) {
	value := Eval(expr, env)
	if isError(value) {
		return nil, value
	}
	integer, ok := value.(*object.Integer)
	if !ok {
		return nil, newError("%s value must be an integer", name)
	}
	return integer, nil
}

// evalAtomicInvocation evaluates Oak's atomic value semantics. Go's sync/atomic
// implementation is stronger than several Oak order variants, so this is a
// reference for storage identity and sequential return values, not the
// weak-memory oracle. Native generated-code tests validate C11 order lowering.
func evalAtomicInvocation(name string, args []ast.Expression, env *object.Environment) (object.Object, bool) {
	spec, recognized := semir.LookupAtomicBuiltin(name)
	if !recognized {
		return nil, false
	}
	if len(args) != int(spec.Arity) {
		return newError("%s expects %d arguments, got %d", name, spec.Arity, len(args)), true
	}
	if spec.Kind == semir.AtomicBuiltinFence {
		return NULL, true
	}
	// The cell argument is a storage path: a named cell, a record field,
	// or an element of an atomic array. Evaluating the path yields the
	// shared AtomicCell object (records/arrays hold cell references, so
	// path access is identity, never a copy).
	var stored object.Object
	if ident, isIdent := args[0].(*ast.Identifier); isIdent {
		bound, found := env.Get(ident.Value)
		if !found {
			return newError("atomic cell not found: %s", ident.Value), true
		}
		stored = bound
	} else {
		stored = Eval(args[0], env)
		if isError(stored) {
			return stored, true
		}
	}
	cell, ok := stored.(*object.AtomicCell)
	if !ok || cell == nil {
		return newError("%s first argument must be an Atomic[T] cell (storage path)", name), true
	}

	switch spec.Kind {
	case semir.AtomicBuiltinLoad:
		return &object.Integer{Value: cell.Value.Load()}, true

	case semir.AtomicBuiltinStore, semir.AtomicBuiltinFetchAdd, semir.AtomicBuiltinExchange:
		integer, errObj := evalAtomicInteger(name, args[1], env)
		if errObj != nil {
			return errObj, true
		}
		if spec.Kind == semir.AtomicBuiltinStore {
			cell.Value.Store(integer.Value)
			return NULL, true
		}
		if spec.Kind == semir.AtomicBuiltinExchange {
			return &object.Integer{Value: cell.Value.Swap(integer.Value)}, true
		}
		return &object.Integer{Value: cell.Value.Add(integer.Value) - integer.Value}, true

	case semir.AtomicBuiltinCompareExchange:
		expected, errObj := evalAtomicInteger(name+" expected", args[1], env)
		if errObj != nil {
			return errObj, true
		}
		desired, errObj := evalAtomicInteger(name+" desired", args[2], env)
		if errObj != nil {
			return errObj, true
		}

		// Strong CAS: success is observed == expected. On failure the Oak
		// result is the observed cell value, mirroring C11's updated expected.
		// The evaluator is exercised sequentially; concurrent weak-memory
		// behavior belongs to generated C/ISA tests rather than Go's model.
		observed := cell.Value.Load()
		if observed != expected.Value {
			return &object.Integer{Value: observed}, true
		}
		if cell.Value.CompareAndSwap(expected.Value, desired.Value) {
			return &object.Integer{Value: expected.Value}, true
		}
		return &object.Integer{Value: cell.Value.Load()}, true

	default:
		return newError("unsupported atomic builtin: %s", name), true
	}
}

// zeroAtomicStorage constructs the zero value for atomic-bearing storage
// declarations: records whose fields include cells, and owned arrays of
// cells. Non-atomic declarations report false and take the ordinary path.
func zeroAtomicStorage(typeExpr ast.Expression, env *object.Environment) (object.Object, bool) {
	switch t := typeExpr.(type) {
	case *ast.IndexExpression:
		length, isFixed := t.Index.(*ast.IntegerLiteral)
		if !isFixed {
			return nil, false
		}
		if !isAtomicTypeExpression(t.Left) {
			// Arrays of atomic-bearing records also qualify.
			if elem, isStorage := zeroAtomicStorage(t.Left, env); isStorage {
				elements := make([]object.Object, length.Value)
				elements[0] = elem
				for i := int64(1); i < length.Value; i++ {
					fresh, _ := zeroAtomicStorage(t.Left, env)
					elements[i] = fresh
				}
				return &object.Array{Elements: elements}, true
			}
			return nil, false
		}
		elements := make([]object.Object, length.Value)
		for i := range elements {
			elements[i] = &object.AtomicCell{}
		}
		return &object.Array{Elements: elements}, true
	case *ast.Identifier:
		recordDecl, isRecord := env.GetRecordDecl(t.Value)
		if !isRecord {
			return nil, false
		}
		hasAtomic := false
		fields := make(map[string]object.Object, len(recordDecl.FieldOrder))
		for _, field := range recordDecl.FieldOrder {
			if isAtomicTypeExpression(field.Value) {
				fields[field.Name] = &object.AtomicCell{}
				hasAtomic = true
				continue
			}
			if nested, isStorage := zeroAtomicStorage(field.Value, env); isStorage {
				fields[field.Name] = nested
				hasAtomic = true
				continue
			}
			fields[field.Name] = &object.Integer{Value: 0}
		}
		if !hasAtomic {
			return nil, false
		}
		return &object.Record{Fields: fields}, true
	}
	return nil, false
}
