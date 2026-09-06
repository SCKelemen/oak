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

// evalAtomicInvocation evaluates the value semantics of Oak atomics. Go's
// sync/atomic implementation is at least as strong as every Oak order exposed
// here; the evaluator is therefore a reference for cell identity and returned
// values, not a weak-memory litmus-test engine.
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
	ident, ok := args[0].(*ast.Identifier)
	if !ok {
		return newError("%s requires a named Atomic[T] cell", name), true
	}
	stored, ok := env.Get(ident.Value)
	if !ok {
		return newError("atomic cell not found: %s", ident.Value), true
	}
	cell, ok := stored.(*object.AtomicCell)
	if !ok || cell == nil {
		return newError("%s first argument must be an Atomic[T] cell", name), true
	}

	switch spec.Kind {
	case semir.AtomicBuiltinLoad:
		return &object.Integer{Value: cell.Value.Load()}, true
	case semir.AtomicBuiltinStore, semir.AtomicBuiltinFetchAdd:
		value := Eval(args[1], env)
		if isError(value) {
			return value, true
		}
		integer, ok := value.(*object.Integer)
		if !ok {
			return newError("%s value must be an integer", name), true
		}
		if spec.Kind == semir.AtomicBuiltinStore {
			cell.Value.Store(integer.Value)
			return NULL, true
		}
		return &object.Integer{Value: cell.Value.Add(integer.Value) - integer.Value}, true
	default:
		return newError("unsupported atomic builtin: %s", name), true
	}
}
