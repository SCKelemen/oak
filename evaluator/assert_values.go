package evaluator

import "github.com/SCKelemen/oak/object"

// evalAssertValues implements assert_eq (wantEqual) and assert_ne over the
// interpreter's scalar objects: integers, Booleans, and floats compare by
// value (a NaN is never equal, as in the compiled helper), and a failure
// names both values in the same words the C runtime prints
// (docs/spec/85-discipline.md section 5).
func evalAssertValues(name string, wantEqual bool, args []object.Object) object.Object {
	if len(args) != 2 {
		return newError("%s expects exactly two arguments: got and want, got %d", name, len(args))
	}
	got, want := args[0], args[1]
	var equal bool
	switch g := got.(type) {
	case *object.Integer:
		w, ok := want.(*object.Integer)
		if !ok {
			return newError("%s operands must have one type, got %s and %s", name, got.Type(), want.Type())
		}
		equal = g.Value == w.Value
	case *object.U128:
		w, ok := want.(*object.U128)
		if !ok {
			return newError("%s operands must have one type, got %s and %s", name, got.Type(), want.Type())
		}
		equal = g.Equal(w)
	case *object.Boolean:
		w, ok := want.(*object.Boolean)
		if !ok {
			return newError("%s operands must have one type, got %s and %s", name, got.Type(), want.Type())
		}
		equal = g.Value == w.Value
	case *object.Float:
		w, ok := want.(*object.Float)
		if !ok {
			return newError("%s operands must have one type, got %s and %s", name, got.Type(), want.Type())
		}
		equal = g.Value == w.Value
	default:
		return newError("%s compares fixed-width integers, f32/f64, or Bool, got %s", name, got.Type())
	}
	if wantEqual && !equal {
		return newError("assertion failed: got %s, want %s", got.Inspect(), want.Inspect())
	}
	if !wantEqual && equal {
		return newError("assertion failed: got %s, want anything but %s", got.Inspect(), want.Inspect())
	}
	return NULL
}
