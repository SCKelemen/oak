package evaluator

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// evalBorrowInvocation realizes view(&owner), span(&owner), and
// subslice(v, start, n) over the interpreter's arrays
// (docs/spec/50-borrowing.md). subslice admits start <= len and
// n <= len - start — compared without adding, exactly the backend helper —
// and derives a window of the same mutability class over the same storage.
func evalBorrowInvocation(name string, args []ast.Expression, env *object.Environment) (object.Object, bool) {
	switch name {
	case "view", "span":
		if len(args) != 1 {
			return newError("%s expects one owned array", name), true
		}
		operand := args[0]
		if prefix, isPrefix := operand.(*ast.PrefixExpression); isPrefix && prefix.Operator == "&" {
			operand = prefix.Right
		}
		owner := Eval(operand, env)
		if isError(owner) {
			return owner, true
		}
		array, isArray := owner.(*object.Array)
		if !isArray {
			return newError("%s requires an owned array, got %s", name, owner.Type()), true
		}
		return &object.View{Array: array, Start: 0, Len: len(array.Elements), Writable: name == "span"}, true
	case "view_as":
		// The scalar view of a view of records (docs/spec/50-borrowing.md
		// section 8d): the fields of every record in declaration order,
		// fixed-array fields spliced. The owner cannot be written while the
		// view lives, so a copy is the same view.
		if len(args) != 1 {
			return newError("view_as expects one view of records"), true
		}
		source := Eval(args[0], env)
		if isError(source) {
			return source, true
		}
		view, isView := source.(*object.View)
		if !isView {
			return newError("view_as requires a view, got %s", source.Type()), true
		}
		flat := &object.Array{}
		for i := 0; i < view.Len; i++ {
			record, isRecord := view.Array.Elements[view.Start+i].(*object.Record)
			if !isRecord {
				return newError("view_as requires a view of records, got %s", view.Array.Elements[view.Start+i].Type()), true
			}
			for _, name := range record.Order {
				switch field := record.Fields[name].(type) {
				case *object.Array:
					flat.Elements = append(flat.Elements, field.Elements...)
				default:
					flat.Elements = append(flat.Elements, field)
				}
			}
		}
		return &object.View{Array: flat, Start: 0, Len: len(flat.Elements), Writable: false}, true
	case "span_as":
		return newError("span_as requires the native backend; the interpreter cannot alias a record's storage as scalars"), true
	case "subslice":
		if len(args) != 3 {
			return newError("subslice expects (view, start, len)"), true
		}
		source := Eval(args[0], env)
		if isError(source) {
			return source, true
		}
		view, isView := source.(*object.View)
		if !isView {
			return newError("subslice requires a view or span, got %s", source.Type()), true
		}
		startObj := Eval(args[1], env)
		if isError(startObj) {
			return startObj, true
		}
		countObj := Eval(args[2], env)
		if isError(countObj) {
			return countObj, true
		}
		start, okS := startObj.(*object.Integer)
		count, okN := countObj.(*object.Integer)
		if !okS || !okN || start.Value < 0 || count.Value < 0 {
			return newError("subslice bounds must be non-negative integers"), true
		}
		if start.Value > int64(view.Len) || count.Value > int64(view.Len)-start.Value {
			return newError("subslice out of range: start %d, len %d over a %d-element %s", start.Value, count.Value, view.Len, view.Type()), true
		}
		return &object.View{Array: view.Array, Start: view.Start + int(start.Value), Len: int(count.Value), Writable: view.Writable}, true
	}
	return nil, false
}

// window is the element storage a builtin operates on: an owned array
// whole, or the elements a view/span selects. Builtins that take []T or
// [*]T (is_valid_utf8, simd loads and stores, get) go through it so that
// borrowed windows and owned arrays are one case.
type window struct {
	array    *object.Array
	start    int
	length   int
	writable bool
}

func elementWindow(obj object.Object) (window, bool) {
	switch v := obj.(type) {
	case *object.Array:
		return window{array: v, start: 0, length: len(v.Elements), writable: true}, true
	case *object.View:
		return window{array: v.Array, start: v.Start, length: v.Len, writable: v.Writable}, true
	}
	return window{}, false
}

func (w window) get(i int) object.Object        { return w.array.Elements[w.start+i] }
func (w window) set(i int, value object.Object) { w.array.Elements[w.start+i] = value }

// bytes reads the window as byte values; false when an element is not a byte.
func (w window) bytes() ([]byte, bool) {
	out := make([]byte, 0, w.length)
	for i := 0; i < w.length; i++ {
		integer, ok := w.get(i).(*object.Integer)
		if !ok || integer.Value < 0 || integer.Value > 255 {
			return nil, false
		}
		out = append(out, byte(integer.Value))
	}
	return out, true
}

// evalSliceExpression realizes v[lo:hi] over an owned array or a view: a
// window [lo, hi) with 0 <= lo <= hi <= len, sharing the source's storage.
// Read-only versus writable is the declared type's business, enforced by
// the type checker; the interpreter keeps the source's class (an owned
// array's slice is writable).
func evalSliceExpression(expr *ast.SliceExpression, env *object.Environment) object.Object {
	source := Eval(expr.Seq, env)
	if isError(source) {
		return source
	}
	var array *object.Array
	base, length := 0, 0
	writable := true
	switch s := source.(type) {
	case *object.Array:
		array, length = s, len(s.Elements)
	case *object.View:
		array, base, length, writable = s.Array, s.Start, s.Len, s.Writable
	default:
		return newError("slice requires an array, view, or span, got %s", source.Type())
	}
	lo, hi := int64(0), int64(length)
	if expr.Low != nil {
		value := Eval(expr.Low, env)
		if isError(value) {
			return value
		}
		integer, ok := value.(*object.Integer)
		if !ok {
			return newError("slice bound must be an integer, got %s", value.Type())
		}
		lo = integer.Value
	}
	if expr.High != nil {
		value := Eval(expr.High, env)
		if isError(value) {
			return value
		}
		integer, ok := value.(*object.Integer)
		if !ok {
			return newError("slice bound must be an integer, got %s", value.Type())
		}
		hi = integer.Value
	}
	if lo < 0 || hi < lo || hi > int64(length) {
		return newError("slice out of range: [%d:%d] over %d elements", lo, hi, length)
	}
	return &object.View{Array: array, Start: base + int(lo), Len: int(hi - lo), Writable: writable}
}
