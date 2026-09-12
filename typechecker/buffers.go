package typechecker

// Owned foreign buffers (docs/spec/92-ffi.md section 2.8): Buffer[T] is an
// owner of runtime length over memory a runtime allocated. It is created
// only by c.own[T](ptr, count) inside an unsafe block, borrowed with
// view(&b) and span(&b) exactly like an owned fixed array, measured with
// len(b), and handed back with c.disown(b), after which it is consumed. It
// is never a value: no copy, no assignment, no parameter, no field, no
// return. Those rules keep the borrow checker's owner story intact for
// memory whose size the compiler cannot see.

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// BufferType is the checked type of Buffer[T] and Buffer[T, S]: an owner of
// runtime memory in custody state S (docs/spec/92-ffi.md section 2.8.5).
// Custody is a phantom marker: `Host` (the default, and the only state that
// can be borrowed or handed back) or any name a custody transition extern
// binding spells; Buffer[T, Host] and Buffer[T, Device] are distinct types
// with one representation.
type BufferType struct {
	Element Type
	Custody string
}

// HostCustody is the initial custody state: the program's own memory.
const HostCustody = "Host"

// custody names the state, defaulting the zero value to Host.
func (t *BufferType) custody() string {
	if t == nil || t.Custody == "" {
		return HostCustody
	}
	return t.Custody
}

// InHostCustody reports whether the buffer may be borrowed or handed back.
func (t *BufferType) InHostCustody() bool { return t.custody() == HostCustody }

// CustodyState is the buffer's custody state name.
func (t *BufferType) CustodyState() string { return t.custody() }

func (t *BufferType) String() string {
	if t == nil || t.Element == nil {
		return "Buffer[?]"
	}
	if t.custody() != HostCustody {
		return "Buffer[" + t.Element.String() + ", " + t.custody() + "]"
	}
	return "Buffer[" + t.Element.String() + "]"
}

func (t *BufferType) Equals(other Type) bool {
	o, ok := other.(*BufferType)
	if !ok || t == nil || o == nil || t.Element == nil || o.Element == nil {
		return false
	}
	return t.Element.Equals(o.Element) && t.custody() == o.custody()
}

// custodyTransitionCall reports whether an expression is a call to an
// extern binding that returns a Buffer — a custody transition (section
// 2.8.5) — and the binding's return type.
func (tc *TypeChecker) custodyTransitionCall(expr ast.Expression) (*BufferType, bool) {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return nil, false
	}
	callee, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || !tc.externFunctions[callee.Value] {
		return nil, false
	}
	scheme, bound := tc.env.Get(callee.Value)
	if !bound || scheme == nil {
		return nil, false
	}
	fn, isFn := scheme.Type.(*FunctionType)
	if !isFn {
		return nil, false
	}
	buffer, returnsBuffer := fn.ReturnType.(*BufferType)
	return buffer, returnsBuffer
}

// ContainsBufferStorage reports whether a type is, or holds, a Buffer.
func ContainsBufferStorage(typ Type) bool {
	switch t := typ.(type) {
	case *BufferType:
		return true
	case *ArrayType:
		return t != nil && ContainsBufferStorage(t.ElementType)
	case *RecordType:
		if t == nil {
			return false
		}
		for _, field := range t.Fields {
			if ContainsBufferStorage(field) {
				return true
			}
		}
	case *GenericType:
		if t == nil {
			return false
		}
		for _, arg := range t.TypeArgs {
			if ContainsBufferStorage(arg) {
				return true
			}
		}
	}
	return false
}

// rejectBufferValue reports a Buffer used as a value in the named position
// and reports whether it did.
func (tc *TypeChecker) rejectBufferValue(node ast.Node, typ Type, position string) bool {
	if !ContainsBufferStorage(typ) {
		return false
	}
	tc.addError(node, "Buffer[T] is an owner of runtime memory, not a value: it cannot be %s; borrow it with view(&b) or span(&b), measure it with len(b), hand it back with c.disown(b), or move it through a custody transition extern (docs/spec/92-ffi.md section 2.8)", position)
	return true
}

// isForeignOwnCall recognizes the one initializer a Buffer binding admits.
func isForeignOwnCall(expr ast.Expression) bool {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return false
	}
	member, _, ok := foreignBorrowAccess(call.Function)
	return ok && member == "own"
}

var _ = fmt.Sprintf
