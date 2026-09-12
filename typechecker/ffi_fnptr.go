package typechecker

// Calls through a foreign function pointer (docs/spec/92-ffi.md section
// 2.10, ml roadmap D3): the boundary function type `c.Fn[(params) -> ret]`
// and the form `c.fn_at(p)` that names the function at a pointer inside an
// unsafe block. A call through such a binding is checked as an extern call
// of the annotated signature; the backend casts the pointer to it.

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// CFnType is a foreign function of a declared boundary signature: the type
// of a local binding that `c.fn_at(p)` initializes inside an unsafe block.
// Its parameter and return types are the boundary types an extern binding
// accepts (section 2.3), so a call through it is checked exactly like an
// extern call; the value itself is opaque to Oak — never a field, a global,
// a parameter, a return value, or an element.
type CFnType struct {
	Parameters []Type
	ReturnType Type
	// Expr is the annotation the signature came from, so the backend spells
	// the C parameter types from the same table as extern prototypes.
	Expr *ast.FunctionTypeExpression
}

func (t *CFnType) String() string {
	params := make([]string, 0, len(t.Parameters))
	for _, p := range t.Parameters {
		params = append(params, p.String())
	}
	ret := "()"
	if t.ReturnType != nil {
		ret = t.ReturnType.String()
	}
	return "c.Fn[(" + strings.Join(params, ", ") + ") -> " + ret + "]"
}

func (t *CFnType) Equals(other Type) bool {
	o, ok := other.(*CFnType)
	if !ok || len(o.Parameters) != len(t.Parameters) {
		return false
	}
	for i := range t.Parameters {
		if !t.Parameters[i].Equals(o.Parameters[i]) {
			return false
		}
	}
	if t.ReturnType == nil || o.ReturnType == nil {
		return t.ReturnType == nil && o.ReturnType == nil
	}
	return t.ReturnType.Equals(o.ReturnType)
}

// CFnTypeExpression recognizes the annotation `c.Fn[(params) -> ret]` and
// returns its signature, for the type checker, the backend, and the effect
// checker.
func CFnTypeExpression(expr ast.Expression) (*ast.FunctionTypeExpression, bool) {
	indexExpr, ok := expr.(*ast.IndexExpression)
	if !ok || indexExpr.Dot {
		return nil, false
	}
	base, isIdent := indexExpr.Left.(*ast.Identifier)
	if !isIdent || base.Value != "c.Fn" {
		return nil, false
	}
	fnExpr, isFn := indexExpr.Index.(*ast.FunctionTypeExpression)
	if !isFn {
		return nil, false
	}
	return fnExpr, true
}

// ForeignFunctionAtCall recognizes `c.fn_at(p)` for the backends and the
// borrow checker.
func ForeignFunctionAtCall(call *ast.InvocationExpression) bool {
	if call == nil {
		return false
	}
	library, member, isLibrary := libraryAccess(call.Function)
	return isLibrary && library == "c" && member == "fn_at"
}

// parseCFnType types the annotation `c.Fn[(params) -> ret]`. The signature
// obeys the extern rule (section 2.3): every parameter type and any non-unit
// return type is a c.* type or a proven-layout struct, so the call site's
// argument forms and the backend's spellings are exactly those of an extern
// call. The annotation is admitted only where checkVariableDeclaration set
// cFnAnnotationAllowed — a local binding, inside an unsafe block, that
// `c.fn_at` initializes; anywhere else it is OAK-F0113.
func (tc *TypeChecker) parseCFnType(indexExpr *ast.IndexExpression, fnExpr *ast.FunctionTypeExpression) Type {
	if !tc.cFnAnnotationAllowed {
		d := tc.addTypeDiagnostic(indexExpr, CodeForeignFunctionType,
			"c.Fn is only the type of a local binding that c.fn_at(p) initializes inside an unsafe block")
		d.AddNote("a foreign function pointer never crosses back into Oak: it cannot be a field, a global, a parameter, a return type, or an element (docs/spec/92-ffi.md section 2.10)")
		return nil
	}
	params := make([]Type, 0, len(fnExpr.Parameters))
	valid := true
	for _, param := range fnExpr.Parameters {
		paramType := tc.parseTypeExpression(param)
		if paramType == nil {
			return nil
		}
		if !tc.boundaryValue(paramType) {
			d := tc.addTypeDiagnostic(param, CodeForeignFunctionType,
				fmt.Sprintf("c.Fn: parameter type %s cannot cross the C boundary", paramType))
			d.AddNote("a foreign function's parameters are c.* types or proven-layout structs, exactly as an extern binding's (docs/spec/92-ffi.md sections 2.3 and 2.10)")
			valid = false
		}
		params = append(params, paramType)
	}
	var returnType Type = &UnitType{}
	if fnExpr.Return != nil {
		returnType = tc.parseTypeExpression(fnExpr.Return)
		if returnType == nil {
			return nil
		}
		if _, isUnit := returnType.(*UnitType); !isUnit && !tc.boundaryValue(returnType) {
			d := tc.addTypeDiagnostic(fnExpr.Return, CodeForeignFunctionType,
				fmt.Sprintf("c.Fn: return type %s cannot cross the C boundary", returnType))
			d.AddNote("a foreign function returns a c.* type, a proven-layout struct, or () (docs/spec/92-ffi.md sections 2.3 and 2.10)")
			valid = false
		}
	}
	if !valid {
		return nil
	}
	return &CFnType{Parameters: params, ReturnType: returnType, Expr: fnExpr}
}

// checkForeignFunctionAt types `c.fn_at(p)`: inside an unsafe block, as the
// initializer of a named binding annotated `c.Fn[...]`, a foreign function
// at the address `p: c.Ptr` with the annotation's signature. The trust
// contract — the pointer is a function of exactly that signature, callable
// until the block ends — is the program's; the borrow checker records it
// (OAK-B0122), and the backend checks the one thing it can: a NULL pointer
// traps at the conversion.
func (tc *TypeChecker) checkForeignFunctionAt(expr *ast.InvocationExpression) Type {
	if tc.unsafeDepth == 0 {
		d := tc.addTypeDiagnostic(expr, CodeForeignBorrowPlacement,
			"c.fn_at takes a foreign function pointer on trust and is admitted only inside an unsafe block")
		d.AddNote("the program asserts that the pointer is a function of the annotated signature, callable for the block's extent (docs/spec/92-ffi.md section 2.10)")
		d.AddHelp("wrap the binding and its calls in unsafe { ... }")
	} else if tc.initializerUnderCheck != expr {
		d := tc.addTypeDiagnostic(expr, CodeForeignBorrowPlacement,
			"c.fn_at must initialize a named binding annotated c.Fn[...], so the function it names has a scope")
		d.AddHelp("bind it first: f: c.Fn[(c.Ptr) -> c.Int32] = c.fn_at(p)")
	}
	if len(expr.Arguments) != 1 {
		tc.addError(expr, "c.fn_at takes exactly one c.Ptr")
		return nil
	}
	ptrType := tc.checkExpression(expr.Arguments[0], &CType{Name: "Ptr"})
	if ptr, isC := ptrType.(*CType); ptrType != nil && (!isC || ptr.Name != "Ptr") {
		tc.addError(expr.Arguments[0], "c.fn_at takes a c.Ptr, got %s", ptrType)
		return nil
	}
	declared, isCFn := tc.initializerDeclaredType.(*CFnType)
	if !isCFn || tc.initializerUnderCheck != expr {
		d := tc.addTypeDiagnostic(expr, CodeForeignFunctionType,
			"c.fn_at needs the binding's signature: annotate it c.Fn[(params) -> ret]")
		d.AddNote("the annotation is the declared ABI of the foreign function, as an extern binding's signature is (docs/spec/92-ffi.md section 2.10)")
		return nil
	}
	return declared
}
