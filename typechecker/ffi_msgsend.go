package typechecker

// Objective-C message sends (docs/spec/92-ffi.md section 2.12, ml roadmap
// D5): `c.msg_send[(params) -> ret](receiver, selector, args...)` calls the
// runtime's `objc_msgSend` under a per-call boundary signature. The receiver
// and the selector are the two leading `c.Ptr` parameters every message
// send has; the bracketed signature names the rest. The call is checked as
// an extern call of `(c.Ptr, c.Ptr, params) -> ret`, and the backend casts
// `objc_msgSend` to exactly that prototype.

import "github.com/SCKelemen/oak/ast"

// CodeMessageSend rejects a `c.msg_send` whose bracket is not a boundary
// function type, that appears outside an unsafe block, or that is used
// anywhere but as the callee of a call (docs/spec/92-ffi.md section 2.12).
const CodeMessageSend = "OAK-F0115"

// MessageSendCallee recognizes the callee `c.msg_send[(params) -> ret]` and
// returns the bracketed signature, for the type checker, the backends, the
// borrow checker, and the effect checker.
func MessageSendCallee(fn ast.Expression) (*ast.FunctionTypeExpression, bool) {
	indexExpr, ok := fn.(*ast.IndexExpression)
	if !ok || indexExpr.Dot {
		return nil, false
	}
	library, member, isLibrary := libraryAccess(indexExpr.Left)
	if !isLibrary || library != "c" || member != "msg_send" {
		return nil, false
	}
	signature, isFn := indexExpr.Index.(*ast.FunctionTypeExpression)
	if !isFn {
		return nil, false
	}
	return signature, true
}

// MessageSendCall recognizes an invocation whose callee is `c.msg_send[...]`.
func MessageSendCall(call *ast.InvocationExpression) (*ast.FunctionTypeExpression, bool) {
	if call == nil {
		return nil, false
	}
	return MessageSendCallee(call.Function)
}

// checkMessageSendCallee types the callee of a message send: inside an
// unsafe block, with a bracketed signature obeying the extern rule (section
// 2.3), the call is a call to a foreign function of type `(c.Ptr, c.Ptr,
// params) -> ret` — receiver, selector, then the declared parameters. The
// trust contract (the selector's implementation has that signature) is the
// program's; the borrow checker records it under OAK-B0122 like c.fn_at's.
func (tc *TypeChecker) checkMessageSendCallee(expr *ast.InvocationExpression, signature *ast.FunctionTypeExpression) Type {
	indexExpr := expr.Function.(*ast.IndexExpression)
	if tc.unsafeDepth == 0 {
		d := tc.addTypeDiagnostic(expr, CodeMessageSend,
			"c.msg_send calls the Objective-C runtime under a signature the program asserts and is admitted only inside an unsafe block")
		d.AddNote("the program asserts that the selector's implementation has the bracketed signature; the borrow checker records the assumption as OAK-B0122 (docs/spec/92-ffi.md section 2.12)")
		d.AddHelp("wrap the send in unsafe { ... }")
	}
	if len(expr.Arguments) < 2 {
		d := tc.addTypeDiagnostic(expr, CodeMessageSend,
			"c.msg_send takes the receiver and the selector, both c.Ptr, before the declared arguments")
		d.AddHelp("c.msg_send[(c.Int) -> c.Ptr](object, selector, c.Int(i32(1)))")
		return nil
	}
	saved := tc.cFnAnnotationAllowed
	tc.cFnAnnotationAllowed = true
	declared := tc.parseCFnType(indexExpr, signature)
	tc.cFnAnnotationAllowed = saved
	if declared == nil {
		return nil
	}
	cfn := declared.(*CFnType)
	params := make([]Type, 0, len(cfn.Parameters)+2)
	params = append(params, &CType{Name: "Ptr"}, &CType{Name: "Ptr"})
	params = append(params, cfn.Parameters...)
	return &CFnType{Parameters: params, ReturnType: cfn.ReturnType, Expr: signature}
}
