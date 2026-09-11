package typechecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/modules"
)

const CodeResourceCallAliasConflict = "OAK-B0112"

// CodeResourceParameterForwarded reports a callee body that forwards one of
// its own mode-marked parameters beyond the authority its contract grants
// (docs/spec/50-borrowing.md section 9, callee-entry authority): a
// borrowed parameter passed to a borrowed-mut or consuming parameter, or a
// borrowed-mut parameter passed to a consuming one.
const CodeResourceParameterForwarded = "OAK-B0114"

// CodeResourceUnknownCallable reports a resource passed through a callable
// whose resource contract is unknown — a function-typed parameter, a
// closure, or a reassigned function value (docs/spec/50-borrowing.md
// section 9, contracts across callable boundaries). An unknown contract is
// not an empty one, so the call fails closed.
const CodeResourceUnknownCallable = "OAK-B0115"

// CodeResourceCallableContractMismatch reports a function value passed for
// a function-typed parameter whose required callable contract it does not
// carry exactly — a consuming function where a borrowed one is required, an
// uncontracted or unknown function value where any mode is required
// (docs/spec/50-borrowing.md section 9, contracts on function types).
const CodeResourceCallableContractMismatch = "OAK-B0116"

// CodeResourceResultContract reports a body that does not honor its
// declared result identity (docs/spec/50-borrowing.md section 9): a
// fresh-return function returning a parameter or its alias, or an
// alias-return function returning anything but the declared parameter's
// authority.
const CodeResourceResultContract = "OAK-B0117"

// CodeResourceDependentResult reports a violation of a borrowed result's
// dependency (docs/spec/50-borrowing.md section 9, borrowed results): its
// owner mutated, consumed, or rebound while it lives; the result itself
// mutated, consumed, stored in an aggregate, or returned without a
// matching contract; or a rebinding that would let it outlive its owner.
const CodeResourceDependentResult = "OAK-B0118"

// addResourceDiagnostic keeps resource authority failures in the borrow/resource
// diagnostic category even though typed resource analysis is hosted by typechecker.
func (tc *TypeChecker) addResourceDiagnostic(node ast.Node, title string) *diagnostic.Diagnostic {
	return tc.addResourceDiagnosticWithCode(node, CodeResourceUsedAfterConsume, title)
}

func (tc *TypeChecker) addResourceDiagnosticWithCode(node ast.Node, code, title string) *diagnostic.Diagnostic {
	// Imported callables carry internal names; readers see the qualified
	// spelling (docs/spec/83-modules.md section 7).
	title = modules.DemangleText(title)
	var d *diagnostic.Diagnostic
	if node != nil {
		d = diagnostic.NewDiagnosticFromNodeWithCode(node, "borrow", code, title)
	} else {
		d = diagnostic.NewDiagnosticWithCode(lsp.Range{}, "borrow", code, title)
	}
	tc.diagnostics.AddDiagnostic(d)
	return d
}
