package typechecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
)

const CodeResourceCallAliasConflict = "OAK-B0112"

// CodeResourceParameterForwarded reports a callee body that forwards one of
// its own mode-marked parameters beyond the authority its contract grants
// (docs/spec/50-borrowing.md section 9, callee-entry authority): a
// borrowed parameter passed to a borrowed-mut or consuming parameter, or a
// borrowed-mut parameter passed to a consuming one.
const CodeResourceParameterForwarded = "OAK-B0114"

// addResourceDiagnostic keeps resource authority failures in the borrow/resource
// diagnostic category even though typed resource analysis is hosted by typechecker.
func (tc *TypeChecker) addResourceDiagnostic(node ast.Node, title string) *diagnostic.Diagnostic {
	return tc.addResourceDiagnosticWithCode(node, CodeResourceUsedAfterConsume, title)
}

func (tc *TypeChecker) addResourceDiagnosticWithCode(node ast.Node, code, title string) *diagnostic.Diagnostic {
	var d *diagnostic.Diagnostic
	if node != nil {
		d = diagnostic.NewDiagnosticFromNodeWithCode(node, "borrow", code, title)
	} else {
		d = diagnostic.NewDiagnosticWithCode(lsp.Range{}, "borrow", code, title)
	}
	tc.diagnostics.AddDiagnostic(d)
	return d
}
