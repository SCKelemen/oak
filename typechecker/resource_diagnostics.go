package typechecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
)

const CodeResourceCallAliasConflict = "OAK-B0112"

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
