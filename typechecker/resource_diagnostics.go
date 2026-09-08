package typechecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
)

// addResourceDiagnostic keeps OAK-B0111 in the borrow/resource diagnostic
// category even though typed resource analysis is hosted by typechecker.
func (tc *TypeChecker) addResourceDiagnostic(node ast.Node, title string) *diagnostic.Diagnostic {
	var d *diagnostic.Diagnostic
	if node != nil {
		d = diagnostic.NewDiagnosticFromNodeWithCode(node, "borrow", CodeResourceUsedAfterConsume, title)
	} else {
		d = diagnostic.NewDiagnosticWithCode(lsp.Range{}, "borrow", CodeResourceUsedAfterConsume, title)
	}
	tc.diagnostics.AddDiagnostic(d)
	return d
}
