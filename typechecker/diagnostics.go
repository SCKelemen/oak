package typechecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
)

const (
	CodeConstraintRequirementMissing = "OAK-T0101"
	CodeConstraintRequirementInvalid = "OAK-T0102"
	CodeConstraintInferenceFailed    = "OAK-T0103"
	CodeConstraintUnsatisfied        = "OAK-T0104"
)

func (tc *TypeChecker) addTypeDiagnostic(node ast.Node, code, title string) *diagnostic.Diagnostic {
	var d *diagnostic.Diagnostic
	if node != nil {
		d = diagnostic.NewDiagnosticFromNodeWithCode(node, "typechecker", code, title)
	} else {
		d = diagnostic.NewDiagnosticWithCode(lsp.Range{}, "typechecker", code, title)
	}
	tc.diagnostics.AddDiagnostic(d)
	return d
}
