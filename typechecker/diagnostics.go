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

	CodeMatchNonExhaustive = "OAK-T0201"
	CodeMatchRedundantArm  = "OAK-T0202"
	CodeMatchImpossibleArm = "OAK-T0203"

	CodeGADTResultInvalid  = "OAK-T0301"
	CodeGADTResultMismatch = "OAK-T0302"

	// CodeAssertOperands rejects assert_eq/assert_ne operands that are not
	// two values of one fixed-width integer, float, or Bool type
	// (docs/spec/85-discipline.md section 5).
	CodeAssertOperands = "OAK-T0601"

	// CodeGuardWrap reports unsigned `+`, `-` or `*` computed inside an
	// ordering comparison (`off + len <= cap`): the sum wraps before the
	// guard sees it (docs/spec/20-types.md §11.1a). Information severity —
	// listed by `oak vet`, never a rejection.
	CodeGuardWrap = "OAK-T0701"
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

// addTypeInformation records a finding that neither profile rejects: it is
// listed by `oak vet` beside the recorded assumptions and stays out of the
// build gate (docs/spec/85-discipline.md §6a).
func (tc *TypeChecker) addTypeInformation(node ast.Node, code, title string) *diagnostic.Diagnostic {
	d := tc.addTypeWarning(node, code, title)
	d.Severity = diagnostic.SeverityInformation
	return d
}

func (tc *TypeChecker) addTypeWarning(node ast.Node, code, title string) *diagnostic.Diagnostic {
	var d *diagnostic.Diagnostic
	if node != nil {
		d = diagnostic.NewDiagnosticFromNodeWithCode(node, "typechecker", code, title)
	} else {
		d = diagnostic.NewDiagnosticWithCode(lsp.Range{}, "typechecker", code, title)
	}
	d.Severity = diagnostic.SeverityWarning
	tc.diagnostics.AddDiagnostic(d)
	return d
}
