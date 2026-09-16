package prove

// Audit-only LRAT checking for the independently replayed native bitwise
// slice.  The formula is never supplied by the caller or read from a cache:
// every check regenerates it from the exact machine function and Oak body.

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// NativeBitwiseEqualityCertificateResult records diagnostics for one accepted
// certificate.  It is not a compiler verdict and no compiler path consumes it.
type NativeBitwiseEqualityCertificateResult struct {
	Variables int
	Clauses   int
	LRAT      LRATResult
}

// CheckNativeBitwiseEqualityCertificate regenerates the independently
// replayed direct-disequality formula and checks certificate only against
// those regenerated DIMACS bytes.  Constant-settled audits deliberately
// refuse this certificate path because they have no clause formula to prove.
func CheckNativeBitwiseEqualityCertificate(fn *asm.Function, decl *ast.FunctionStatement, certificate string) (NativeBitwiseEqualityCertificateResult, error) {
	var result NativeBitwiseEqualityCertificateResult
	audit, reason, ok := asm.ExportNativeBitwiseEqualityAudit(fn, decl)
	if !ok {
		return result, fmt.Errorf("native bitwise equality certificate unavailable: %s", reason)
	}
	if settled, ok := audit.Settled(); ok {
		return result, fmt.Errorf("native bitwise equality obligation settled without an LRAT formula: %s", settled.Message)
	}
	formula := audit.DIMACS()
	if formula == "" || audit.Variables() <= 0 || audit.Clauses() <= 0 {
		return result, fmt.Errorf("native bitwise equality exporter produced no complete formula")
	}
	if strings.TrimSpace(certificate) == "" {
		return result, fmt.Errorf("native bitwise equality certificate is empty")
	}
	result.Variables, result.Clauses = audit.Variables(), audit.Clauses()
	checked, err := CheckLRAT(formula, certificate)
	if err != nil {
		return result, fmt.Errorf("native bitwise equality certificate refused: %w", err)
	}
	result.LRAT = checked
	return result, nil
}
