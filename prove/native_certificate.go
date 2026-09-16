package prove

// Audit-only checking for the bounded native scalar certificate slice. The
// formula is never accepted from storage or from the caller: it is regenerated
// from the exact machine function and verifier reference body on every check.

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// NativeEqualityCertificateResult records the exact regenerated obligation
// and the work performed by the LRAT checker. Counts are diagnostics only;
// CheckNativeEqualityCertificate's authority is CheckLRAT over the complete
// regenerated DIMACS text.
type NativeEqualityCertificateResult struct {
	Variables int
	Clauses   int
	LRAT      LRATResult
}

// CheckNativeEqualityCertificate regenerates a closed scalar native
// inequivalence formula and accepts certificate only when it derives the empty
// clause from that exact formula. It is intentionally not wired to compiler
// verdict selection yet; callers may use it only as an additional audit.
func CheckNativeEqualityCertificate(fn *asm.Function, decl *ast.FunctionStatement, certificate string) (NativeEqualityCertificateResult, error) {
	var result NativeEqualityCertificateResult
	cnf, reason, ok := asm.ExportNativeEqualityCNF(fn, decl)
	if !ok {
		return result, fmt.Errorf("native equality certificate unavailable: %s", reason)
	}
	if cnf.Settled != nil {
		return result, fmt.Errorf("native equality obligation settled without an LRAT certificate: %s", cnf.Settled.Message)
	}
	if cnf.Text == "" {
		return result, fmt.Errorf("native equality exporter produced no formula")
	}
	result.Variables, result.Clauses = cnf.Variables, cnf.Clauses
	checked, err := CheckLRAT(cnf.Text, certificate)
	if err != nil {
		return result, fmt.Errorf("native equality certificate refused: %w", err)
	}
	result.LRAT = checked
	return result, nil
}
