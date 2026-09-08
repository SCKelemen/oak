package compiler

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/modules"
)

// DiagnosticError preserves first-class compiler diagnostics across the public
// Compilation/Stage API. Consumers may render these for a terminal, LSP, JSON,
// tests, or another UI without parsing human error text.
type DiagnosticError struct {
	Phase       string
	Diagnostics []*diagnostic.Diagnostic
}

func (e *DiagnosticError) Error() string {
	if e == nil {
		return ""
	}
	if len(e.Diagnostics) == 0 {
		return fmt.Sprintf("%s failed", e.Phase)
	}
	parts := make([]string, 0, len(e.Diagnostics))
	for _, d := range e.Diagnostics {
		if d == nil {
			continue
		}
		parts = append(parts, modules.DemangleText(d.PlainText()))
	}
	if len(parts) == 0 {
		return fmt.Sprintf("%s failed", e.Phase)
	}
	return fmt.Sprintf("%s failed:\n%s", e.Phase, strings.Join(parts, "\n"))
}

func diagnosticErrors(all []*diagnostic.Diagnostic) []*diagnostic.Diagnostic {
	errors := make([]*diagnostic.Diagnostic, 0, len(all))
	for _, d := range all {
		if d != nil && d.Severity == diagnostic.SeverityError {
			errors = append(errors, d)
		}
	}
	return errors
}
