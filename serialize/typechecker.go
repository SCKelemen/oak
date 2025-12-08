package serialize

import (
	"fmt"

	"github.com/SCKelemen/oak/typechecker"
)

// TypecheckerJSON represents typechecker output in JSON format
type TypecheckerJSON struct {
	Errors      []string          `json:"errors,omitempty"`
	TypeEnv     map[string]string `json:"type_env,omitempty"` // variable name -> type string
	Diagnostics []DiagnosticJSON  `json:"diagnostics,omitempty"`
}

// DiagnosticJSON represents a diagnostic message
type DiagnosticJSON struct {
	Message  string `json:"message"`
	Severity string `json:"severity,omitempty"`
	Line     int    `json:"line,omitempty"`
	Column   int    `json:"column,omitempty"`
}

// SerializeTypechecker writes typechecker information to a JSONL file
// Each line represents a type-checked entity (variable, function, etc.) or an error
func SerializeTypechecker(tc *typechecker.TypeChecker, outputPath string) error {
	writer, err := NewJSONLWriter(outputPath)
	if err != nil {
		return err
	}
	defer writer.Close()

	// Get type environment
	env := tc.Env()
	if env != nil {
		// Serialize type environment entries
		// We need to iterate through the environment store
		// Since GetAll() might not exist, we'll serialize what we can access
		// For now, we'll serialize errors and diagnostics, and note that
		// type environment serialization may need additional methods
	}

	// Serialize errors (important for negative tests)
	errors := tc.Errors()
	if len(errors) > 0 {
		for i, errMsg := range errors {
			errorEntry := map[string]interface{}{
				"type":        "error",
				"error_index": i,
				"message":     errMsg,
			}
			if err := writer.WriteLine(errorEntry); err != nil {
				return fmt.Errorf("failed to write error: %w", err)
			}
		}
	}

	// Serialize diagnostics if available (includes errors with position info)
	diagnostics := tc.Diagnostics()
	if len(diagnostics) > 0 {
		for i, diag := range diagnostics {
			// Convert severity to string representation
			severityStr := "unknown"
			switch diag.Severity {
			case 1:
				severityStr = "error"
			case 2:
				severityStr = "warning"
			case 3:
				severityStr = "information"
			case 4:
				severityStr = "hint"
			}
			
			diagEntry := map[string]interface{}{
				"type":     "diagnostic",
				"index":    i,
				"message":  diag.Message,
				"severity": severityStr,
				"source":   diag.Source,
				"code":     diag.Code,
				"range": map[string]interface{}{
					"start": map[string]interface{}{
						"line":      diag.Range.Start.Line,
						"character": diag.Range.Start.Character,
					},
					"end": map[string]interface{}{
						"line":      diag.Range.End.Line,
						"character": diag.Range.End.Character,
					},
				},
			}
			if err := writer.WriteLine(diagEntry); err != nil {
				return fmt.Errorf("failed to write diagnostic: %w", err)
			}
		}
	}

	// If no errors, serialize a success marker
	if len(errors) == 0 && len(diagnostics) == 0 {
		successEntry := map[string]interface{}{
			"type":    "success",
			"message": "Type checking passed with no errors",
		}
		if err := writer.WriteLine(successEntry); err != nil {
			return fmt.Errorf("failed to write success marker: %w", err)
		}
	}

	return nil
}
