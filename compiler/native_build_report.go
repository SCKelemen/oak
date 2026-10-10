package compiler

import (
	"crypto/sha256"
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/opt"
)

// NativeBuildInput identifies a checked declaration before native lowering.
// Externs are dependencies, never verification obligations or proven bodies.
type NativeBuildInput struct {
	Name         string `json:"name"`
	SourceSHA256 string `json:"source_sha256"`
	ExternSymbol string `json:"extern_symbol"`
}

type NativeBuildInventory struct {
	Eligible []NativeBuildInput `json:"eligible"`
	Externs  []NativeBuildInput `json:"externs"`
}

type NativeBuildCandidate struct {
	Name         string `json:"name"`
	BodySHA256   string `json:"body_sha256"`
	RecipeSHA256 string `json:"recipe_sha256"`
	Outcome      string `json:"outcome"`
	Message      string `json:"message"`
	Cached       bool   `json:"cached"`
}

// NativeBuildFunction is output-only evidence. An absent terminal verdict is
// unfinished, never the zero value of asm.Verdict (which happens to be Trusted).
type NativeBuildFunction struct {
	Input        NativeBuildInput       `json:"input"`
	Status       string                 `json:"status"`
	Reason       string                 `json:"reason"`
	Callees      []string               `json:"callees"`
	Considered   int                    `json:"considered"`
	Materialized int                    `json:"materialized"`
	Selected     *NativeBuildCandidate  `json:"selected"`
	Validations  []NativeBuildCandidate `json:"validations"`
}

type NativeBuildReport struct {
	SchemaVersion int                   `json:"schema_version"`
	Inventory     NativeBuildInventory  `json:"inventory"`
	Functions     []NativeBuildFunction `json:"functions"`
}

// WithNativeBuildReport observes completed lowering after vector-callee
// demotion. It cannot change candidate admission, selection, or verification.
func (comp Compilation) WithNativeBuildReport(sink func(NativeBuildReport)) Compilation {
	comp.nativeBuildReport = sink
	return comp
}

// NativeInventory independently checks the same optimized frontend used by
// EmitNative, without running or trusting the native backend or its report.
func (comp Compilation) NativeInventory() (NativeBuildInventory, error) {
	comp.options.InlineHelpers = true
	comp.options.NativeAsm = true
	comp.options.NativeBodies = false
	comp.nativeBuildReport = nil
	model, err := comp.Check().Get()
	if err != nil {
		return NativeBuildInventory{}, err
	}
	return nativeBuildInventory(model.Tree.Root), nil
}

func nativeBuildInventory(root *ast.Program) NativeBuildInventory {
	result := NativeBuildInventory{Eligible: []NativeBuildInput{}, Externs: []NativeBuildInput{}}
	for _, stmt := range root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil {
			continue
		}
		input := NativeBuildInput{Name: fn.Name.Value, SourceSHA256: fmt.Sprintf("%x", sha256.Sum256([]byte(fn.String()))), ExternSymbol: fn.ExternSymbol}
		if fn.ExternSymbol != "" {
			result.Externs = append(result.Externs, input)
			continue
		}
		if fn.Body != nil && !fn.AsmBacked && fn.Receiver == nil && len(fn.TypeParams) == 0 {
			result.Eligible = append(result.Eligible, input)
		}
	}
	return result
}

func nativeBuildCandidate(driver *nativeDriver, candidate *opt.Candidate, verdict opt.Verdict) NativeBuildCandidate {
	key, err := driver.MaterializationKey(candidate)
	if err != nil {
		key = ""
	} // A missing identity makes the consumer reject.
	return NativeBuildCandidate{Name: candidate.Name(), BodySHA256: driver.Key(candidate), RecipeSHA256: key, Outcome: verdict.Outcome.String(), Message: verdict.Message, Cached: verdict.Cached}
}

func finishNativeBuildReport(report *NativeBuildReport, result nativeLowering) {
	for i := range report.Functions {
		row := &report.Functions[i]
		if reason, ok := result.Fallbacks[row.Input.Name]; ok {
			row.Status, row.Reason = "c-fallback", reason
		} else if verdict, ok := result.Verdicts[row.Input.Name]; ok {
			switch verdict.Kind {
			case asm.VerdictProven:
				row.Status = "proven"
			case asm.VerdictWitnessed:
				row.Status = "witnessed"
			case asm.VerdictTrusted:
				row.Status = "trusted"
			default:
				row.Status = "error"
			}
			row.Reason = verdict.Message
			row.Callees = append([]string{}, verdict.Callees...)
		}
	}
}
