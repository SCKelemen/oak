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
	Eligible []NativeBuildInput         `json:"eligible"`
	Externs  []NativeBuildInput         `json:"externs"`
	Supplied []NativeBuildSuppliedInput `json:"supplied"`
}

// NativeBuildSuppliedInput identifies an actually selected assembly unit,
// independently of the optimizer's generated candidates.
type NativeBuildSuppliedInput struct {
	Input      NativeBuildInput `json:"input"`
	Arch       string           `json:"arch"`
	BodySHA256 string           `json:"body_sha256"`
}

// NativeBuildSupplied observes the stitcher's real verdict. A supplied unit
// never acquires invented optimizer selections or validation records.
// TransientResourceExhausted is cache-persistence metadata, not a different
// verification result: preserve its actual Trusted/Witnessed status and reason.
// This observation neither stores verdicts nor changes hybrid admission policy.
type NativeBuildSupplied struct {
	Input      NativeBuildInput `json:"input"`
	Arch       string           `json:"arch"`
	BodySHA256 string           `json:"body_sha256"`
	Status     string           `json:"status"`
	Reason     string           `json:"reason"`
	Callees    []string         `json:"callees"`
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
	Supplied      []NativeBuildSupplied `json:"supplied"`
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
	return nativeBuildInventory(model.Tree.Root, model.AsmFunctions), nil
}

func nativeBuildInventory(root *ast.Program, suppliedFunctions []*asm.Function) NativeBuildInventory {
	result := NativeBuildInventory{Eligible: []NativeBuildInput{}, Externs: []NativeBuildInput{}, Supplied: []NativeBuildSuppliedInput{}}
	declarations := map[string]NativeBuildInput{}
	for _, stmt := range root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil {
			continue
		}
		input := NativeBuildInput{Name: fn.Name.Value, SourceSHA256: fmt.Sprintf("%x", sha256.Sum256([]byte(fn.String()))), ExternSymbol: fn.ExternSymbol}
		declarations[input.Name] = input
		if fn.ExternSymbol != "" {
			result.Externs = append(result.Externs, input)
			continue
		}
		if fn.Body != nil && !fn.AsmBacked && fn.Receiver == nil && len(fn.TypeParams) == 0 {
			result.Eligible = append(result.Eligible, input)
		}
	}
	// Use actual stitch outputs, not AsmBacked: an inert foreign dispatch
	// realization can carry that marker without selecting a unit on this target.
	for _, fn := range suppliedFunctions {
		if fn == nil {
			result.Supplied = append(result.Supplied, NativeBuildSuppliedInput{})
			continue // Invalid observation identity fails closed in the consumer.
		}
		result.Supplied = append(result.Supplied, NativeBuildSuppliedInput{Input: declarations[fn.Name], Arch: fn.Arch, BodySHA256: nativeSuppliedBodyDigest(fn)})
	}
	return result
}

func nativeBuildSuppliedRows(inputs []NativeBuildSuppliedInput, verdicts map[string]asm.Verdict) []NativeBuildSupplied {
	rows := make([]NativeBuildSupplied, len(inputs))
	for i, input := range inputs {
		row := NativeBuildSupplied{Input: input.Input, Arch: input.Arch, BodySHA256: input.BodySHA256, Status: "unfinished", Callees: []string{}}
		if verdict, ok := verdicts[input.Input.Name]; ok {
			row.Status, row.Reason = nativeBuildVerdictStatus(verdict), verdict.Message
			row.Callees = append([]string{}, verdict.Callees...)
		}
		rows[i] = row
	}
	return rows
}

func nativeBuildVerdictStatus(verdict asm.Verdict) string {
	switch verdict.Kind {
	case asm.VerdictProven:
		return "proven"
	case asm.VerdictWitnessed:
		return "witnessed"
	case asm.VerdictTrusted:
		return "trusted"
	default:
		return "error"
	}
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
			row.Status = nativeBuildVerdictStatus(verdict)
			row.Reason = verdict.Message
			row.Callees = append([]string{}, verdict.Callees...)
		}
	}
}
