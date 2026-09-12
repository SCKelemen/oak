package compiler

import (
	"fmt"
	"os"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/typechecker"
)

// lowerNativeBodies runs the native backend over the program's ordinary
// functions (docs/spec/94-assembler.md §9). A function the backend lowers
// becomes an asm function beside the units: it passes the seam checker (a
// finding there is a backend bug and rejects the compilation), is verified
// against its own Oak body (a mismatch rejects; proof, evidence, and trust
// are reported), and its Oak body stays as the portable realization. A
// function outside the backend's subset is left to the C backend, with the
// reason reported as information.
func (comp Compilation) lowerNativeBodies(root *ast.Program, tc *typechecker.TypeChecker) ([]*asm.Function, []*diagnostic.Diagnostic) {
	var diagnostics []*diagnostic.Diagnostic
	functions := map[string]*ast.FunctionStatement{}
	records := map[string]*ast.RecordLiteral{}
	adts := map[string]*ast.ADTType{}
	symbols := map[string]bool{}
	for _, stmt := range root.Statements {
		// A record type declaration: an ADT with one record-literal variant
		// (docs/spec/40-records.md), monomorphic.
		if adt, isADT := stmt.(*ast.ADTType); isADT && adt.Name != nil && len(adt.TypeParams) == 0 {
			if literal, isRecord := recordShape(adt); isRecord {
				records[adt.Name.Value] = literal
			} else {
				adts[adt.Name.Value] = adt
			}
			continue
		}
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil {
			continue
		}
		symbols[fn.Name.Value] = true
		if fn.ExternSymbol == "" && fn.Receiver == nil && len(fn.TypeParams) == 0 {
			functions[fn.Name.Value] = fn
		}
	}
	var lowered []*asm.Function
	for _, stmt := range root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.Body == nil || fn.AsmBacked || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 {
			continue
		}
		asmFn, err := nativegen.Compile(fn, functions, records, adts, tc)
		if err != nil {
			if _, outside := err.(nativegen.Unsupported); outside {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s left to the C backend (%v)", fn.Name.Value, err)))
				continue
			}
			diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
			continue
		}
		if os.Getenv("OAK_NATIVE_DUMP") != "" {
			// A debugging aid: the lowered assembly of every function, as the
			// checker sees it.
			fmt.Fprint(os.Stderr, nativegen.Describe(asmFn))
		}
		if findings := asm.Check(asmFn, fn, symbols); len(findings) != 0 {
			for _, finding := range findings {
				diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: the checker refuses the lowering of %s: %s", fn.Name.Value, finding)))
			}
			continue
		}
		verdict := asm.Verify(asmFn, fn, fn.Body)
		if verdict.Kind == asm.VerdictMismatch {
			diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", "native backend: "+verdict.Message))
			continue
		}
		diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", "native backend: "+verdict.Message))
		fn.NativeBacked = true
		lowered = append(lowered, asmFn)
	}
	return lowered, diagnostics
}
