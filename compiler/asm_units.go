package compiler

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/nativegen"
)

// stitchAsmUnits parses the compilation's `.oakasm` units, pairs each unit
// function with the source's definition-less declaration of the same name
// (marking it AsmBacked), and runs the assembler's seam checker
// (docs/spec/94-assembler.md). Every failure is an error-severity
// diagnostic in the "asm" phase: a body-less declaration with no unit, a
// unit function with no declaration, a signature mismatch, or any checker
// finding rejects the compilation.
func (comp Compilation) stitchAsmUnits(root *ast.Program) ([]*asm.Function, []*diagnostic.Diagnostic) {
	var diagnostics []*diagnostic.Diagnostic
	report := func(format string, args ...interface{}) {
		diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "asm", fmt.Sprintf(format, args...)))
	}

	declarations := map[string]*ast.FunctionStatement{}
	fallbacks := map[string]*ast.FunctionStatement{}
	symbols := map[string]bool{}
	records := map[string]*ast.RecordLiteral{}
	adts := map[string]*ast.ADTType{}
	for _, stmt := range root.Statements {
		// A record type declaration (one record-literal variant): the
		// checker binds records at the boundary by their placed size.
		if adt, isADT := stmt.(*ast.ADTType); isADT && adt.Name != nil && len(adt.TypeParams) == 0 {
			if literal, isRecord := recordShape(adt); isRecord {
				records[adt.Name.Value] = literal
			} else {
				adts[adt.Name.Value] = adt
			}
			continue
		}
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.ExternSymbol != "" || len(fn.TypeParams) > 0 || fn.Receiver != nil {
			if ok && fn.Name != nil {
				symbols[fn.Name.Value] = true
			}
			continue
		}
		symbols[fn.Name.Value] = true
		if fn.Body == nil {
			declarations[fn.Name.Value] = fn
		} else {
			fallbacks[fn.Name.Value] = fn
		}
	}

	var functions []*asm.Function
	seen := map[string]string{}
	for _, unitText := range comp.options.AsmUnits {
		unit, errs := asm.ParseUnit(unitText.Path, unitText.Text)
		for _, err := range errs {
			report("%v", err)
		}
		if unit == nil {
			continue
		}
		for _, fn := range unit.Functions {
			if previous, duplicate := seen[fn.Name]; duplicate {
				report("%s: asm function %s is also defined in %s (one function, one unit)", unitText.Path, fn.Name, previous)
				continue
			}
			seen[fn.Name] = unitText.Path
			decl, declared := declarations[fn.Name]
			if !declared {
				// A declaration WITH a body is the Oak fallback: the asm
				// realizes the same signature on AArch64, the body elsewhere.
				if fallback, hasFallback := fallbacks[fn.Name]; hasFallback {
					decl = fallback
					fn.Fallback = true
				} else {
					report("%s: asm function %s has no Oak declaration", unitText.Path, fn.Name)
					continue
				}
			}
			decl.AsmBacked = true
			fn.Composites = nativegen.Composites(records, adts)
			fn.Records, fn.ADTs = records, adts
			findings := asm.Check(fn, decl, symbols)
			for _, finding := range findings {
				report("%s: %s", unitText.Path, finding)
			}
			// With an Oak fallback body as the specification, verify the
			// asm against it (docs/spec/94-assembler.md §8): a definite
			// mismatch rejects; proof, evidence, and trust are reported as
			// labeled information.
			if len(findings) == 0 && fn.Fallback && decl.Body != nil {
				verdict := asm.Verify(fn, decl, decl.Body)
				if verdict.Kind == asm.VerdictMismatch {
					report("%s: %s", unitText.Path, verdict.Message)
				} else {
					diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "asm", verdict.Message))
				}
			}
			functions = append(functions, fn)
		}
	}

	for name, decl := range declarations {
		if !decl.AsmBacked {
			report("function %s is declared without a definition and no asm unit provides its body (docs/spec/94-assembler.md)", name)
		}
	}
	return functions, diagnostics
}
