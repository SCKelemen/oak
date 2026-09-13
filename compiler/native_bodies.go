package compiler

import (
	"fmt"
	"os"
	"reflect"
	"strconv"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/typechecker"
)

// lowerNativeBodies runs the native backend over the program's ordinary
// functions on the target's assembler lane (docs/spec/94-assembler.md §9,
// AArch64 or RV64). A function the backend lowers
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
	templates := map[string]*ast.ADTType{}
	symbols := map[string]bool{}
	for _, stmt := range root.Statements {
		// A record type declaration: an ADT with one record-literal variant
		// (docs/spec/40-records.md), monomorphic.
		if adt, isADT := stmt.(*ast.ADTType); isADT && adt.Name != nil {
			if len(adt.TypeParams) > 0 {
				templates[adt.Name.Value] = adt
				continue
			}
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
	specializeInstantiations(tc, templates, records, adts)
	constants := nativeConstants(root)
	var lowered []*asm.Function
	for _, stmt := range root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.Body == nil || fn.AsmBacked || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 {
			continue
		}
		// The native backend sees a read of a constant top-level scalar as
		// the typed literal it is (the OS pilot's N1: `page_size`,
		// `entries`); the C emitter keeps the original body.
		source := substituteConstants(fn, constants)
		lane := nativegen.Lane{Arch: comp.options.Target.AsmArch(), SoftFloat: comp.options.Target.Freestanding() && comp.options.Target.Arch == target.ArchRiscv64}
		// Check elision (docs/spec/94-assembler.md §9): an element access the
		// typechecker proved in range is lowered without its guard first;
		// if the seam checker cannot admit the body from the facts on the
		// path, the body is lowered again with every guard. The checker
		// decides safety; the elision is only what it already knows.
		lane.ElideProven = lane.Arch == asm.ArchArm64
		asmFn, err := nativegen.CompileFor(lane, source, functions, records, adts, tc)
		if err != nil {
			if _, outside := err.(nativegen.Unsupported); outside {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s left to the C backend (%v)", fn.Name.Value, err)))
				continue
			}
			diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
			continue
		}
		findings := asm.Check(asmFn, source, symbols)
		if len(findings) != 0 && lane.ElideProven && nativegen.ElidedGuards(asmFn) > 0 {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its element guards (the checker did not admit the elided form: %s)", fn.Name.Value, findings[0])))
			lane.ElideProven = false
			asmFn, err = nativegen.CompileFor(lane, source, functions, records, adts, tc)
			if err != nil {
				diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
				continue
			}
			findings = asm.Check(asmFn, source, symbols)
		} else if elided := nativegen.ElidedGuards(asmFn); elided > 0 && len(findings) == 0 {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d element guard(s) elided under the checker's own facts", fn.Name.Value, elided)))
		}
		if os.Getenv("OAK_NATIVE_DUMP") != "" {
			// A debugging aid: the lowered assembly of every function, as the
			// checker sees it.
			fmt.Fprint(os.Stderr, nativegen.Describe(asmFn))
		}
		if len(findings) != 0 {
			for _, finding := range findings {
				diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: the checker refuses the lowering of %s: %s", fn.Name.Value, finding)))
			}
			continue
		}
		verdict := asm.Verify(asmFn, source, source.Body)
		if verdict.Kind == asm.VerdictMismatch {
			diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", "native backend: "+verdict.Message))
			continue
		}
		diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", "native backend: "+verdict.Message))
		fn.NativeBacked = true
		fn.AsmArch = asmFn.Arch // the C emitter guards the Oak body by the lane's negation
		lowered = append(lowered, asmFn)
	}
	return lowered, diagnostics
}

// specializeInstantiations adds every generic ADT instantiation the
// typechecker recorded (Option[u32], Result[u32, Overflow], Ring[u8, 4]) as
// a monomorphic declaration under its mangled name — the template's
// variants with the type parameters substituted (typechecker.SubstituteTypeAST,
// the one substitution authority) — so the native backend and the verifier
// see exactly the types the C backend emits for them.
func specializeInstantiations(tc *typechecker.TypeChecker, templates map[string]*ast.ADTType, records map[string]*ast.RecordLiteral, adts map[string]*ast.ADTType) {
	if tc == nil {
		return
	}
	for _, inst := range tc.ADTInstantiations() {
		template, declared := templates[inst.ADT]
		if !declared || len(template.TypeParams) != len(inst.Args) {
			continue
		}
		bindings := make(map[string]ast.Expression, len(inst.Args))
		for i, param := range template.TypeParams {
			if param == nil || param.Name == nil {
				continue
			}
			bindings[param.Name.Value] = argumentExpressionOf(inst.Args[i])
		}
		mangled := inst.MangledName()
		specialized := &ast.ADTType{BaseNode: template.BaseNode, Token: template.Token, EndToken: template.EndToken, Name: &ast.Identifier{Token: template.Name.Token, Value: mangled}, TagValues: template.TagValues}
		ok := true
		for _, variant := range template.Variants {
			payload, okPayload := typechecker.SubstituteTypeAST(variant.Payload, bindings)
			if !okPayload {
				ok = false
				break
			}
			literal := variant.Literal
			if recordLit, isRecord := variant.Literal.(*ast.RecordLiteral); isRecord {
				substituted := &ast.RecordLiteral{BaseNode: recordLit.BaseNode, Token: recordLit.Token, EndToken: recordLit.EndToken, Fields: map[string]ast.Expression{}, Layout: recordLit.Layout, TypeName: recordLit.TypeName}
				for _, field := range recordLit.FieldOrder {
					fieldType, okField := typechecker.SubstituteTypeAST(field.Value, bindings)
					if !okField {
						ok = false
						break
					}
					substituted.Fields[field.Name] = fieldType
					substituted.FieldOrder = append(substituted.FieldOrder, ast.RecordField{Token: field.Token, Name: field.Name, Value: fieldType, Align: field.Align})
				}
				literal = substituted
			}
			specialized.Variants = append(specialized.Variants, &ast.ADTVariant{Token: variant.Token, Name: variant.Name, Payload: payload, Literal: literal, Result: variant.Result})
		}
		if !ok {
			continue
		}
		if literal, isRecord := recordShape(specialized); isRecord {
			records[mangled] = literal
		} else {
			adts[mangled] = specialized
		}
	}
}

// argumentExpressionOf spells an instantiation argument atom as a type
// expression: an integer constant, or a type name.
func argumentExpressionOf(atom string) ast.Expression {
	if n, err := strconv.ParseInt(atom, 10, 64); err == nil {
		return &ast.IntegerLiteral{Value: n}
	}
	return &ast.Identifier{Value: atom}
}

// nativeConstants is the set of constant integer top-level bindings the
// native lowering folds (codegen.ConstantScalarGlobals, integers only: a
// Bool or float constant has no conversion spelling to fold through).
func nativeConstants(root *ast.Program) map[string]*ast.VariableDeclaration {
	constants := map[string]*ast.VariableDeclaration{}
	for name, decl := range codegen.ConstantScalarGlobals(root) {
		if typeName, isIdent := decl.Type.(*ast.Identifier); isIdent && nativeConstantTypes[typeName.Value] {
			constants[name] = decl
		}
	}
	return constants
}

var nativeConstantTypes = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true, "i8": true, "i16": true, "i32": true, "i64": true, "byte": true,
}

// substituteConstants returns fn with every read of a constant top-level
// integer binding replaced by its initializer under the binding's type,
// `T(init)`, on a copy of the declaration (docs/spec/94-assembler.md
// section 9): the generator and the verifier both see the literal, and
// the emitted C keeps the original body and its `static const`. A function
// that reads none is returned as is. Oak forbids shadowing a global, so a
// name that is a constant is the constant wherever it appears as a value
// (member names after `.` are not visited).
func substituteConstants(fn *ast.FunctionStatement, constants map[string]*ast.VariableDeclaration) *ast.FunctionStatement {
	if len(constants) == 0 {
		return fn
	}
	reads := false
	_ = transformSyntax(reflect.ValueOf(fn.Body), func(expr ast.Expression) (ast.Expression, error) {
		if id, isIdent := expr.(*ast.Identifier); isIdent {
			if _, isConst := constants[id.Value]; isConst {
				reads = true
			}
		}
		return expr, nil
	})
	if !reads {
		return fn
	}
	clone := cloneSyntax(reflect.ValueOf(fn)).Interface().(*ast.FunctionStatement)
	_ = transformSyntax(reflect.ValueOf(clone), func(expr ast.Expression) (ast.Expression, error) {
		id, isIdent := expr.(*ast.Identifier)
		if !isIdent {
			return expr, nil
		}
		decl, isConst := constants[id.Value]
		if !isConst {
			return expr, nil
		}
		typeName := decl.Type.(*ast.Identifier).Value
		init := cloneSyntax(reflect.ValueOf(decl.Value)).Interface().(ast.Expression)
		return &ast.InvocationExpression{
			Token:     id.Token,
			Function:  &ast.Identifier{Token: id.Token, Value: typeName},
			Arguments: []ast.Expression{init},
		}, nil
	})
	return clone
}
