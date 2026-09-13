package compiler

import (
	"fmt"
	"os"
	"strconv"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/object"
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
			if nativegen.VectorContract(fn) {
				// The native entry of a function under the vector contract
				// (nativegen.VectorContractSuffix): a call target too.
				symbols[nativegen.NativeSymbol(fn)] = true
			}
		}
	}
	specializeInstantiations(tc, templates, records, adts)
	constants := constantGlobals(root, tc)
	globals, globalDecls := addressableGlobals(root, tc, constants)
	var lowered []*asm.Function
	for _, stmt := range root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.Body == nil || fn.AsmBacked || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 {
			continue
		}
		// A read of a constant top-level scalar (the OS pilot's N1:
		// `page_size`, `entries`) reaches the backend and the verifier as
		// its folded value (constants); the C emitter keeps the body and
		// its `static const`.
		source := fn
		lane := nativegen.Lane{Arch: comp.options.Target.AsmArch(), SoftFloat: comp.options.Target.Freestanding() && comp.options.Target.Arch == target.ArchRiscv64}
		// Check elision (docs/spec/94-assembler.md §9): an element access the
		// typechecker proved in range is lowered without its guard first;
		// if the seam checker cannot admit the body from the facts on the
		// path, the body is lowered again with every guard. The checker
		// decides safety; the elision is only what it already knows.
		lane.ElideProven = lane.Arch == asm.ArchArm64
		lane.Globals = globals
		asmFn, err := nativegen.CompileFor(lane, source, functions, records, adts, constants, tc)
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
			asmFn, err = nativegen.CompileFor(lane, source, functions, records, adts, constants, tc)
			if err != nil {
				diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
				continue
			}
			findings = asm.Check(asmFn, source, symbols)
		} else if elided := nativegen.ElidedGuards(asmFn); elided > 0 && len(findings) == 0 {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d element guard(s) elided under the checker's own facts", fn.Name.Value, elided)))
		}
		// The verifier takes calls to program functions at their Oak bodies
		// (asm.Function.Callees, docs/spec/94-assembler.md §8).
		asmFn.Callees = functions
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
		for name := range asmFn.Globals {
			// The C emitter gives the global external linkage under the
			// label the native code names (codegen/globals.go).
			globalDecls[name].NativeAddressed = true
		}
		lowered = append(lowered, asmFn)
	}
	// A native function calls a vector-contract callee at its native entry,
	// so the callee must be native too; a caller whose callee stayed on the
	// C backend is demoted, and demotion cascades to a fixpoint.
	for changed := true; changed; {
		changed = false
		kept := lowered[:0]
		for _, asmFn := range lowered {
			fn := asmFn.Signature
			demoted := false
			for _, callee := range nativegen.VectorCallees(fn, functions) {
				if target := functions[callee]; target != nil && !target.NativeBacked {
					diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s left to the C backend (it passes vectors to %s, which the C backend realizes)", fn.Name.Value, callee)))
					demoted = true
					break
				}
			}
			if demoted {
				fn.NativeBacked = false
				fn.AsmArch = ""
				changed = true
				continue
			}
			kept = append(kept, asmFn)
		}
		lowered = kept
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

// constantScalarTypes are the declared types of the globals the native
// backend folds: the C backend's scalar constant set less the floats (a
// float constant is not yet materialized natively).
var constantScalarTypes = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true, "i8": true, "i16": true, "i32": true, "i64": true,
	"Bool": true, "byte": true,
}

// constantGlobals folds the program's constant globals to their values
// under the C backend's own rule (docs/spec/90-backend.md §8a,
// codegen.ConstantScalarGlobals: a typed scalar top-level binding with a
// constant initializer that no statement assigns, index-assigns, borrows,
// or addresses, outside any placed section; a target constant's `c.const`
// is no constant initializer, since only the C compiler knows its value
// per target). The initializers fold through the
// interpreter in declaration order — the semantics the C backend's own
// file-scope fold uses, so both realizations agree on every value — and
// every constant-initialized global, mutated or not, is bound for the
// initializers after it, as the C backend binds them. A global whose
// initializer does not fold is left out, and a function reading it stays
// with the C backend.
// addressableGlobals lists the mutable top-level scalars a native body
// may address (docs/spec/94-assembler.md §9, the OS pilot's N3): a typed
// scalar binding some statement writes (the constant ones are folded
// instead), neither measured nor a target constant.
func addressableGlobals(root *ast.Program, tc *typechecker.TypeChecker, constants map[string]asm.Constant) (map[string]asm.Global, map[string]*ast.VariableDeclaration) {
	globals := map[string]asm.Global{}
	decls := map[string]*ast.VariableDeclaration{}
	if root == nil {
		return globals, decls
	}
	mutated := codegen.MutatedGlobals(root)
	targetConstants := map[string]bool{}
	if tc != nil {
		for _, constant := range tc.TargetConstants() {
			targetConstants[constant.Name] = true
		}
	}
	for _, stmt := range root.Statements {
		decl, isDecl := stmt.(*ast.VariableDeclaration)
		if !isDecl || decl.Name == nil || decl.Type == nil || decl.Measured != nil {
			continue
		}
		name := decl.Name.Value
		if _, isConst := constants[name]; isConst || !mutated[name] || targetConstants[name] {
			continue
		}
		typeName, isIdent := decl.Type.(*ast.Identifier)
		if !isIdent {
			continue
		}
		global, ok := nativegen.GlobalStorage(typeName.Value)
		if !ok {
			continue
		}
		globals[name] = global
		decls[name] = decl
	}
	return globals, decls
}

func constantGlobals(root *ast.Program, tc *typechecker.TypeChecker) map[string]asm.Constant {
	out := map[string]asm.Constant{}
	if root == nil || tc == nil {
		return out
	}
	eligible := codegen.ConstantScalarGlobals(root)
	env := object.NewEnvironment()
	env.SetArithmeticWidths(tc.ArithmeticType)
	folded := map[string]bool{}
	for _, stmt := range root.Statements {
		decl, isDecl := stmt.(*ast.VariableDeclaration)
		if !isDecl || decl.Name == nil || decl.Type == nil || decl.Value == nil {
			continue
		}
		if !typechecker.IsConstantInitializerIn(decl.Value, folded) {
			continue
		}
		if result := evaluator.Eval(decl, env); result == nil {
			continue
		} else if _, isErr := result.(*object.Error); isErr {
			continue
		}
		folded[decl.Name.Value] = true
		typeName, isIdent := decl.Type.(*ast.Identifier)
		if _, isEligible := eligible[decl.Name.Value]; !isEligible || !isIdent || !constantScalarTypes[typeName.Value] {
			continue
		}
		value, bound := env.Get(decl.Name.Value)
		if !bound {
			continue
		}
		switch v := value.(type) {
		case *object.Integer:
			out[decl.Name.Value] = asm.Constant{Type: typeName.Value, Value: uint64(v.Value)}
		case *object.Boolean:
			bit := uint64(0)
			if v.Value {
				bit = 1
			}
			out[decl.Name.Value] = asm.Constant{Type: typeName.Value, Value: bit}
		}
	}
	return out
}
