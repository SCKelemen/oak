package compiler

import (
	"fmt"
	"os"
	"reflect"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/opt"
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
func (comp Compilation) lowerNativeBodies(root *ast.Program, tc *typechecker.TypeChecker) nativeLowering {
	var diagnostics []*diagnostic.Diagnostic
	result := nativeLowering{Verdicts: map[string]asm.Verdict{}, Fallbacks: map[string]string{}}
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
				// (nativegen.VectorContractSuffix, RVVContractSuffix): a
				// call target too.
				symbols[nativegen.NativeSymbolFor(comp.options.Target.AsmArch(), fn)] = true
			}
		}
	}
	specializeInstantiations(tc, templates, records, adts)
	declarations := programDeclarations(root)
	verified, fromCache := 0, 0 // the verdict cache's tally, reported once
	constants := constantGlobals(root, tc)
	globals, aggregates, globalDecls := addressableGlobals(root, tc, constants, records)
	tables, data := nativeGlobalArrays(root)
	// The verdict cache (compiler/verdict_cache.go), the optimization
	// report (opt.Report; printed under -opt-report or OAK_OPT_REPORT), and
	// the lane's candidate search, shared by every body.
	cacheDir := verdictCacheDir()
	if comp.options.VerifyFresh {
		cacheDir = ""
	}
	report := &opt.Report{}
	search := nativeSearch(comp.options.Target.AsmArch(), report)
	var lowered []*asm.Function
	for _, stmt := range root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.Body == nil || fn.AsmBacked || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 {
			continue
		}
		// A function with a dispatch clause (docs/spec/93-simd.md §6) is the
		// selection between its realizations, decided once at startup by
		// the processor's probed features; its Oak body is only the
		// portable one. The C backend emits that selection, so the function
		// stays there: lowering the body natively would define the symbol
		// as the portable realization and leave the hardware unit
		// unreachable (measured on CRC-32C: 23x behind the C backend,
		// benchmarks/native/README.md). Its callers lower as usual and
		// call the C backend's dispatching definition.
		if len(fn.Dispatch) > 0 {
			slots := make([]string, 0, len(fn.Dispatch))
			for _, slot := range fn.Dispatch {
				slots = append(slots, slot.Feature)
			}
			reason := fmt.Sprintf("it dispatches on %s; the C backend keeps the selection between its realizations", strings.Join(slots, ", "))
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s left to the C backend (%s)", fn.Name.Value, reason)))
			result.Fallbacks[fn.Name.Value] = reason
			continue
		}
		// A read of a constant top-level scalar (the OS pilot's N1:
		// `page_size`, `entries`) reaches the backend and the verifier as
		// its folded value (constants); the C emitter keeps the body and
		// its `static const`.
		source := fn
		lane := nativegen.Lane{Arch: comp.options.Target.AsmArch(), SoftFloat: comp.options.Target.Freestanding() && comp.options.Target.Arch == target.ArchRiscv64, Tables: tables, PackedStackArgs: comp.options.Target.OS == target.OSDarwin}
		// The processor decides the rv64 lane's vector lowering: the fixed
		// simd vectors need V (docs/spec/93-simd.md §1.4, 94-assembler.md §9).
		lane.Vector = comp.options.Target.Arch == target.ArchRiscv64 && comp.options.Target.CPUFeatures(comp.options.CPU)["v"]
		// The lane's transforms — check elision, strength reduction, compare
		// reuse, loop-invariant motion, reduction unrolling — are the candidate
		// search's to turn on (nativegen.Transforms, below), not the lane's.
		lane.Globals = globals
		lane.Aggregates = aggregates
		// The candidate search (compiler/native_search.go, package opt;
		// docs/notes/optimizer-search-2026-09.md): the plain lowering is the
		// identity candidate, the lane's transforms — check elision, strength
		// reduction, compare reuse, loop-invariant motion, reduction
		// unrolling (nativegen.Transforms) — propose configurations from it,
		// the seam checker and the verifier judge each, and the cheapest
		// proven body is kept, else the strongest verdict, the plain lowering
		// last. A refused or weaker form is reported as set aside.
		driver := &nativeDriver{source: source, functions: functions, records: records, adts: adts, constants: constants, tc: tc, symbols: symbols, declarations: declarations, cacheDir: cacheDir, verdicts: map[*asm.Function]asm.Verdict{}, verified: &verified, fromCache: &fromCache}
		facts := nativegen.FunctionFacts(source, tc)
		selection, err := search.Run(fn.Name.Value, opt.Identity(nativegen.PlainLane(lane)), facts, driver)
		if err != nil {
			if _, outside := err.(nativegen.Unsupported); outside {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s left to the C backend (%v)", fn.Name.Value, err)))
				result.Fallbacks[fn.Name.Value] = err.Error()
				continue
			}
			diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
			continue
		}
		asmFn := selection.Candidate.Body.(*asm.Function)
		chosen := selection.Candidate.Config.(nativegen.Lane)
		if os.Getenv("OAK_NATIVE_DUMP") != "" {
			// A debugging aid: the lowered assembly of every function, as the
			// checker sees it.
			fmt.Fprint(os.Stderr, nativegen.Describe(asmFn))
		}
		if selection.Verdict.Outcome == opt.Refused {
			for _, finding := range selection.Verdict.Findings {
				diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: the checker refuses the lowering of %s: %s", fn.Name.Value, finding)))
			}
			continue
		}
		for _, reason := range setAsideReasons(report, fn.Name.Value, selection.Candidate) {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", "native backend: "+reason))
		}
		if elided := nativegen.ElidedGuards(asmFn); elided > 0 {
			if kept := nativegen.GuardLinesKept(chosen); len(kept) > 0 {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d element guard(s) elided under the checker's own facts, the guards of line(s) %s kept (the checker did not admit their elided form)", fn.Name.Value, elided, joinLines(kept))))
			} else {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d element guard(s) elided under the checker's own facts", fn.Name.Value, elided)))
			}
		}
		verdict := driver.verdicts[asmFn]
		if kept := nativegen.VectorHomes(asmFn); kept > 0 && verdict.Kind == asm.VerdictProven {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d vector local(s) kept in registers across calls", fn.Name.Value, kept)))
		} else if homed := nativegen.LeafVectorHomes(asmFn); homed > 0 && verdict.Kind == asm.VerdictProven {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d vector local(s) homed in the argument registers", fn.Name.Value, homed)))
		}
		if reduced := nativegen.Reduced(asmFn); reduced > 0 && verdict.Kind == asm.VerdictProven {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d constant operation(s) strength-reduced, proven", fn.Name.Value, reduced)))
		}
		if verdict.Kind == asm.VerdictMismatch {
			diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", "native backend: "+verdict.Message))
			continue
		}
		diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", "native backend: "+verdict.Message))
		result.Verdicts[fn.Name.Value] = verdict
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
					result.Fallbacks[fn.Name.Value] = fmt.Sprintf("it passes vectors to %s, which the C backend realizes", callee)
					delete(result.Verdicts, fn.Name.Value)
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
	if verified > 0 {
		// The verdict cache's tally: how many of the verified bodies kept a
		// verdict from an earlier build under the same key.
		diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %d of %d verdicts from the verdict cache", fromCache, verified)))
	}
	if comp.options.OptReport || os.Getenv("OAK_OPT_REPORT") != "" {
		fmt.Fprint(os.Stderr, report.String())
	}
	result.Report = report
	result.Functions, result.Data, result.Diagnostics = lowered, data, diagnostics
	return result
}

// nativeLowering is what the native backend made of a program: the
// lowered functions and their constant tables, each lowered body's
// verdict by Oak name, each body left to the C backend with the reason,
// and the diagnostics that say the same in prose.
type nativeLowering struct {
	Functions   []*asm.Function
	Data        []asm.DataSymbol
	Verdicts    map[string]asm.Verdict
	Fallbacks   map[string]string
	Diagnostics []*diagnostic.Diagnostic
	// Report is the optimization report: what the candidate search tried,
	// kept, and set aside for each body, with the facts that licensed it.
	Report *opt.Report
}

// nativeGlobalArrays collects the program's constant tables: top-level
// arrays of fixed-width integers with literal initializers that no
// statement writes — no assignment, no element assignment, no mutable
// borrow (`span(&t)`, `&t` outside `view`). A native body reads one through
// its data symbol (nativegen.GlobalArray), and the object carries the bytes
// in its read-only data section (docs/spec/94-assembler.md §9, constant
// tables). The C backend keeps its own `static const` copy for the bodies
// it realizes; the two never alias, both being constant.
func nativeGlobalArrays(root *ast.Program) (map[string]nativegen.GlobalArray, []asm.DataSymbol) {
	if root == nil {
		return nil, nil
	}
	mutated := mutatedTables(root)
	tables := map[string]nativegen.GlobalArray{}
	var data []asm.DataSymbol
	for _, stmt := range root.Statements {
		decl, isDecl := stmt.(*ast.VariableDeclaration)
		if !isDecl || decl.Name == nil || decl.Section != "" || mutated[decl.Name.Value] {
			continue
		}
		table, bytes, ok := nativegen.GlobalArrayOf(decl)
		if !ok {
			continue
		}
		tables[decl.Name.Value] = table
		data = append(data, asm.DataSymbol{Name: table.Symbol, Bytes: bytes, Align: table.ElemSize()})
	}
	return tables, data
}

// mutatedTables names every top-level identifier some statement may write:
// the target of an assignment or element assignment, or the operand of a
// borrow `&x` that is not the argument of `view(...)` (a shared borrow).
func mutatedTables(program *ast.Program) map[string]bool {
	mutated := map[string]bool{}
	var walk func(v reflect.Value, shared bool)
	walk = func(v reflect.Value, shared bool) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			switch node := v.Interface().(type) {
			case *ast.AssignmentStatement:
				if node.Name != nil {
					mutated[node.Name.Value] = true
				}
			case *ast.IndexAssignmentStatement:
				if root, ok := pathRoot(node.Target); ok {
					mutated[root] = true
				}
			case *ast.InvocationExpression:
				if fn, isIdent := node.Function.(*ast.Identifier); isIdent && fn.Value == "view" {
					for _, arg := range node.Arguments {
						walk(reflect.ValueOf(arg), true)
					}
					return
				}
			case *ast.PrefixExpression:
				if node.Operator == "&" && !shared {
					if root, ok := pathRoot(node.Right); ok {
						mutated[root] = true
					}
				}
			}
			walk(v.Elem(), false)
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i), false)
				}
			}
		case reflect.Slice, reflect.Array:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i), false)
			}
		case reflect.Map:
			for _, key := range v.MapKeys() {
				walk(v.MapIndex(key), false)
			}
		}
	}
	walk(reflect.ValueOf(program), false)
	return mutated
}

// pathRoot is the identifier a place expression roots at: `t`, `t[i]`,
// `t.f[i]`, `*t`.
func pathRoot(expr ast.Expression) (string, bool) {
	for {
		switch e := expr.(type) {
		case *ast.Identifier:
			return e.Value, true
		case *ast.IndexExpression:
			expr = e.Left
		case *ast.PrefixExpression:
			expr = e.Right
		default:
			return "", false
		}
	}
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
func addressableGlobals(root *ast.Program, tc *typechecker.TypeChecker, constants map[string]asm.Constant, records map[string]*ast.RecordLiteral) (map[string]asm.Global, map[string]*ast.VariableDeclaration, map[string]*ast.VariableDeclaration) {
	globals := map[string]asm.Global{}
	aggregates := map[string]*ast.VariableDeclaration{}
	decls := map[string]*ast.VariableDeclaration{}
	if root == nil {
		return globals, aggregates, decls
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
		if _, isConst := constants[name]; isConst || targetConstants[name] {
			continue
		}
		// A top-level record, or a written array (an unwritten array is a
		// constant table, nativegen.Lane.Tables): an aggregate the body
		// addresses as a place (the OS pilot's N9).
		if typeName, isIdent := decl.Type.(*ast.Identifier); isIdent {
			if _, isRecord := records[typeName.Value]; isRecord {
				aggregates[name] = decl
				decls[name] = decl
				continue
			}
		} else if index, isIndex := decl.Type.(*ast.IndexExpression); isIndex && !index.Dot {
			if _, isLit := index.Index.(*ast.IntegerLiteral); isLit && mutated[name] {
				aggregates[name] = decl
				decls[name] = decl
			}
			continue
		}
		if !mutated[name] {
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
	return globals, aggregates, decls
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

// joinLines spells the kept lines for the diagnostic.
func joinLines(lines []int) string {
	parts := make([]string, len(lines))
	for i, line := range lines {
		parts[i] = strconv.Itoa(line)
	}
	return strings.Join(parts, ", ")
}

// verifiedBody is the Oak body the verifier judges a lowering against: the
// body the lowering realized when it rewrote the source's (a verified
// rewrite, asm.Function.Body), else the source's.
func verifiedBody(asmFn *asm.Function, source *ast.FunctionStatement) ast.Expression {
	if asmFn.Body != nil {
		return asmFn.Body
	}
	return source.Body
}
