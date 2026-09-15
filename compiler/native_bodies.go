package compiler

import (
	"fmt"
	"os"
	"reflect"
	"strconv"
	"strings"
	"time"

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
		// Check elision (docs/spec/94-assembler.md §9): an element access the
		// typechecker proved in range is lowered without its guard first;
		// if the seam checker cannot admit the body from the facts on the
		// path, the body is lowered again with every guard. The checker
		// decides safety; the elision is only what it already knows.
		lane.ElideProven = lane.Arch == asm.ArchArm64
		// Strength reduction (docs/spec/90-backend.md §16): constant
		// multiplications, divisions, and remainders as shifts, masks, and
		// untested divisions; the checker and the verifier decide, and a
		// refusal or a lost proof lowers the body again without it.
		lane.Strength = lane.Arch == asm.ArchArm64
		// Vector homes across calls (docs/spec/94-assembler.md §9.ad): a
		// calling function's vector locals in v16–v31, saved around a call
		// only when live after it; the checker and the verifier decide.
		lane.VectorHomes = lane.Arch == asm.ArchArm64
		// Compare reuse across a conditional chain (docs/spec/94-assembler.md
		// §9 "Condition selection"): the checker carries flags across a
		// label every predecessor reaches with them, or the body lowers
		// again without the reuse.
		lane.ReuseFlags = lane.Arch == asm.ArchArm64
		// Loop-invariant code motion (§9 "Loop invariants"): hoisted
		// values, propagated copies, peeled guards; the checker judges the
		// result, or the body lowers again with its loops as written.
		lane.HoistInvariants = lane.Arch == asm.ArchArm64
		lane.Globals = globals
		lane.Aggregates = aggregates
		asmFn, err := nativegen.CompileFor(lane, source, functions, records, adts, constants, tc)
		if err != nil {
			if _, outside := err.(nativegen.Unsupported); outside {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s left to the C backend (%v)", fn.Name.Value, err)))
				result.Fallbacks[fn.Name.Value] = err.Error()
				continue
			}
			diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
			continue
		}
		findings := asm.Check(asmFn, source, symbols)
		// A refused elision falls back one source line at a time
		// (docs/spec/94-assembler.md §9 "Check elision"): the finding
		// names the line of the access the checker could not admit, that
		// line's accesses keep their guards, and the body is lowered
		// again, so the accesses the checker does admit stay elided. A
		// finding without a line, or a line already kept, or the eighth
		// round, falls back to every guard as before.
		var kept []int
		for round := 0; len(findings) != 0 && lane.ElideProven && nativegen.ElidedGuards(asmFn) > 0; round++ {
			if os.Getenv("OAK_NATIVE_DUMP") != "" {
				// The refused form, for reading the checker's gap
				// (docs/spec/94-assembler.md §9.ad).
				fmt.Fprintf(os.Stderr, "// refused elided form of %s (round %d): %s\n%s", fn.Name.Value, round, findings[0], nativegen.Describe(asmFn))
			}
			line, hasLine := findingLine(findings[0], fn.Name.Value)
			if round >= 8 || !hasLine || lane.GuardLines[line] {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its element guards (the checker did not admit the elided form: %s)", fn.Name.Value, findings[0])))
				lane.ElideProven = false
				lane.GuardLines = nil
				kept = nil
			} else {
				if lane.GuardLines == nil {
					lane.GuardLines = map[int]bool{}
				}
				lane.GuardLines[line] = true
				kept = append(kept, line)
			}
			asmFn, err = nativegen.CompileFor(lane, source, functions, records, adts, constants, tc)
			if err != nil {
				break
			}
			findings = asm.Check(asmFn, source, symbols)
		}
		if err != nil {
			diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
			continue
		}
		if elided := nativegen.ElidedGuards(asmFn); elided > 0 && len(findings) == 0 {
			if len(kept) > 0 {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d element guard(s) elided under the checker's own facts, the guards of line(s) %s kept (the checker did not admit their elided form)", fn.Name.Value, elided, joinLines(kept))))
			} else {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d element guard(s) elided under the checker's own facts", fn.Name.Value, elided)))
			}
		}
		if len(findings) != 0 && lane.HoistInvariants && nativegen.Hoisted(asmFn) > 0 {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its loop invariants in place (the checker did not admit the hoisted form: %s)", fn.Name.Value, findings[0])))
			lane.HoistInvariants = false
			asmFn, err = nativegen.CompileFor(lane, source, functions, records, adts, constants, tc)
			if err != nil {
				diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
				continue
			}
			findings = asm.Check(asmFn, source, symbols)
		}
		if len(findings) != 0 && lane.ReuseFlags && nativegen.ReusedCompares(asmFn) > 0 {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s repeats its compares (the checker did not admit the reused form: %s)", fn.Name.Value, findings[0])))
			lane.ReuseFlags = false
			asmFn, err = nativegen.CompileFor(lane, source, functions, records, adts, constants, tc)
			if err != nil {
				diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
				continue
			}
			findings = asm.Check(asmFn, source, symbols)
		}
		if len(findings) != 0 && lane.VectorHomes && nativegen.VectorHomes(asmFn)+nativegen.LeafVectorHomes(asmFn) > 0 {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its vector slots (the checker did not admit the vector homes: %s)", fn.Name.Value, findings[0])))
			lane.VectorHomes = false
			asmFn, err = nativegen.CompileFor(lane, source, functions, records, adts, constants, tc)
			if err != nil {
				diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
				continue
			}
			findings = asm.Check(asmFn, source, symbols)
		}
		if len(findings) != 0 && lane.Strength && nativegen.Reduced(asmFn) > 0 {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its plain arithmetic (the checker did not admit the strength-reduced form: %s)", fn.Name.Value, findings[0])))
			lane.Strength = false
			asmFn, err = nativegen.CompileFor(lane, source, functions, records, adts, constants, tc)
			if err != nil {
				diagnostics = append(diagnostics, diagnostic.NewDiagnostic(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %v", fn.Name.Value, err)))
				continue
			}
			findings = asm.Check(asmFn, source, symbols)
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
		verifyStart := time.Now()
		// The verdict cache (compiler/verdict_cache.go): a body verified
		// before under the same key — the same assembly, Oak body, reachable
		// callees, declarations, and compiler — keeps its verdict.
		cacheDir := verdictCacheDir()
		if comp.options.VerifyFresh {
			cacheDir = ""
		}
		cacheKey := ""
		if cacheDir != "" {
			cacheKey = verdictCacheKey(asmFn, source, functions, declarations)
		}
		verdict, cached := cachedVerdict(cacheDir, cacheKey)
		if !cached {
			verdict = asm.Verify(asmFn, source, verifiedBody(asmFn, source))
			storeVerdict(cacheDir, cacheKey, verdict)
		} else {
			fromCache++
		}
		verified++
		if asmFn.Body != nil && verdict.Kind != asm.VerdictProven {
			// The unrolled reduction did not prove (nativegen/reduction.go):
			// the loop as written is lowered and verified too, and kept
			// when its verdict is the stronger — a faster body is not
			// worth a weaker verdict.
			plainLane := lane
			plainLane.NoReductions = true
			if plain, plainErr := nativegen.CompileFor(plainLane, source, functions, records, adts, constants, tc); plainErr == nil && len(asm.Check(plain, source, symbols)) == 0 {
				plain.Callees = functions
				plainKey := ""
				if cacheDir != "" {
					plainKey = verdictCacheKey(plain, source, functions, declarations)
				}
				plainVerdict, plainCached := cachedVerdict(cacheDir, plainKey)
				if !plainCached {
					plainVerdict = asm.Verify(plain, source, verifiedBody(plain, source))
					storeVerdict(cacheDir, plainKey, plainVerdict)
				}
				if verdictRank(plainVerdict.Kind) > verdictRank(verdict.Kind) {
					diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its plain reduction (the verifier judged it %s and the unrolled form %s: %s)", fn.Name.Value, plainVerdict.Kind, verdict.Kind, verdict.Message)))
					asmFn, verdict = plain, plainVerdict
				}
			}
		}
		if verdict.Kind != asm.VerdictProven && lane.VectorHomes && nativegen.VectorHomes(asmFn)+nativegen.LeafVectorHomes(asmFn) > 0 {
			// The body with vector homes did not prove: the slot form is
			// lowered and verified too, and kept when it proves.
			slotLane := lane
			slotLane.VectorHomes = false
			if plain, plainErr := nativegen.CompileFor(slotLane, source, functions, records, adts, constants, tc); plainErr == nil && len(asm.Check(plain, source, symbols)) == 0 {
				plain.Callees = functions
				plainKey := ""
				if cacheDir != "" {
					plainKey = verdictCacheKey(plain, source, functions, declarations)
				}
				plainVerdict, plainCached := cachedVerdict(cacheDir, plainKey)
				if !plainCached {
					plainVerdict = asm.Verify(plain, source, verifiedBody(plain, source))
					storeVerdict(cacheDir, plainKey, plainVerdict)
				}
				if plainVerdict.Kind == asm.VerdictProven {
					diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its vector slots (the verifier proved them and not the vector homes: %s)", fn.Name.Value, verdict.Message)))
					asmFn, verdict = plain, plainVerdict
					lane.VectorHomes = false
				} else {
					diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its vector homes (neither form proved; the slot form: %s)", fn.Name.Value, plainVerdict.Message)))
				}
			} else if plainErr != nil {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its vector homes (the slot form did not lower: %v)", fn.Name.Value, plainErr)))
			} else {
				diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its vector homes (the checker refused the slot form)", fn.Name.Value)))
			}
		} else if kept := nativegen.VectorHomes(asmFn); kept > 0 && verdict.Kind == asm.VerdictProven {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d vector local(s) kept in registers across calls", fn.Name.Value, kept)))
		} else if homed := nativegen.LeafVectorHomes(asmFn); homed > 0 && verdict.Kind == asm.VerdictProven {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d vector local(s) homed in the argument registers", fn.Name.Value, homed)))
		}
		if verdict.Kind != asm.VerdictProven && lane.Strength && nativegen.Reduced(asmFn) > 0 {
			// The reduced form did not prove: the plain arithmetic is
			// lowered and verified too, and kept when it proves — a
			// faster body is not worth a weaker verdict.
			if plain, plainErr := nativegen.CompileFor(nativegen.Lane{Arch: lane.Arch, SoftFloat: lane.SoftFloat, ElideProven: lane.ElideProven, VectorHomes: lane.VectorHomes, GuardLines: lane.GuardLines, ReuseFlags: lane.ReuseFlags, Globals: lane.Globals, Aggregates: lane.Aggregates, Tables: lane.Tables, PackedStackArgs: lane.PackedStackArgs, Vector: lane.Vector}, source, functions, records, adts, constants, tc); plainErr == nil && len(asm.Check(plain, source, symbols)) == 0 {
				plainKey := ""
				if cacheDir != "" {
					plainKey = verdictCacheKey(plain, source, functions, declarations)
				}
				plainVerdict, plainCached := cachedVerdict(cacheDir, plainKey)
				if !plainCached {
					plainVerdict = asm.Verify(plain, source, verifiedBody(plain, source))
					storeVerdict(cacheDir, plainKey, plainVerdict)
				}
				if plainVerdict.Kind == asm.VerdictProven {
					diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s keeps its plain arithmetic (the verifier proved it and not the strength-reduced form: %s)", fn.Name.Value, verdict.Message)))
					asmFn, verdict = plain, plainVerdict
				}
			}
		} else if reduced := nativegen.Reduced(asmFn); reduced > 0 && verdict.Kind == asm.VerdictProven {
			diagnostics = append(diagnostics, diagnostic.NewInformation(lsp.Range{}, "native", fmt.Sprintf("native backend: %s: %d constant operation(s) strength-reduced, proven", fn.Name.Value, reduced)))
		}
		if os.Getenv("OAK_NATIVE_TIMING") != "" {
			// A profiling aid: how long each body's verification took.
			note := ""
			if cached {
				note = ", cached"
			}
			fmt.Fprintf(os.Stderr, "timing: %s: %.2fs (%s%s)\n", fn.Name.Value, time.Since(verifyStart).Seconds(), verdict.Kind, note)
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

// findingLine reads the source line a seam-checker finding names: the
// checker prefixes every finding with `function:line:` (asm/check.go
// errorf).
func findingLine(finding, function string) (int, bool) {
	rest, hasPrefix := strings.CutPrefix(finding, function+":")
	if !hasPrefix {
		return 0, false
	}
	digits, _, hasColon := strings.Cut(rest, ":")
	if !hasColon {
		return 0, false
	}
	line, err := strconv.Atoi(digits)
	if err != nil || line <= 0 {
		return 0, false
	}
	return line, true
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

// verdictRank orders verdicts by strength: proven, then witnessed
// (evidence), then trusted; a mismatch is the weakest.
func verdictRank(kind asm.VerdictKind) int {
	switch kind {
	case asm.VerdictProven:
		return 3
	case asm.VerdictWitnessed:
		return 2
	case asm.VerdictTrusted:
		return 1
	}
	return 0
}
