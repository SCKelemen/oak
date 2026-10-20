package compiler

import (
	"crypto/sha256"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/stdlib"
	"github.com/SCKelemen/oak/typechecker"
)

// These are source/type/layout regression fixtures, not an acceptance profile
// or a source-to-machine refinement proof. In particular, native lowering is
// inspected directly: neither C fallback nor inlining can satisfy that check.
func statefulCopySource(t *testing.T) string {
	t.Helper()
	b, err := os.ReadFile(filepath.Join("testdata", "stateful_copy", "main.oak"))
	if err != nil {
		t.Fatal(err)
	}
	if got := fmt.Sprintf("%x", sha256.Sum256(b)); got != "b7e0745da1b388e29c281c2f15d89ef4061ab33f1c5eb55f8dda7297d87f95f5" {
		t.Fatalf("frozen caller changed (%s); review the source-closure contract", got)
	}
	return string(b)
}

func statefulCopyCompilation(t *testing.T, source string) Compilation {
	t.Helper()
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/stateful-copy-contract\noak 0.1.0\n",
		"main.oak": source,
	})
	return New().WithPackageDir(root)
}

func statefulCopyDeclarations(model *SemanticModel) (map[string]*ast.FunctionStatement, map[string]*ast.ADTType) {
	functions := map[string]*ast.FunctionStatement{}
	adts := map[string]*ast.ADTType{}
	templates := map[string]*ast.ADTType{}
	for _, statement := range model.Tree.Root.Statements {
		switch s := statement.(type) {
		case *ast.FunctionStatement:
			functions[s.Name.Value] = s
		case *ast.ADTType:
			if len(s.TypeParams) > 0 {
				templates[s.Name.Value] = s
			} else {
				adts[s.Name.Value] = s
			}
		}
	}
	// Use the same specialization authority as compiler/native_bodies.go.
	specializeInstantiations(model.TypeChecker, templates, map[string]*ast.RecordLiteral{}, adts)
	return functions, adts
}

func TestStatefulCopySourceClosure(t *testing.T) {
	for _, dependency := range []struct {
		path, embedded, digest string
	}{
		{"bytes.oak", stdlib.Packages["bytes"], "e4da6755200dbcfe409f9ec11ea928515d7fcd91838ba63e284d1c9f30603f7c"},
		{"std.oak", stdlib.Prelude, "10bbc09408ba76fccbac59f06936411e29eff8b81777c788b2b77b8e57eaa0e7"},
	} {
		disk, err := os.ReadFile(filepath.Join("..", "stdlib", dependency.path))
		if err != nil {
			t.Fatal(err)
		}
		if string(disk) != dependency.embedded || fmt.Sprintf("%x", sha256.Sum256(disk)) != dependency.digest {
			t.Fatalf("frozen dependency %s changed; review the source-closure contract", dependency.path)
		}
	}
	comp := statefulCopyCompilation(t, statefulCopySource(t))
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	info := model.Tree.Modules
	if info == nil || !info.StandardLibrary["bytes"] || model.Tree.Prelude != "core" {
		t.Fatalf("not the qualified stdlib bytes/core-prelude closure: %+v", info)
	}
	if got := info.Imports[info.RootPackage]; !reflect.DeepEqual(got, []string{"bytes"}) {
		t.Fatalf("root imports = %v", got)
	}
	for name, kind := range map[string]modules.MemberKind{"copy_into": modules.KindValue, "CopyError": modules.KindType} {
		member, outcome := modules.Lookup(info.Exports["bytes"], nil, name)
		if outcome != modules.Resolved || member.Kind != kind {
			t.Fatalf("bytes.%s did not resolve with expected kind: %+v %v", name, member, outcome)
		}
	}
	functions, adts := statefulCopyDeclarations(model)
	calleeName, errorName := modules.Mangle("bytes", "copy_into"), modules.Mangle("bytes", "CopyError")
	caller, callee := functions["copy_checked"], functions[calleeName]
	if caller == nil || callee == nil || adts[errorName] == nil {
		t.Fatal("missing resolved caller, real callee, or error type")
	}
	typ, exists := model.TypeChecker.Env().GetType(calleeName)
	sig, ok := typ.(*typechecker.FunctionType)
	if !exists || !ok || len(sig.Parameters) != 2 {
		t.Fatalf("missing checked callee signature: %v", typ)
	}
	if sig.String() != "fn([*]u8, []u8) -> Result[u32, bytes__CopyError]" || sig.Variadic {
		t.Fatalf("changed checked callee signature: %s", sig)
	}
	resultName, ok := asm.TypeApplicationName(callee.ReturnType)
	if !ok || resultName != "Result_u32_"+errorName {
		t.Fatalf("callee result = %v / %q", callee.ReturnType, resultName)
	}
	result := adts[resultName]
	if result == nil || len(result.Variants) != 2 ||
		result.Variants[0].Name.Value != "Ok" || result.Variants[0].Payload.String() != "u32" ||
		result.Variants[1].Name.Value != "Err" || result.Variants[1].Payload.String() != errorName {
		t.Fatalf("wrong concrete Result declaration: %v", result)
	}
	body := caller.Body.(*ast.BlockExpression).Block.Statements
	if len(body) != 3 {
		t.Fatalf("caller changed: %s", caller.Body.String())
	}
	n := body[0].(*ast.VariableDeclaration)
	copied := body[1].(*ast.VariableDeclaration)
	call, ok := copied.Value.(*ast.InvocationExpression)
	if !ok || call.Function.String() != calleeName || n.Name.Value != "n" ||
		n.Value.String() != "len(src)" || len(call.Arguments) != 2 ||
		call.Arguments[0].String() != "dst" || call.Arguments[1].String() != "src" ||
		!strings.Contains(body[2].String(), "(count == n)") {
		t.Fatalf("caller lost direct call or caller-live observation: %s", caller.Body.String())
	}
	// Compare the qualified callee with the actual dependency's parsed body,
	// not only its name or hash. This body has no qualified free references.
	p := parser.New(layout.New(scanner.New(stdlib.Packages["bytes"])))
	original := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatal(p.Errors())
	}
	var originalCopy *ast.FunctionStatement
	for _, statement := range original.Statements {
		if f, ok := statement.(*ast.FunctionStatement); ok && f.Name.Value == "copy_into" {
			originalCopy = f
		}
	}
	if originalCopy == nil || callee.Body.String() != originalCopy.Body.String() {
		t.Fatal("resolved callee body differs from the actual stdlib definition")
	}
	t.Logf("resolved %s : %s; concrete result %s; caller %s", calleeName, sig, resultName, caller.Body.String())
}

func TestStatefulCopyConcreteLayoutAndNativeCall(t *testing.T) {
	model, err := statefulCopyCompilation(t, statefulCopySource(t)).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	functions, adts := statefulCopyDeclarations(model)
	calleeName, errorName := modules.Mangle("bytes", "copy_into"), modules.Mangle("bytes", "CopyError")
	resultName, _ := asm.TypeApplicationName(functions[calleeName].ReturnType)
	composites := nativegen.Composites(nil, adts)
	wantError := asm.Composite{Size: 4, Fields: []asm.CompositeField{{Name: "tag", Size: 4, Scalar: "u32"}}, Variants: map[string]int64{"DestinationTooSmall": 0}}
	wantResult := asm.Composite{
		Size: 8,
		Fields: []asm.CompositeField{
			{Name: "tag", Size: 4, Scalar: "u32"},
			{Name: "Ok", Offset: 4, Size: 4, Scalar: "u32"},
			{Name: "Err", Offset: 4, Size: 4, Type: errorName},
		},
		Variants: map[string]int64{"Ok": 0, "Err": 1},
	}
	if !reflect.DeepEqual(composites[errorName], wantError) || !reflect.DeepEqual(composites[resultName], wantResult) {
		t.Fatalf("concrete layout changed: error=%+v result=%+v", composites[errorName], composites[resultName])
	}
	rep, err := semir.TaggedUnionLayout([]semir.RecordFieldRepresentation{
		{Name: "Ok", Size: 4, Alignment: 4}, {Name: "Err", Size: 4, Alignment: 4},
	})
	if err != nil || rep.Size != 8 || rep.Alignment != 4 || rep.Tag.Offset != 0 || rep.Fields[1].Offset != 4 {
		t.Fatalf("Result representation = %+v, %v", rep, err)
	}
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
		t.Run(arch, func(t *testing.T) {
			for _, name := range []string{"copy_checked", calleeName} {
				fn, err := nativegen.CompileFor(nativegen.Lane{Arch: arch}, functions[name], functions, nil, adts, nil, model.TypeChecker)
				if err != nil {
					t.Fatalf("direct native lowering of %s: %v", name, err)
				}
				for i, param := range []string{"dst", "src"} {
					wantBase, wantLen := fmt.Sprintf("x%d", i*2), fmt.Sprintf("w%d", i*2+1)
					if arch == asm.ArchRV64 {
						wantBase, wantLen = fmt.Sprintf("a%d", i*2), fmt.Sprintf("a%d", i*2+1)
					}
					found := false
					for _, binding := range fn.Bindings {
						if binding.Param == param && binding.Register.Text == wantBase && binding.Length != nil && binding.Length.Text == wantLen {
							found = true
						}
					}
					if !found {
						t.Fatalf("%s: missing %s=(%s,%s) binding: %+v", name, param, wantBase, wantLen, fn.Bindings)
					}
				}
				code, relocations, err := asm.EncodeFunction(fn)
				if err != nil {
					t.Fatal(err)
				}
				calls := 0
				for _, relocation := range relocations {
					if relocation.Symbol == calleeName {
						kind, width := "call26", 4
						if arch == asm.ArchRV64 {
							kind, width = "riscv_call_plt", 8
						}
						if relocation.Kind != kind || relocation.Offset < 0 || relocation.Offset > len(code)-width {
							t.Fatalf("invalid direct-call relocation: %+v for %d code bytes", relocation, len(code))
						}
						calls++
					}
				}
				if name == "copy_checked" && calls != 1 || name == calleeName && calls != 0 {
					t.Fatalf("%s: actual callee relocations = %d", name, calls)
				}
				// Observe aggregate transport in the production instructions,
				// rather than inferring it solely from the eight-byte layout.
				callOp, loadOp, storeOp, moveOp, resultReg := "bl", "ldr", "str", "mov", "x0"
				byteLoad, byteStore := "ldrb", "strb"
				if arch == asm.ArchRV64 {
					callOp, loadOp, storeOp, moveOp, resultReg = "call", "ld", "sd", "mv", "a0"
					byteLoad, byteStore = "lbu", "sb"
				}
				afterCall, receives, returns, byteReads, byteWrites := false, 0, 0, 0, 0
				for _, item := range fn.Items {
					if ins, ok := item.(asm.Instruction); ok {
						if ins.Mnemonic == callOp {
							afterCall = true
						}
						if ins.Mnemonic == byteLoad {
							byteReads++
						}
						if ins.Mnemonic == byteStore {
							byteWrites++
						}
						if len(ins.Operands) > 0 {
							if register, ok := ins.Operands[0].(asm.Register); ok && register.Text == resultReg {
								if afterCall && ins.Mnemonic == storeOp {
									receives++
								}
								if ins.Mnemonic == loadOp || ins.Mnemonic == moveOp {
									returns++
								}
							}
						}
					}
				}
				if name == "copy_checked" && receives != 1 {
					t.Fatalf("caller did not receive exactly one aggregate chunk from %s: %d", resultReg, receives)
				}
				if name == calleeName && (returns == 0 || byteReads != 1 || byteWrites != 1) {
					t.Fatalf("callee return/byte-access shape: chunks=%d reads=%d writes=%d", returns, byteReads, byteWrites)
				}
				t.Logf("%s: bytes=%d frame=%d relocations=%+v receives=%d returns=%d byteReads=%d byteWrites=%d",
					name, len(code), fn.Frame, relocations, receives, returns, byteReads, byteWrites)
				t.Log(asm.EmitC(fn, name, func(symbol string) string { return symbol }))
			}
		})
	}
}

func TestStatefulCopyCurrentOptIRAndWasmRefusals(t *testing.T) {
	comp := statefulCopyCompilation(t, statefulCopySource(t))
	module, err := comp.OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	callee := modules.Mangle("bytes", "copy_into")
	want := map[string]string{
		"copy_checked": "parameter dst has unsupported type",
		callee:         "return type Result",
	}
	for _, refusal := range module.Refusals {
		if prefix, expected := want[refusal.Function]; expected {
			if !strings.HasPrefix(refusal.Reason, prefix) {
				t.Fatalf("%s: changed refusal: %s", refusal.Function, refusal.Reason)
			}
			t.Logf("%s: %s", refusal.Function, refusal.Reason)
			delete(want, refusal.Function)
		}
	}
	if len(want) != 0 {
		t.Fatalf("expected current OptIR refusals missing: %v", want)
	}
	if _, err := comp.EmitWasm().Get(); err == nil || !strings.Contains(err.Error(), "scalar profile supports function declarations only") {
		t.Fatalf("current Wasm package-declaration refusal changed: %v", err)
	} else {
		t.Log(err)
	}
}

// Finite source semantics checks: arbitrary-input machine theorems remain an
// obligation. Nonempty backing plus offsets keep empty windows observable.
func TestStatefulCopyCallerMemoryFixtures(t *testing.T) {
	var source strings.Builder
	source.WriteString(statefulCopySource(t))
	cases := 0
	for _, d := range []int{0, 1, 3, 5} {
		for _, s := range []int{0, 1, 2, 3, 5} {
			dst := []byte{11, 22, 33, 44, 55, 66, 77}
			src := []byte{81, 0, 128, 255, 17, 240, 82}
			fmt.Fprintf(&source, "\ncheck_%d: (): () {\n dst: [7]u8 = %s\n src: [7]u8 = %s\n", cases, oakU8Array(dst), oakU8Array(src))
			fmt.Fprintf(&source, " observed: Bool = copy_checked(span(&dst)[u32(1):u32(%d)], view(&src)[u32(1):u32(%d)])\n assert(observed == %t)\n", d+1, s+1, s <= d)
			if s <= d {
				copy(dst[1:1+s], src[1:1+s])
			}
			for i := range dst {
				fmt.Fprintf(&source, " assert(dst[%d] == u8(%d))\n assert(src[%d] == u8(%d))\n", i, dst[i], i, src[i])
			}
			source.WriteString("}\n")
			cases++
		}
	}
	fmt.Fprintf(&source, "\ncheck_%d: (): () {\n dst: [1]u8 = [u8(173)]\n src: [1]u8 = [u8(219)]\n assert(copy_checked(span(&dst)[u32(1):u32(1)], view(&src)[u32(1):u32(1)]))\n assert(dst[0] == u8(173))\n assert(src[0] == u8(219))\n}\n", cases)
	cases++
	source.WriteString("\nmain: (): i32 {\n")
	for i := 0; i < cases; i++ {
		fmt.Fprintf(&source, " check_%d()\n", i)
	}
	source.WriteString(" 42\n}\n")
	comp := statefulCopyCompilation(t, source.String())
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if result := evaluator.Eval(model.Tree.Root, env); result != nil {
		if failure, ok := result.(*object.Error); ok {
			t.Fatal(failure.Message)
		}
	}
	call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
	result := evaluator.Eval(call, env)
	integer, ok := result.(*object.Integer)
	if !ok || integer.Value != 42 {
		t.Fatalf("interpreted window fixtures: %v", result)
	}
	code, abnormal := buildPackageAndRun(t, comp)
	if abnormal || code != 42 {
		t.Fatalf("C source correspondence fixtures: exit=%d abnormal=%v", code, abnormal)
	}
	t.Logf("%d offset/capacity cases checked Bool, count-vs-live-length, full destination backing and unchanged source in interpreter and C", cases)
}
