package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
)

func nativeLoopResultHomesFixedProgram(width string, length, trips int) string {
	elements := make([]string, length)
	elements[0] = "seed"
	for i := 1; i < length; i++ {
		elements[i] = fmt.Sprintf("%d", i+1)
	}
	return fmt.Sprintf(`
cached: (seed: %[1]s): [%[2]d]%[1]s {
  v: [%[2]d]%[1]s = [%[2]d]%[1]s{ %[3]s }
  i: %[1]s = 0
  while i < %[1]s(%[4]d) {
    v[0] = (v[0] + v[1]) ^ (seed + i)
    v[1] = (v[1] + v[0]) ^ (seed + %[1]s(3))
    i = i + %[1]s(1)
  }
  k: %[1]s = seed & %[1]s(%[5]d)
  v[k] = v[k] ^ v[0]
  v
}
`, width, length, strings.Join(elements, ", "), trips, length-1)
}

func nativeLoopResultFunction(t *testing.T, program string) (*ast.FunctionStatement, map[string]*ast.FunctionStatement, map[string]bool, *SemanticModel) {
	t.Helper()
	model, err := New().WithSource("loop_result_homes.oak", program).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	functions := map[string]*ast.FunctionStatement{}
	symbols := map[string]bool{}
	for _, statement := range model.Tree.Root.Statements {
		if fn, ok := statement.(*ast.FunctionStatement); ok {
			functions[fn.Name.Value] = fn
			symbols[fn.Name.Value] = true
		}
	}
	if functions["cached"] == nil {
		t.Fatal("missing cached source")
	}
	return functions["cached"], functions, symbols, model
}

func compileLoopResultHomes(t *testing.T, program string, enabled bool) (*asm.Function, *ast.FunctionStatement) {
	t.Helper()
	source, functions, symbols, model := nativeLoopResultFunction(t, program)
	original := source.Body.String()
	body, err := nativegen.CompileFor(nativegen.Lane{
		Arch: asm.ArchArm64, NoReductions: true, LoopResultHomes: enabled,
	}, source, functions, nil, nil, nil, model.TypeChecker)
	if err != nil {
		t.Fatal(err)
	}
	body.Callees = functions
	if source.Body.String() != original || body.Body != nil {
		t.Fatal("result-home promotion changed its verification reference")
	}
	wantHomes := 0
	if enabled {
		wantHomes = 2
	}
	if got := nativegen.LoopResultHomes(body); got != wantHomes {
		t.Fatalf("enabled=%v, result homes=%d, want %d", enabled, got, wantHomes)
	}
	if got := nativegen.LoopArrayHomes(body); got != 0 {
		t.Fatalf("result storage acquired %d private-frame homes", got)
	}
	if len(nativegen.FrameObjects(body)) != 0 {
		t.Fatalf("result array retained frame storage: %+v", nativegen.FrameObjects(body))
	}
	if findings := asm.Check(body, source, symbols); len(findings) != 0 {
		t.Fatalf("candidate checker: %v", findings)
	}
	if verdict := asm.Verify(body, source, source.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("enabled=%v: %s (%s)", enabled, verdict.Kind, verdict.Message)
	}
	return body, source
}

func TestNativeLoopResultHomesAgainstOriginal(t *testing.T) {
	for _, test := range []struct {
		width  string
		length int
	}{
		{"u32", 16},
		{"u64", 8},
	} {
		for _, trips := range []int{0, 1, 3} {
			t.Run(fmt.Sprintf("%s/%d", test.width, trips), func(t *testing.T) {
				program := nativeLoopResultHomesFixedProgram(test.width, test.length, trips)
				compileLoopResultHomes(t, program, false)
				compileLoopResultHomes(t, program, true)
			})
		}
	}
}

func TestNativeLoopResultHomesWrongFlushIsRefuted(t *testing.T) {
	body, source := compileLoopResultHomes(t, nativeLoopResultHomesFixedProgram("u32", 16, 1), true)
	changed := *body
	changed.Items = append([]asm.Item(nil), body.Items...)
	seenExit, removed := false, false
	for i, item := range changed.Items {
		if label, ok := item.(asm.Label); ok && strings.HasPrefix(label.Name, "done_") {
			seenExit = true
			continue
		}
		ins, ok := item.(asm.Instruction)
		if !seenExit || !ok || ins.Mnemonic != "str" || len(ins.Operands) != 2 {
			continue
		}
		memory, ok := ins.Operands[1].(asm.Memory)
		if !ok || memory.Base.Num != 8 {
			continue
		}
		changed.Items = append(changed.Items[:i], changed.Items[i+1:]...)
		removed = true
		break
	}
	if !removed {
		t.Fatal("fixture did not expose a result-home exit flush")
	}
	if verdict := asm.Verify(&changed, source, source.Body); verdict.Kind != asm.VerdictMismatch {
		t.Fatalf("deleted result flush must be refuted, got %s: %s", verdict.Kind, verdict.Message)
	}
}

const nativeLoopResultHomesRuntimeProgram = `
cached: (input: [16]u32, seed: u32, count: u32): [16]u32 {
  v: [16]u32 = input
  n: u32 = count & u32(7)
  i: u32 = 0
  while i < n {
    v[0] = (v[0] + v[1]) ^ (seed + i)
    v[1] = (v[1] + input[0]) ^ (v[0] + n)
    i = i + u32(1)
  }
  v
}

main: (): i32 {
  words: [16]u32 = [16]u32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 }
  acc: u32 = 0
  n: u32 = 0
  while n < u32(8) {
    words = cached(words, u32(23) + n, n)
    acc = ((acc * u32(31)) ^ words[0]) + words[1] + words[15]
    n = n + u32(1)
  }
  i32_bits_u32(acc & u32(255))
}
`

func TestE2ENativeLoopResultHomes(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_NATIVE_LOOP_RESULT_HOMES", "1")
	t.Setenv("OAK_OPT_SKIP", strings.Join([]string{
		nativegen.TransformElide, nativegen.TransformHoist, nativegen.TransformRotate,
		nativegen.TransformSchedule, nativegen.TransformReallocate, nativegen.TransformUnrollConst,
		nativegen.TransformLoopArrayHomes,
	}, ","))
	comp := New().WithSource("loop_result_homes.oak", nativeLoopResultHomesRuntimeProgram)
	nativeComp := comp.WithNativeBodies().WithNativeAsm()
	nativeComp.options.InlineHelpers = true
	model, err := nativeComp.SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	selected := false
	for _, fn := range model.AsmFunctions {
		if fn.Name == "cached" && nativegen.LoopResultHomes(fn) > 0 {
			selected = true
		}
	}
	verdict := model.NativeVerdicts["cached"]
	if !selected || (verdict.Kind != asm.VerdictProven && verdict.Kind != asm.VerdictWitnessed) {
		t.Fatalf("cached result-home candidate: selected=%v verdict=%s (%s)", selected, verdict.Kind, verdict.Message)
	}
	_, native, abnormal := buildAndRunFrom(t, "loop_result_homes", nativeComp)
	_, viaC, abnormalC := buildAndRunFrom(t, "loop_result_homes_c", comp)
	if abnormal || abnormalC || native != viaC {
		t.Fatalf("dynamic counts and input snapshot: native=%d (%v), C=%d (%v)", native, abnormal, viaC, abnormalC)
	}
}
