package compiler

import (
	"fmt"
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/target"
)

const nativeLoopArrayHomesProgram = `
salt: (x: u32): u32 {
  a: u32 = x
  j: u32 = 0
  while j < u32(3) {
    a = (a + u32(17)) ^ (a << u32(3))
    j = j + u32(1)
  }
  a
}

cached: (seed: u32, count: u32): [16]u32 {
  v: [16]u32 = [16]u32{ seed, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 }
  m: [2]u32 = [2]u32{17, 19}
  n: u32 = count & u32(7)
  i: u32 = 0
  warm: u32 = seed + u32(1)
  v[14] = warm
  while i < n {
    v[0] = salt(v[0]) + v[1]
    v[1] = v[0] ^ (v[1] + seed)
    i != u32(1) ? { v[15] = v[15] + m[0] } | {}
    m = [2]u32{m[1], m[0]}
    i = i + u32(1)
  }
  k: u32 = seed & u32(15)
  v[k] = v[k] ^ v[0]
  [16]u32{v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]}
}

main: (): i32 {
  acc: u32 = 0
  n: u32 = 0
  while n < u32(8) {
    out: [16]u32 = cached(u32(0xFFFFFFF0) + n, n)
    i: u32 = 0
    while i < u32(16) {
      acc = (acc * u32(31)) ^ out[i]
      i = i + u32(1)
    }
    n = n + u32(1)
  }
  i32_bits_u32(acc & u32(255))
}
`

func TestNativeLoopArrayHomesAgainstOriginal(t *testing.T) {
	// Fixed trip counts let the verifier symbolically expand the nonlinear
	// array recurrence. The dynamic-count version is exercised at runtime.
	for _, trips := range []int{0, 1, 3} {
		for _, width := range []string{"u32", "u64"} {
			t.Run(fmt.Sprintf("%s/%d", width, trips), func(t *testing.T) {
				program := strings.Split(nativeLoopArrayHomesProgram, "\nmain:")[0]
				program = strings.Replace(program, "count & u32(7)", fmt.Sprintf("u32(%d)", trips), 1)
				program = strings.ReplaceAll(program, "u32", width)
				testNativeLoopArrayHomesAgainstOriginal(t, program)
			})
		}
	}
}

func testNativeLoopArrayHomesAgainstOriginal(t *testing.T, program string) {
	t.Helper()
	model, err := New().WithSource("loop_array_homes.oak", program).Check().Get()
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
	source := functions["cached"]
	if source == nil {
		t.Fatal("missing source")
	}
	original := source.Body.String()
	for _, enabled := range []bool{false, true} {
		lane := nativegen.Lane{Arch: asm.ArchArm64, NoReductions: true, LoopArrayHomes: enabled}
		body, err := nativegen.CompileFor(lane, source, functions, nil, nil, nil, model.TypeChecker)
		if err != nil {
			t.Fatal(err)
		}
		body.Callees = functions
		if source.Body.String() != original || body.Body != nil {
			t.Fatal("home promotion changed its verification reference")
		}
		if got := nativegen.LoopArrayHomes(body); (got > 0) != enabled {
			t.Fatalf("enabled=%v, homes=%d", enabled, got)
		}
		if findings := asm.Check(body, source, symbols); len(findings) != 0 {
			t.Fatalf("candidate checker: %v", findings)
		}
		if verdict := asm.Verify(body, source, source.Body); verdict.Kind != asm.VerdictProven {
			t.Fatalf("enabled=%v: %s (%s)", enabled, verdict.Kind, verdict.Message)
		}
	}
}

func TestE2ENativeLoopArrayHomes(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_VERIFY_CACHE", "0")
	// Isolate this transform from competing candidates whose unrelated
	// guard/recurrence refusals can consume the search's verification cap.
	// The actual BLAKE3 regression below exercises the full default search.
	t.Setenv("OAK_OPT_SKIP", strings.Join([]string{
		nativegen.TransformElide, nativegen.TransformHoist, nativegen.TransformRotate,
		nativegen.TransformSchedule, nativegen.TransformReallocate, nativegen.TransformUnrollConst,
	}, ","))
	comp := New().WithSource("loop_array_homes.oak", nativeLoopArrayHomesProgram)
	nativeComp := comp.WithNativeBodies().WithNativeAsm()
	nativeComp.options.InlineHelpers = true
	var infos []string
	nativeComp = nativeComp.WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := nativeComp.SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	selected := false
	for _, fn := range model.AsmFunctions {
		if fn.Name == "cached" && nativegen.LoopArrayHomes(fn) > 0 {
			selected = true
		}
	}
	if !selected {
		t.Fatalf("runtime test did not select the loop-home candidate:\n%s", strings.Join(infos, "\n"))
	}
	_, native, abnormal := buildAndRunFrom(t, "loop_array_homes", nativeComp)
	_, viaC, abnormalC := buildAndRunFrom(t, "loop_array_homes_c", comp)
	if abnormal || abnormalC || native != viaC {
		t.Fatalf("zero-trip, call, and post-loop cases: native=%d (%v) C=%d (%v)", native, abnormal, viaC, abnormalC)
	}
}

func TestNativeBlake3LoopArrayHomesCompetition(t *testing.T) {
	t.Setenv("OAK_NATIVE_ONLY", nativeBlake3CompressName)
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	root := nativeBlake3Module(t, [][]byte{nil})
	comp := New().WithPackageDir(root).
		WithTarget(target.Target{OS: target.OSDarwin, Arch: target.ArchArm64}).
		WithNativeBodies().WithNativeAsm()
	comp.options.InlineHelpers = true
	stackCount := func(model *SemanticModel) int {
		t.Helper()
		v := model.NativeVerdicts[nativeBlake3CompressName]
		if v.Kind != asm.VerdictProven || !strings.Contains(v.Message, "all 8 result chunks") {
			t.Fatalf("compressor did not prove: %s (%s)", v.Kind, v.Message)
		}
		for _, fn := range model.AsmFunctions {
			if fn.Name != nativeBlake3CompressName {
				continue
			}
			// Exact trip costs may select the measured fully unrolled
			// profile. Keep its bounds distinct from the rolled fallback.
			requireNativeBlake3StrongProfile(t, fn)
			count := 0
			for _, item := range fn.Items {
				if ins, ok := item.(asm.Instruction); ok && (strings.HasPrefix(ins.Mnemonic, "ld") || strings.HasPrefix(ins.Mnemonic, "st")) {
					for _, operand := range ins.Operands {
						if mem, ok := operand.(asm.Memory); ok && mem.Base.Class == asm.ClassSP {
							count++
						}
					}
				}
			}
			return count
		}
		t.Fatal("missing compressor")
		return 0
	}
	t.Setenv("OAK_OPT_SKIP", nativegen.TransformLoopArrayHomes)
	baseline, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	before := stackCount(baseline)
	t.Setenv("OAK_OPT_SKIP", "")
	candidate, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	after := stackCount(candidate)
	// Other candidates can supersede loop homes: direct result storage is
	// deliberately not a private-frame array, and constant unrolling may
	// eliminate the loop entirely. Do not force a worse production choice.
	if after > before {
		t.Fatalf("stack accesses regressed: %d -> %d", before, after)
	}
	// Run the compiler twice to pin deterministic selection/home ordering.
	repeated, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	if stackCount(repeated) != after {
		t.Fatal("nondeterministic home selection")
	}
	for _, first := range candidate.AsmFunctions {
		if first.Name == nativeBlake3CompressName {
			for _, second := range repeated.AsmFunctions {
				if second.Name == first.Name && !reflect.DeepEqual(first.Items, second.Items) {
					t.Fatal("nondeterministic selected instructions")
				}
			}
		}
	}
}
