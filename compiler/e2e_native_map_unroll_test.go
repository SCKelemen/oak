package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
)

// Exercise the wider candidate independently of profitability, including
// in-place maps, integer widths, strict floats, nested FMA and zipped inputs.
func TestNativeUnrolledMapCandidatesProve(t *testing.T) {
	for _, source := range []string{nativeFMAMaps, nativeVectorMapProgram} {
		model, err := New().WithSource("map_candidates.oak", source).Check().Get()
		if err != nil {
			t.Fatal(err)
		}
		functions := map[string]*ast.FunctionStatement{}
		for _, stmt := range model.Tree.Root.Statements {
			if fn, ok := stmt.(*ast.FunctionStatement); ok {
				functions[fn.Name.Value] = fn
			}
		}
		for name, fn := range functions {
			if name == "main" {
				continue
			}
			t.Run(name, func(t *testing.T) {
				original := fn.Body.String()
				lane := nativegen.Lane{Arch: asm.ArchArm64, VectorMaps: true, UnrollVectorMaps: true, NoReductions: true, ElideProven: true, HoistInvariants: true, RotateLoops: true, VectorHomes: true, Strength: true}
				unit, err := nativegen.CompileFor(lane, fn, functions, nil, nil, nil, model.TypeChecker)
				if err != nil {
					t.Fatal(err)
				}
				if nativegen.UnrolledMaps(unit) != 1 {
					t.Fatal("wider candidate fell back before verification")
				}
				if findings := asm.CheckWithFacts(unit, fn, nil, model.TypeChecker.IndexProofs()); len(findings) != 0 {
					t.Fatalf("wider candidate not admitted: %v", findings)
				}
				verdict := asm.Verify(unit, fn, verifiedBody(unit, fn))
				if verdict.Kind != asm.VerdictProven {
					t.Fatalf("wider candidate not proven: %+v", verdict)
				}
				stores := 0
				for _, ins := range mainLoopOf(unit) {
					if ins.Mnemonic == "str" {
						if reg, ok := ins.Operands[0].(asm.Register); ok && reg.Vec == "q" {
							stores++
						}
					}
					if name == "fadd_k" && (ins.Mnemonic == "fmla" || ins.Mnemonic == "fmadd") {
						t.Fatal("grouping contracted strict arithmetic")
					}
				}
				if stores != 2 {
					t.Fatalf("got %d vector stores per main trip, want 2", stores)
				}
				// Reuse the very same AST/checker with a different grouping:
				// the rewrite cache must not return the earlier wider stage.
				lane.UnrollVectorMaps = false
				plain, err := nativegen.CompileFor(lane, fn, functions, nil, nil, nil, model.TypeChecker)
				if err != nil {
					t.Fatal(err)
				}
				if nativegen.UnrolledMaps(plain) != 0 || nativegen.VectorizedMaps(plain) != 1 {
					t.Fatal("single-vector configuration reused a grouped rewrite")
				}
				if fn.Body.String() != original {
					t.Fatal("map rewriting mutated checked source")
				}
			})
		}
	}
}

func TestE2ENativeUnrolledMapInPlaceAndMismatchedLengths(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "map64,inplace")
	map64 := nativeFMAMaps[strings.Index(nativeFMAMaps, "map64:"):strings.Index(nativeFMAMaps, "nested:")]
	for _, length := range []int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 17} {
		t.Run(fmt.Sprint(length), func(t *testing.T) {
			values := make([]string, length)
			for i := range values {
				values[i] = fmt.Sprintf("%d.0", i)
			}
			source := map64 + fmt.Sprintf(`
inplace: (v: [*]f64, k: f64, c: f64): () {
  i: u32 = u32(0)
  while i < len(v) {
    v[i] = fma(v[i], k, c)
    i = i + u32(1)
  }
}
main: (): i32 {
  values: [%d]f64 = [%d]f64{%s}
  sentinel: [18]f64 = [18]f64{7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0,7.0}
  map64(span(&sentinel), view(&values), 2.0, 1.0)
  i: u32 = u32(0)
  while i < len(sentinel) {
    assert(sentinel[i] == 7.0)
    i = i + u32(1)
  }
  inplace(span(&values), 2.0, 1.0)
  j: u32 = u32(0)
  while j < len(values) {
    assert(values[j] == f64_round_u32(j) * 2.0 + 1.0)
    j = j + u32(1)
  }
  i32(42)
}
`, length, length, strings.Join(values, ","))
			comp := New().WithSource("map_inplace.oak", source).WithNativeBodies().WithNativeAsm()
			model, err := comp.Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			seen := 0
			for _, unit := range model.AsmFunctions {
				if unit.Name == "map64" || unit.Name == "inplace" {
					seen++
					if nativegen.UnrolledMaps(unit) != 1 || model.NativeVerdicts[unit.Name].Kind != asm.VerdictProven {
						t.Fatalf("%s not proven/grouped", unit.Name)
					}
				}
			}
			if seen != 2 {
				t.Fatalf("got %d native kernels, want 2", seen)
			}
			if _, code, abnormal := buildAndRunFrom(t, "map_inplace", comp); abnormal || code != 42 {
				t.Fatalf("exit=%d abnormal=%v", code, abnormal)
			}
		})
	}
}
