package nativegen

import (
	"fmt"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func TestLeafVectorHomesPreferUnusedArguments(t *testing.T) {
	fn, _, _, _ := checkedFillFunction(t, `mix: (a: simd.U32x4, f: f32, b: simd.U32x4): simd.U32x4 { simd.add_u32x4(a, b) }`, "mix")
	g := generator{
		fn: fn, vectorHomes: true,
		slots: map[string]int64{}, types: map[string]scalar{}, regs: map[string]int{},
		homesUsedV: map[int]bool{},
	}
	g.pushScope()
	// v0, v1, and v2 carry mixed vector/float arguments. All five
	// remaining homes must precede even an already-free callee home.
	g.freeCalleeV = []int{vecBase + 8}
	for i := 0; i < 5; i++ {
		name := fmt.Sprintf("local%d", i)
		g.declare(name, vecShapes["U32x4"])
		if got, want := g.regs[name], vecBase+3+i; got != want {
			t.Fatalf("%s home = %d, want %d", name, got, want)
		}
	}
	if g.usedCalleeV != 0 || len(g.freeCalleeV) != 1 || g.leafVecHomes != 5 {
		t.Fatal("unused argument homes did not precede callee homes")
	}
	g.declare("overflow", vecShapes["U32x4"])
	if g.regs["overflow"] != vecBase+8 {
		t.Fatal("exhausted argument pool did not fall back to existing callee pool")
	}
	for r := vecBase; r < vecBase+3; r++ {
		if g.homesUsedV[r] {
			t.Fatal("incoming argument or result was reused as a home")
		}
	}
}

func TestLeafVectorHomesEligibilityAndReuse(t *testing.T) {
	fn, _, _, _ := checkedFillFunction(t, `leaf: (): u32 { u32(0) }`, "leaf")
	for _, tc := range []struct {
		name            string
		gate, calls, rv bool
		want            int
	}{
		{"enabled", true, false, false, 7},
		{"disabled", false, false, false, 0},
		{"calling", true, true, false, 0},
		{"rv64", true, false, true, 0},
	} {
		t.Run(tc.name, func(t *testing.T) {
			g := generator{fn: fn, vectorHomes: tc.gate, hasCalls: tc.calls, rvLane: tc.rv}
			if got := g.leafVectorPool(); got != tc.want {
				t.Fatalf("pool = %d, want %d", got, tc.want)
			}
			for _, r := range g.leafHomesV {
				if r <= vecBase || r > vecBase+7 {
					t.Fatalf("unsafe leaf home %d", r)
				}
			}
		})
	}
	full, _, _, _ := checkedFillFunction(t, `full: (a: simd.U32x4, b: simd.U32x4, c: simd.U32x4, d: simd.U32x4, e: simd.U32x4, f: simd.U32x4, g: simd.U32x4, h: simd.U32x4): simd.U32x4 { simd.add_u32x4(a, h) }`, "full")
	fullPool := generator{fn: full, vectorHomes: true}
	if fullPool.leafVectorPool() != 0 {
		t.Fatal("fully occupied argument registers exposed a leaf home")
	}
	g := generator{
		fn: fn, vectorHomes: true,
		slots: map[string]int64{}, types: map[string]scalar{}, regs: map[string]int{},
		homesUsedV: map[int]bool{},
	}
	g.pushScope()
	for pass := 0; pass < 3; pass++ {
		g.pushScope()
		for i := 0; i < 7; i++ {
			g.declare(fmt.Sprintf("local%d", i), vecShapes["U32x4"])
		}
		if len(g.leafHomesV) != 0 || g.usedCalleeV != 0 {
			t.Fatal("unexpected allocation under full leaf-pool pressure")
		}
		g.popScope()
		seen := map[int]bool{}
		for _, r := range g.leafHomesV {
			if seen[r] || r <= vecBase || r > vecBase+7 {
				t.Fatalf("duplicate or unsafe recycled home %d", r)
			}
			seen[r] = true
		}
		if len(seen) != 7 || len(g.homesUsedV) != 7 {
			t.Fatal("scope release lost a home or its clobber history")
		}
	}
}

func TestLeafVectorHomesProvenABI(t *testing.T) {
	for _, source := range []string{
		`leaf: (seed: u32): simd.U32x4 {
  a: simd.U32x4 = simd.splat_u32x4(seed)
  b: simd.U32x4 = simd.add_u32x4(a, a)
  simd.add_u32x4(b, a)
}`,
		`leaf: (a: simd.U32x4, f: f32, b: simd.U32x4): simd.U32x4 {
  x: simd.U32x4 = simd.add_u32x4(a, b)
  y: simd.U32x4 = simd.add_u32x4(x, a)
  simd.add_u32x4(y, b)
}`,
		`leaf: (a: simd.F32x4, f: f32, b: simd.F32x4): simd.F32x4 {
  x: simd.F32x4 = simd.add_f32x4(a, b)
  y: simd.F32x4 = simd.splat_f32x4(f)
  simd.add_f32x4(x, y)
}`,
	} {
		fn, functions, _, tc := checkedFillFunction(t, source, "leaf")
		before := cloneNode(fn)
		for _, gate := range []bool{false, true} {
			body, err := CompileFor(Lane{Arch: asm.ArchArm64, VectorHomes: gate, NoReductions: true}, fn, functions, nil, nil, nil, tc)
			if err != nil {
				t.Fatal(err)
			}
			if (LeafVectorHomes(body) > 0) != gate {
				t.Fatalf("leaf home gate=%v: %s", gate, Describe(body))
			}
			if findings := asm.Check(body, fn, map[string]bool{body.Name: true}); len(findings) != 0 {
				t.Fatalf("ABI/checker: %v\n%s", findings, Describe(body))
			}
			if _, _, err := asm.EncodeFunction(body); err != nil {
				t.Fatal(err)
			}
			if verdict := asm.Verify(body, fn, fn.Body); verdict.Kind != asm.VerdictProven {
				t.Fatalf("gate=%v: %s: %s\n%s", gate, verdict.Kind, verdict.Message, Describe(body))
			}
			if !reflect.DeepEqual(fn, before) {
				t.Fatal("allocation mutated the source reference")
			}
		}
	}
}

func TestLeafVectorHomesReductionElidesFrame(t *testing.T) {
	fn, functions, _, tc := checkedFillFunction(t, `sum: (v: []u32): u32 {
  acc: u32 = 0
  i: u32 = 0
  while i < len(v) { acc = acc + v[i]; i = i + u32(1) }
  acc
}`, "sum")
	body, err := CompileFor(Lane{Arch: asm.ArchArm64, VectorHomes: true, VectorReductions: true, Reallocate: true, TrimCalleeSaves: true, ElideEmptyFrame: true}, fn, functions, nil, nil, nil, tc)
	if err != nil {
		t.Fatal(err)
	}
	if body.Frame != 0 {
		t.Fatalf("stackless combine should have an empty frame:\n%s", Describe(body))
	}
	if findings := asm.Check(body, fn, map[string]bool{body.Name: true}); len(findings) != 0 {
		t.Fatalf("checker: %v\n%s", findings, Describe(body))
	}
	reference := body.Body
	if reference == nil {
		reference = fn.Body
	}
	if verdict := asm.Verify(body, fn, reference); verdict.Kind != asm.VerdictProven {
		t.Fatalf("%s: %s\n%s", verdict.Kind, verdict.Message, Describe(body))
	}
}
