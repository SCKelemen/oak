package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// Fold vectorization (docs/spec/94-assembler.md §9 "Fold vectorization";
// nativegen/vector_fold.go, the `vectorize-folds` candidate). A float
// reduction whose element expression is lane-wise over spans of one
// length — the dot product — computes one vector of element values a trip
// and adds its lanes to the accumulator in element order, so the result
// rounds as the scalar loop's did; the remainder loop stays as written and
// the body is proven against the rewritten form (Oak.Fold.blocked_eq).
const nativeVectorFoldProgram = `
dot32: (a: []f32, b: []f32): f32 {
  total: f32 = 0.0
  len(a) == len(b) ? {
    i: u32 = 0
    while i < len(a) {
      total = total + a[i] * b[i]
      i = i + u32(1)
    }
  }
  total
}

dot64: (a: []f64, b: []f64): f64 {
  total: f64 = 0.0
  len(a) == len(b) ? {
    i: u32 = 0
    while i < len(a) {
      total = total + a[i] * b[i]
      i = i + u32(1)
    }
  }
  total
}

scaled: (a: []f32, k: f32): f32 {
  total: f32 = 0.0
  i: u32 = 0
  while i < len(a) {
    total = total + a[i] * k
    i = i + u32(1)
  }
  total
}

fsum: (v: []f32): f32 {
  acc: f32 = 0.0
  i: u32 = 0
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}

main: () -> i32 {
  xs: [9]f32 = [9]f32{ 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0 }
  hs: [9]f32 = [9]f32{ 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5 }
  ys: [5]f64 = [5]f64{ 1.0, 2.0, 3.0, 4.0, 5.0 }
  ts: [5]f64 = [5]f64{ 2.0, 2.0, 2.0, 2.0, 2.0 }
  // 45 * 0.5 = 22.5; 15 * 2 = 30; 45 * 0.25 = 11.25; the plain sum 45 —
  // every product and sum exact, so both backends agree bit for bit.
  d32: u32 = dot32(view(&xs), view(&hs)) == 22.5 ? u32(45) | u32(0)
  d64: u32 = dot64(view(&ys), view(&ts)) == 30.0 ? u32(60) | u32(0)
  sc: u32 = scaled(view(&xs), 0.25) == 11.25 ? u32(20) | u32(0)
  fs: u32 = fsum(view(&xs)) == 45.0 ? u32(7) | u32(0)
  i32_bits_u32(d32 + d64 + sc + fs)
}
`

func TestE2ENativeVectorFold(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("vecfold.oak", nativeVectorFoldProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	joined := strings.Join(infos, "\n")
	for _, name := range []string{"dot32", "dot64", "scaled", "fsum"} {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven equal to its Oak body") {
			t.Errorf("%s must be proven; diagnostics:\n%s", name, joined)
		}
	}
	// Each vectorized main loop: one lane-wise multiply over the vector
	// arrangement, one lane move and one scalar add per lane, and no
	// scalar multiply.
	for _, shape := range []struct {
		unit, arrangement string
		lanes             int
	}{{"dot32", "4s", 4}, {"dot64", "2d", 2}, {"scaled", "4s", 4}} {
		if n := nativegen.VectorizedFolds(units[shape.unit]); n != 1 {
			t.Errorf("%s must vectorize its fold once, got %d:\n%s\n%s", shape.unit, n, nativegen.Describe(units[shape.unit]), joined)
		}
		vecMuls, laneMoves, adds, scalarMuls, compares := 0, 0, 0, 0, 0
		for _, ins := range mainLoopOf(units[shape.unit]) {
			dst, isReg := ins.Operands[0].(asm.Register)
			switch {
			case ins.Mnemonic == "fmul" && isReg && dst.Vec == shape.arrangement:
				vecMuls++
			case ins.Mnemonic == "fmul":
				scalarMuls++
			case ins.Mnemonic == "mov" && len(ins.Operands) == 2:
				if src, isSrc := ins.Operands[1].(asm.Register); isSrc && src.Class == asm.ClassV && src.Lane >= 0 {
					laneMoves++
				}
			case ins.Mnemonic == "fadd":
				adds++
			case ins.Mnemonic == "cmp":
				compares++
			}
		}
		// One vector a trip, or two under the fold unrolling
		// (unroll-vector-folds): the lane moves and adds follow.
		if (vecMuls != 1 && vecMuls != 2) || laneMoves != shape.lanes*vecMuls || adds != shape.lanes*vecMuls || scalarMuls != 0 {
			t.Errorf("%s's main loop must be one or two vector multiplies with %d lane moves and adds each, no scalar multiply; got %d, %d, %d, %d:\n%s", shape.unit, shape.lanes, vecMuls, laneMoves, adds, scalarMuls, nativegen.Describe(units[shape.unit]))
		}
		// One compare a trip: the rotated loop's slack test. The second
		// span's lanes stand under the first's test (the arm's
		// `len(a) == len(b)`, read by the lowering as by the checker), and
		// the invariant half of the condition is hoisted, not re-tested.
		if compares != 1 {
			t.Errorf("%s's main loop must test its index once a trip, got %d compares:\n%s", shape.unit, compares, nativegen.Describe(units[shape.unit]))
		}
	}
	// A bare float sum saves nothing by the vector and stays scalar.
	if n := nativegen.VectorizedFolds(units["fsum"]); n != 0 {
		t.Errorf("fsum must stay scalar (a bare element saves no work as a vector):\n%s", nativegen.Describe(units["fsum"]))
	}
	_, code, abnormal := buildAndRunFrom(t, "native_vector_fold", comp)
	if abnormal || code != 45+60+20+7 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 132\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_vector_fold_c", New().WithSource("vecfold.oak", nativeVectorFoldProgram)); abnormal || code != 132 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 132", code, abnormal)
	}
}
