package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// Lane-wise accumulators (docs/spec/94-assembler.md §9 "Lane-wise
// accumulators"; nativegen/vector_lanes.go, the `vectorize-lanes`
// candidate). A block's independent accumulators become the lanes of
// vectors: eight f32 accumulators two F32x4, four f64 accumulators two
// F64x2; each lane meets its accumulator's values in order, so the sums
// round as the scalar loop's did and the body is proven against the
// rewritten form (Oak.Lanes.blocks_eq).
const nativeVectorLanesProgram = `
squares: (a: []f32): f32 {
  acc: [8]f32 = [8]f32{ 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0 }
  i: u32 = 0
  while len(a) >= u32(8) && i <= len(a) - u32(8) {
    acc[0] = acc[0] + a[i] * a[i]
    acc[1] = acc[1] + a[i + u32(1)] * a[i + u32(1)]
    acc[2] = acc[2] + a[i + u32(2)] * a[i + u32(2)]
    acc[3] = acc[3] + a[i + u32(3)] * a[i + u32(3)]
    acc[4] = acc[4] + a[i + u32(4)] * a[i + u32(4)]
    acc[5] = acc[5] + a[i + u32(5)] * a[i + u32(5)]
    acc[6] = acc[6] + a[i + u32(6)] * a[i + u32(6)]
    acc[7] = acc[7] + a[i + u32(7)] * a[i + u32(7)]
    i = i + u32(8)
  }
  while i < len(a) {
    acc[0] = acc[0] + a[i] * a[i]
    i = i + u32(1)
  }
  ((acc[0] + acc[1]) + (acc[2] + acc[3])) + ((acc[4] + acc[5]) + (acc[6] + acc[7]))
}

scaled: (a: []f64, k: f64): f64 {
  acc: [4]f64 = [4]f64{ 0.0, 0.0, 0.0, 0.0 }
  i: u32 = 0
  while len(a) >= u32(4) && i <= len(a) - u32(4) {
    acc[0] = acc[0] + a[i] * k
    acc[1] = acc[1] + a[i + u32(1)] * k
    acc[2] = acc[2] + a[i + u32(2)] * k
    acc[3] = acc[3] + a[i + u32(3)] * k
    i = i + u32(4)
  }
  while i < len(a) {
    acc[0] = acc[0] + a[i] * k
    i = i + u32(1)
  }
  (acc[0] + acc[1]) + (acc[2] + acc[3])
}

main: () -> i32 {
  xs: [19]f32 = [19]f32{ 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 1.0, 2.0, 3.0 }
  ys: [6]f64 = [6]f64{ 1.0, 2.0, 3.0, 4.0, 5.0, 6.0 }
  // squares: 2 * 204 + 1 + 4 + 9 = 422; scaled: 21 * 0.5 = 10.5.
  s: u32 = squares(view(&xs)) == 422.0 ? u32(100) | u32(0)
  d: u32 = scaled(view(&ys), 0.5) == 10.5 ? u32(11) | u32(0)
  i32_bits_u32(s + d)
}
`

func TestE2ENativeVectorLanes(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("veclanes.oak", nativeVectorLanesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	for _, shape := range []struct {
		unit, arrangement string
		vectors           int
	}{{"squares", "4s", 2}, {"scaled", "2d", 2}} {
		unit := units[shape.unit]
		if unit == nil {
			t.Fatalf("%s was not lowered natively:\n%s", shape.unit, joined)
		}
		// Verified: proven, or witnessed where the scalar accumulators'
		// coupling is beyond the loop proof (the scalar form is witnessed
		// too); never trusted.
		if !strings.Contains(joined, "asm unit "+shape.unit+": proven equal to its Oak body") && !strings.Contains(joined, "asm unit "+shape.unit+": agrees with its Oak body") {
			t.Errorf("%s must be verified; diagnostics:\n%s", shape.unit, joined)
		}
		if n := nativegen.VectorizedLanes(unit); n != 1 {
			t.Errorf("%s must vectorize its accumulators once, got %d:\n%s\n%s", shape.unit, n, nativegen.Describe(unit), joined)
		}
		// The main loop: one lane-wise add per vector and no scalar
		// float arithmetic.
		vecAdds, scalarFloat := 0, 0
		for _, ins := range mainLoopOf(unit) {
			dst, isReg := ins.Operands[0].(asm.Register)
			switch {
			case ins.Mnemonic == "fadd" && isReg && dst.Vec == shape.arrangement:
				vecAdds++
			case (ins.Mnemonic == "fadd" || ins.Mnemonic == "fmul") && isReg && (dst.Vec == "s" || dst.Vec == "d"):
				scalarFloat++
			}
		}
		if vecAdds != shape.vectors || scalarFloat != 0 {
			t.Errorf("%s's main loop must accumulate in %d vectors with no scalar float arithmetic, got %d and %d:\n%s", shape.unit, shape.vectors, vecAdds, scalarFloat, nativegen.Describe(unit))
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "native_vector_lanes", comp)
	if abnormal || code != 111 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 111\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_vector_lanes_c", New().WithSource("veclanes.oak", nativeVectorLanesProgram)); abnormal || code != 111 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 111", code, abnormal)
	}
}
