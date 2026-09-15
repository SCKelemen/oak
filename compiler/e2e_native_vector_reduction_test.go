package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// Reduction vectorization (docs/spec/94-assembler.md §9 "Reductions";
// nativegen/vector_reduction.go, the `vectorize-reductions` candidate).
// A reduction's accumulators are the lanes of four fixed vectors: a u32
// accumulator's main loop is four `ldr q` and four `add v.4s` over
// sixteen elements an iteration, a u64 one's the same over eight, the
// lanes fold in the vector domain and reach the scalar through a frame
// array of one vector's lanes, and both bodies are proven against the
// rewritten source. A float accumulator is never rewritten — its
// addition does not reassociate.
const nativeVectorReductionProgram = `
sum32: (v: []u32): u32 {
  acc: u32 = 0
  i: u32 = 0
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}

sum64: (v: []u64): u64 {
  acc: u64 = 0
  i: u32 = 0
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
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

main: (): i32 {
  xs: [11]u32 = [11]u32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 }
  ys: [9]u64 = [9]u64{ 1, 2, 3, 4, 5, 6, 7, 8, 9 }
  zs: [3]f32 = [3]f32{ 0.5, 1.5, 2.0 }
  // 66 + 45 - 7 = 104, the f32 sum exactly 4.0 (it is never reassociated).
  drop: u32 = fsum(view(&zs)) == 4.0 ? u32(7) | u32(0)
  i32_bits_u32((sum32(view(&xs)) + u32_trunc_u64(sum64(view(&ys)))) - drop)
}
`

// mainLoopOf returns the instructions of a unit's first loop body.
func mainLoopOf(fn *asm.Function) []asm.Instruction {
	var body []asm.Instruction
	inLoop := false
	for _, item := range fn.Items {
		switch it := item.(type) {
		case asm.Label:
			if strings.HasPrefix(it.Name, "loop") {
				if inLoop {
					return body
				}
				inLoop = true
			} else if inLoop {
				return body
			}
		case asm.Instruction:
			if inLoop {
				body = append(body, it)
			}
		}
	}
	return body
}

func TestE2ENativeVectorReduction(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("vecred.oak", nativeVectorReductionProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	for _, name := range []string{"sum32", "sum64", "fsum"} {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven equal to its Oak body") {
			t.Errorf("%s must be proven; diagnostics:\n%s", name, joined)
		}
	}
	// Each main loop: four vector loads and four lane-wise adds, no
	// scalar element load.
	for _, shape := range []struct {
		unit, arrangement string
	}{{"sum32", "4s"}, {"sum64", "2d"}} {
		vecLoads, vecAdds, scalarLoads := 0, 0, 0
		for _, ins := range mainLoopOf(units[shape.unit]) {
			dst, isReg := ins.Operands[0].(asm.Register)
			switch {
			case ins.Mnemonic == "ldr" && isReg && dst.Vec == "q":
				vecLoads++
			case ins.Mnemonic == "add" && isReg && dst.Vec == shape.arrangement:
				vecAdds++
			case ins.Mnemonic == "ldr" || ins.Mnemonic == "ldp":
				scalarLoads++
			}
		}
		if vecLoads != 4 || vecAdds != 4 || scalarLoads != 0 {
			t.Errorf("%s's main loop must be four vector loads and four lane-wise adds, got %d, %d, and %d scalar loads:\n%s", shape.unit, vecLoads, vecAdds, scalarLoads, nativegen.Describe(units[shape.unit]))
		}
	}
	// The float accumulator is never rewritten: one load, one fadd.
	for _, ins := range mainLoopOf(units["fsum"]) {
		if dst, isReg := ins.Operands[0].(asm.Register); isReg && dst.Vec == "4s" {
			t.Errorf("fsum must not be vectorized (float addition does not reassociate):\n%s", nativegen.Describe(units["fsum"]))
			break
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "native_vector_reduction", comp)
	if abnormal || code != 104 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 104\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_vector_reduction_c", New().WithSource("vecred.oak", nativeVectorReductionProgram)); abnormal || code != 104 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 104", code, abnormal)
	}
}
