package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// Verified reduction unrolling (docs/spec/94-assembler.md §9 "Reductions";
// nativegen/reduction.go; Oak.Reduction.unrolled4_eq): a plain integer
// reduction over a span lowers as a four-accumulator main loop, the
// remainder loop, and the combine, proven against the rewritten body; a
// float reduction and a loop that reads the accumulator elsewhere are left
// as written, and an unrolled form whose verdict would be weaker than the
// plain loop's is dropped for it (compiler/native_bodies.go). The values
// are checked against the C backend over lengths that cover the remainder
// (0 through 9) and an 8-bit accumulator that wraps.
const nativeReductionProgram = `
sum: (v: []u64): u64 {
  total: u64 = 0
  i: u32 = 0
  while i < len(v) {
    total = total + v[i]
    i = i + u32(1)
  }
  total
}

sum8: (v: []u8): u8 {
  total: u8 = 0
  i: u32 = 0
  while i < len(v) {
    total = v[i] + total
    i = i + u32(1)
  }
  total
}

fsum: (v: []f32): f32 {
  total: f32 = 0.0
  i: u32 = 0
  while i < len(v) {
    total = total + v[i]
    i = i + u32(1)
  }
  total
}

running_max: (v: []u32): u32 {
  best: u32 = 0
  i: u32 = 0
  while i < len(v) {
    best = best + v[i]
    v[i] > best ? { best = v[i] }
    i = i + u32(1)
  }
  best
}

main: (): i32 {
  xs: [9]u64 = [9]u64{ 1, 2, 3, 4, 5, 6, 7, 8, 9 }
  bytes: [7]u8 = [7]u8{ 200, 100, 50, 25, 12, 6, 3 }
  fs: [5]f32 = [5]f32{ 1.5, 2.5, 3.0, 4.0, 5.0 }
  ws: [6]u32 = [6]u32{ 3, 9, 1, 1, 1, 1 }
  // Every remainder: the sums of the first 0..9 elements are 0, 1, 3, 6, 10, 15, 21, 28, 36, 45 (total 165).
  all: []u64 = view(&xs)
  acc: u64 = 0
  n: u32 = 0
  while n <= u32(9) {
    acc = acc + sum(subslice(all, u32(0), n))
    n = n + u32(1)
  }
  // 396 wraps to 140 in eight bits; the float sum is 16.0; running_max ends at 16.
  b: u32 = u32(sum8(view(&bytes)))
  f: u32 = fsum(view(&fs)) == 16.0 ? u32(1) | u32(0)
  r: u32 = running_max(view(&ws))
  // 165 + 140 + 1 + 16 = 322; modulo 256 the exit code is 66.
  i32_bits_u32((u32_trunc_u64(acc) + b + f + r) & u32(255))
}
`

func TestE2ENativeReductionUnrolling(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("reduce.oak", nativeReductionProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	// loops counts a unit's loops and, in the first, its element loads
	// (`ldr`, `ldrb`) and pair loads (`ldp`, nativegen/pair_loads.go).
	loops := func(name string) (count int, loads int, pairs int) {
		fn, ok := units[name]
		if !ok {
			t.Fatalf("%s was not lowered natively:\n%s", name, strings.Join(infos, "\n"))
		}
		firstName, firstStart, firstEnd := "", -1, len(fn.Items)
		for i, item := range fn.Items {
			if label, ok := item.(asm.Label); ok && strings.HasPrefix(label.Name, "loop_") {
				count++
				if firstStart < 0 {
					firstName, firstStart = label.Name, i+1
				}
			}
		}
		for i, item := range fn.Items {
			if label, ok := item.(asm.Label); ok && label.Name == "check_"+firstName {
				firstEnd = i
				break
			}
			instruction, ok := item.(asm.Instruction)
			if !ok || (instruction.Mnemonic != "b" && instruction.Mnemonic != "j") || len(instruction.Operands) == 0 {
				continue
			}
			if symbol, ok := instruction.Operands[len(instruction.Operands)-1].(asm.Symbol); ok && symbol.Name == firstName && i >= firstStart {
				firstEnd = i
				break
			}
		}
		for _, item := range fn.Items[firstStart:firstEnd] {
			instruction, ok := item.(asm.Instruction)
			if !ok {
				continue
			}
			if instruction.Mnemonic == "ldr" || instruction.Mnemonic == "ldrb" {
				loads++
			}
			if instruction.Mnemonic == "ldp" {
				pairs++
			}
		}
		return count, loads, pairs
	}
	joined := strings.Join(infos, "\n")
	// The four 8-byte loads of the main loop are two pair loads off one
	// block address (nativegen/pair_loads.go).
	if count, loads, pairs := loops("sum"); count != 2 || loads != 0 || pairs != 2 {
		t.Errorf("sum must lower as a main loop of two pair loads and a remainder loop, got %d loop(s), %d load(s), %d pair(s) in the first", count, loads, pairs)
	}
	if units["sum"].Body == nil {
		t.Error("sum must record the rewritten body for the verifier")
	}
	if !strings.Contains(joined, "asm unit sum: proven equal to its Oak body") {
		t.Errorf("sum must be proven against its rewritten body; diagnostics:\n%s", joined)
	}
	// The 8-bit accumulator: the verifier finds no affine image of a
	// normalized narrow accumulator in either form (evidence, not proof,
	// for the loop as written too), so the unrolled form is kept — the
	// verdict is not weakened — and the wrapping sum agrees with the C
	// backend below.
	// Byte loads have no pair form: the four stay — or, both forms being
	// evidence, the cost model keeps the cheaper bottom-tested plain loop
	// (docs/spec/94-assembler.md §9 "Bottom-tested loops"): one loop, one
	// load, a conditional back edge.
	if count, loads, _ := loops("sum8"); !(count == 2 && loads == 4) && !(count == 1 && loads == 1 && nativegen.RotatedLoops(units["sum8"]) == 1) {
		t.Errorf("sum8 must unroll as sum does or keep its rotated plain loop (both forms are evidence), got %d loop(s), %d load(s)", count, loads)
	}
	if !strings.Contains(joined, "asm unit sum8: agrees with its Oak body") {
		t.Errorf("sum8 must keep at least the evidence verdict of its plain form; diagnostics:\n%s", joined)
	}
	for _, name := range []string{"fsum", "running_max"} {
		if count, _, _ := loops(name); count != 1 {
			t.Errorf("%s must keep its single loop (a float accumulator, an accumulator read in the body), got %d loops", name, count)
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "native_reduction", comp)
	if abnormal || code != 66 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 66\n%s", code, abnormal, strings.Join(infos, "\n"))
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_reduction_c", New().WithSource("reduce.oak", nativeReductionProgram)); abnormal || code != 66 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 66", code, abnormal)
	}
}
