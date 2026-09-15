package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Bottom-tested loops (docs/spec/94-assembler.md §9 "Bottom-tested
// loops"): a `while` over one comparison is lowered with its test once
// before the loop and again as a conditional back edge, one branch an
// iteration; a conjunction rotates too, its tail a run of exits ending in
// the back edge; the verifier recognizes both shapes and still proves the
// bodies, and a disjunction keeps its top-tested form. The C
// backend's realization is the oracle for the values.
const nativeRotationProgram = `
total: (v: []u64): u64 {
  acc: u64 = 0
  i: u32 = 0
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}

first_zero: (v: []u64): u32 {
  i: u32 = 0
  found: Bool = false
  while i < len(v) && !found {
    v[i] == u64(0) ? { found = true } | { i = i + u32(1) }
  }
  i
}

at_least_once: (n: u32): u32 {
  i: u32 = 0
  count: u32 = 0
  while i < n || count == u32(0) {
    count = count + u32(1)
    i = i + u32(1)
  }
  count
}

main: (): i32 {
  xs: [6]u64 = [u64(5), u64(7), u64(9), u64(0), u64(11), u64(10)]
  i32_bits_u32(u32_trunc_u64(total(view(&xs))) + first_zero(view(&xs)) - u32(3) + at_least_once(u32(0)) - u32(1))
}
`

func TestE2ENativeBottomTestedLoops(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("rotate.oak", nativeRotationProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	shapes := map[string]string{}
	for _, f := range model.AsmFunctions {
		unconditional, conditionalBack := 0, 0
		labels := map[string]int{}
		for i, item := range f.Items {
			if label, isLabel := item.(asm.Label); isLabel {
				labels[label.Name] = i
			}
		}
		for i, item := range f.Items {
			instr, isInstr := item.(asm.Instruction)
			if !isInstr || len(instr.Operands) == 0 {
				continue
			}
			sym, isSym := instr.Operands[len(instr.Operands)-1].(asm.Symbol)
			if !isSym || !strings.HasPrefix(sym.Name, "loop_") {
				continue
			}
			if instr.Mnemonic == "b" {
				unconditional++
			} else if labels[sym.Name] < i {
				conditionalBack++
			}
		}
		// A rotated loop has a conditional back edge and no jump to its
		// head; a body may also hold a top-tested loop the pass left (the
		// unrolled reduction's main loop, whose test has a setup
		// instruction), so the shape is "bottom" when any loop rotated.
		_ = unconditional
		shapes[f.Name] = map[bool]string{true: "bottom", false: "top"}[conditionalBack >= 1]
	}
	joined := strings.Join(infos, "\n")
	if shapes["total"] != "bottom" {
		t.Errorf("total's remainder loop must be bottom-tested (a conditional back edge); shapes %v\n%s", shapes, joined)
	}
	if shapes["first_zero"] != "bottom" {
		t.Errorf("first_zero's conjunction must be bottom-tested too (the tail a run of exits ending in the back edge); shapes %v\n%s", shapes, joined)
	}
	if shapes["at_least_once"] != "top" {
		t.Errorf("a disjunction keeps the top-tested shape; shapes %v\n%s", shapes, joined)
	}
	for _, name := range []string{"total", "first_zero"} {
		if !strings.Contains(joined, name+": 1 loop(s) bottom-tested, proven") || !strings.Contains(joined, "asm unit "+name+": proven equal to its Oak body") {
			t.Errorf("%s's rotated loop must be proven; diagnostics:\n%s", name, joined)
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "native_rotation", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_rotation_c", New().WithSource("rotate.oak", nativeRotationProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
