package compiler

import (
	"regexp"
	"strconv"
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
// bodies, and a disjunction keeps its top-tested form. (A plain
// reduction is not the example: the search unrolls it, and the cost model
// finds the peeled test not worth rotating a three-trip remainder.) The C
// backend's realization is the oracle for the values.
const nativeRotationProgram = `
fill: (v: [*]u64, x: u64): () {
  i: u32 = 0
  while i < len(v) {
    v[i] = x
    i = i + u32(1)
  }
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
  fill(span(&xs), u64(7))
  i32_bits_u32(first_zero(view(&xs)) + at_least_once(u32(0)) + u32(35))
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
	if shapes["fill"] != "bottom" {
		t.Errorf("fill's loop must be bottom-tested (a conditional back edge); shapes %v\n%s", shapes, joined)
	}
	if shapes["first_zero"] != "bottom" {
		t.Errorf("first_zero's conjunction must be bottom-tested too (the tail a run of exits ending in the back edge); shapes %v\n%s", shapes, joined)
	}
	if shapes["at_least_once"] != "top" {
		t.Errorf("a disjunction keeps the top-tested shape; shapes %v\n%s", shapes, joined)
	}
	// Every loop each unit ends up with rotates, and the unit is proven.
	// The count is not pinned: how many loops `fill` becomes is the
	// vectorizer's business — a map of a constant is now a vector main
	// loop, an unrolled remainder and a scalar remainder, where it was a
	// main loop and one remainder — and a test that names the number goes
	// stale every time that changes. What matters is that none of them
	// is left top-tested.
	rotated := regexp.MustCompile(`(?m)^native backend: (\w+): (\d+) loop\(s\) bottom-tested, proven$`)
	counts := map[string]int{}
	for _, m := range rotated.FindAllStringSubmatch(joined, -1) {
		n, err := strconv.Atoi(m[2])
		if err != nil {
			t.Fatalf("unreadable rotation count %q", m[2])
		}
		counts[m[1]] = n
	}
	for _, name := range []string{"fill", "first_zero"} {
		if counts[name] < 1 {
			t.Errorf("%s's loops must all rotate and be proven, got %v; diagnostics:\n%s", name, counts, joined)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven equal to its Oak body") {
			t.Errorf("%s must be proven; diagnostics:\n%s", name, joined)
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
