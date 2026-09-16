package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// Multiply-add forms (docs/spec/94-assembler.md §9 "Multiply-add forms";
// nativegen/multiply_add.go, the `multiply-add` candidate). An integer
// product and its addend are one instruction: `a + b * c` is `madd`,
// `a - b * c` is `msub`, `u32(0) - b * c` is `mneg`, and a dot-product
// loop pays one instruction less an element. The operands are evaluated
// in the order the source writes them. A float expression keeps its
// two roundings — `fmla` is one — and a product by a constant keeps the
// strength reduction's shift.
const nativeMultiplyAddProgram = `
fma: (a: u32, b: u32, c: u32): u32 = a + b * c

fms: (a: u32, b: u32, c: u32): u32 = a - b * c

mneg: (b: u32, c: u32): u32 = u32(0) - b * c

wide: (a: u64, b: u64, c: u64): u64 = a + b * c

shifted: (a: u32, b: u32): u32 = a + b * u32(4)

fsum: (a: f32, b: f32, c: f32): f32 = a + b * c

dot: (x: []u32, y: []u32): u32 {
  acc: u32 = 0
  i: u32 = 0
  while i < len(x) && i < len(y) {
    acc = acc + x[i] * y[i]
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  // fma 7 + 3*5 = 22, wide the same, shifted 7 + 2*4 = 15, the float sum
  // exactly 7.0, and the dot product 5 + 12 + 21 + 32 = 70:
  // 22 + 22 + 15 - 1 + 1 = 59.
  xs: [4]u32 = [4]u32{ 1, 2, 3, 4 }
  ys: [4]u32 = [4]u32{ 5, 6, 7, 8 }
  drop: u32 = fsum(1.0, 2.0, 3.0) == 7.0 ? u32(1) | u32(0)
  keep: u32 = dot(view(&xs), view(&ys)) == u32(70) ? u32(1) | u32(0)
  i32_bits_u32(fma(u32(7), u32(3), u32(5)) + u32_trunc_u64(wide(u32(7) == u32(7) ? u64(7) | u64(0), u64(3), u64(5))) + shifted(u32(7), u32(2)) - drop + keep)
}
`

func TestE2ENativeMultiplyAdd(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("madd.oak", nativeMultiplyAddProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	mnemonics := func(name string) map[string]int {
		fn := units[name]
		if fn == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		counts := map[string]int{}
		for _, item := range fn.Items {
			if ins, isIns := item.(asm.Instruction); isIns {
				counts[ins.Mnemonic]++
			}
		}
		return counts
	}
	for _, want := range []struct {
		unit, mnemonic string
	}{{"fma", "madd"}, {"fms", "msub"}, {"mneg", "mneg"}, {"wide", "madd"}} {
		counts := mnemonics(want.unit)
		if counts[want.mnemonic] != 1 || counts["mul"] != 0 {
			t.Errorf("%s must be one %s and no mul, got %v:\n%s", want.unit, want.mnemonic, counts, nativegen.Describe(units[want.unit]))
		}
		if !strings.Contains(joined, "asm unit "+want.unit+": proven equal to its Oak body") {
			t.Errorf("%s must be proven; diagnostics:\n%s", want.unit, joined)
		}
	}
	// A product by a constant power of two keeps the shift — as an lsl,
	// or folded into the add's shifted operand by machine.Fuse.
	shifts := 0
	for _, item := range units["shifted"].Items {
		ins, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		if ins.Mnemonic == "lsl" {
			shifts++
		}
		for _, op := range ins.Operands {
			if sh, isShifted := op.(asm.Shifted); isShifted && sh.Kind == "lsl" {
				shifts++
			}
		}
	}
	if counts := mnemonics("shifted"); counts["madd"] != 0 || shifts != 1 {
		t.Errorf("shifted must keep the strength reduction's shift, got %d shift(s) in %v:\n%s", shifts, counts, nativegen.Describe(units["shifted"]))
	}
	// The dot-product loop fuses each element's product into its
	// accumulator: at least one madd (four, unrolled) and no mul.
	if counts := mnemonics("dot"); counts["madd"] < 1 || counts["mul"] != 0 {
		t.Errorf("dot must fuse its product into the accumulator, got %v:\n%s", counts, nativegen.Describe(units["dot"]))
	}
	// A float expression is two roundings: fmul and fadd, never fmla.
	if counts := mnemonics("fsum"); counts["fmla"] != 0 || counts["fmul"] != 1 || counts["fadd"] != 1 {
		t.Errorf("fsum must keep its two roundings, got %v:\n%s", counts, nativegen.Describe(units["fsum"]))
	}
	_, code, abnormal := buildAndRunFrom(t, "native_multiply_add", comp)
	if abnormal || code != 59 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 59\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_multiply_add_c", New().WithSource("madd.oak", nativeMultiplyAddProgram)); abnormal || code != 59 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 59", code, abnormal)
	}
}
