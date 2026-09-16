package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// Value-position select forms (docs/spec/94-assembler.md §9 "Select
// forms"; nativegen/value_select.go, the `value-select` candidate). A
// conditional in value position is a compare and one conditional select
// where it was a branch over two moves: `csel` in general, and `csinc`,
// `csneg`, `csinv` where both arms share a variable the machine can
// increment, negate, or complement in the select itself. A float result
// and an arm that is not safe to evaluate on both paths keep the branch.
const nativeValueSelectProgram = `
pick: (a: u32, b: u32): u32 = a < b ? b | a
third: (a: u32, b: u32, c: u32): u32 = a < b ? c | a
inc: (a: u32, c: u32): u32 = a < c ? a + u32(1) | a
negate: (a: i32, c: i32): i32 = a < c ? 0 - a | a
flip: (a: u32, c: u32): u32 = a < c ? ^a | a
narrow: (a: u8, c: u8): u8 = a < c ? a + u8(1) | a
signed: (a: i32, b: i32): i32 = a > b ? b | a

// A guarded read is not safe on both paths: the branch stands.
guarded: (v: []u32, i: u32): u32 = i < len(v) ? v[i] | u32(0)

// A float result keeps the branch: the select forms are the integer ones.
fpick: (a: f32, b: f32): f32 = a < b ? b | a

// In a loop body: the select keeps the body one block.
clamp_sum: (v: []u32, cap: u32): u32 {
  total: u32 = 0
  i: u32 = 0
  while i < len(v) {
    x: u32 = v[i]
    total = total + (x < cap ? x | cap)
    i = i + u32(1)
  }
  total
}

main: (): i32 {
  xs: [4]u32 = [4]u32{ 1, 9, 3, 7 }
  // pick(2,5)=5, third(2,5,8)=8, inc(2,5)=3, negate(-2,5)=2, flip(0,5)=4294967295 -> low byte 255,
  // narrow(250,255)=251, signed(-3,-9)=-9 -> +9 taken below, guarded(xs,1)=9, fpick 2.5,
  // clamp_sum(xs, 5) = 1 + 5 + 3 + 5 = 14.
  f: u32 = fpick(1.5, 2.5) == 2.5 ? u32(1) | u32(0)
  s: i32 = signed(0 - 3, 0 - 9)
  n: u32 = u32_bits_i32(negate(0 - 2, 5))
  // 5 + 8 + 3 + 2 + 255 + 251 + 9 + 9 + 1 + 14 = 557; modulo 256 the exit code is 45.
  total: u32 = pick(u32(2), u32(5)) + third(u32(2), u32(5), u32(8)) + inc(u32(2), u32(5)) + n +
    (flip(u32(0), u32(5)) & u32(255)) + u32(narrow(u8(250), u8(255))) + u32_bits_i32(0 - s) + f +
    guarded(view(&xs), u32(1)) + clamp_sum(view(&xs), u32(5))
  i32_bits_u32(total & u32(255))
}
`

func TestE2ENativeValueSelectForms(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("value_select.oak", nativeValueSelectProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	counts := func(name string) map[string]int {
		fn := units[name]
		if fn == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		out := map[string]int{}
		for _, item := range fn.Items {
			if ins, isIns := item.(asm.Instruction); isIns {
				out[ins.Mnemonic]++
			}
		}
		return out
	}
	// Each form, and no branch left in the body.
	for _, want := range []struct{ unit, mnemonic string }{
		{"pick", "csel"}, {"third", "csel"}, {"signed", "csel"},
		{"inc", "csinc"}, {"negate", "csneg"}, {"flip", "csinv"}, {"narrow", "csinc"},
	} {
		got := counts(want.unit)
		if got[want.mnemonic] != 1 || got["b."] != 0 || got["b"] != 0 {
			t.Errorf("%s must be one %s and no branch, got %v:\n%s", want.unit, want.mnemonic, got, nativegen.Describe(units[want.unit]))
		}
		if !strings.Contains(joined, "asm unit "+want.unit+": proven equal to its Oak body") {
			t.Errorf("%s must be proven; diagnostics:\n%s", want.unit, joined)
		}
	}
	// A guarded read and a float result keep the branch.
	for _, name := range []string{"guarded", "fpick"} {
		if got := counts(name); got["csel"] != 0 || got["csinc"] != 0 {
			t.Errorf("%s must keep its branch, got %v:\n%s", name, got, nativegen.Describe(units[name]))
		}
	}
	// The loop body holds the select and no branch other than the loop's own.
	if got := counts("clamp_sum"); got["csel"] < 1 {
		t.Errorf("clamp_sum must select inside its loop, got %v:\n%s", got, nativegen.Describe(units["clamp_sum"]))
	}
	if nativegen.ValueSelects(units["clamp_sum"]) < 1 {
		t.Errorf("clamp_sum must report a value select, got %d", nativegen.ValueSelects(units["clamp_sum"]))
	}
	_, code, abnormal := buildAndRunFrom(t, "native_value_select", comp)
	if abnormal || code != 45 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 45\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_value_select_c", New().WithSource("value_select.oak", nativeValueSelectProgram)); abnormal || code != 45 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 45", code, abnormal)
	}
}
