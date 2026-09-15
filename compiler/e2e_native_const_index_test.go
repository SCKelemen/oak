package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Constant span indices the typechecker proved (docs/spec/50-borrowing.md,
// facts from asserts and exact lengths) are lowered without a guard on the
// AArch64 lane: the constant lands in a register the checker knows
// (Oak.Assembler.constant_index_bound) and the span's proven minimum —
// from `cmp wL, #K; b.lo` or the exact `cmp wL, #K; b.ne` an assert or a
// `len(v) == K` test spells — admits the read.
const nativeConstIndexProgram = `
first_of_one: (state: []u64): u64 {
  assert(len(state) == u32(1))
  state[0]
}

fourth_or_zero: (v: []u8): u32 = len(v) >= u32(4) ? u32(v[3]) | u32(0)

main: (): i32 {
  one: [1]u64 = [1]u64{u64(40)}
  quad: [4]u8 = [4]u8{u8(1), u8(1), u8(1), u8(2)}
  i32_bits_u32(u32_trunc_u64(first_of_one(view(&one))) + fourth_or_zero(view(&quad)))
}
`

func TestE2ENativeConstantIndexElision(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("const_index.oak", nativeConstIndexProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"first_of_one", "fourth_or_zero"} {
		if !strings.Contains(joined, fn+": 1 element guard(s) elided") {
			t.Errorf("%s: the constant read must be elided:\n%s", fn, joined)
		}
		if !strings.Contains(joined, "asm unit "+fn+": proven equal") {
			t.Errorf("%s must stay proven:\n%s", fn, joined)
		}
	}
	for _, f := range model.AsmFunctions {
		if f.Name != "first_of_one" && f.Name != "fourth_or_zero" {
			continue
		}
		guards := 0
		for _, item := range f.Items {
			if instr, isInstr := item.(asm.Instruction); isInstr && instr.Mnemonic == "b." && instr.Cond == "hs" {
				guards++
			}
		}
		if guards != 0 {
			t.Errorf("%s must carry no element guard, found %d", f.Name, guards)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_const_index", comp); abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
}
