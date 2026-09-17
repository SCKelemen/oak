package machine

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func calleeSaveFixture(body ...asm.Item) *asm.Function {
	items := []asm.Item{
		ins("sub", sp(), sp(), imm(80)),
		ins("stp", x(19), x(20), mem(sp(), 16)),
	}
	items = append(items, body...)
	items = append(items,
		ins("ldp", x(19), x(20), mem(sp(), 16)),
		ins("add", sp(), sp(), imm(80)),
		ins("ret"),
	)
	return &asm.Function{
		Name: "f", Arch: asm.ArchArm64, Frame: 80, Items: items,
		Clobbers: []asm.Register{x(9), x(19), x(20)},
	}
}

func TestTrimCalleeSavesRemovesUnusedPairAndDeadHome(t *testing.T) {
	input := calleeSaveFixture(
		ins("mov", w(20), w(1)),
		ins("mov", w(0), w(2)),
	)
	before := cloneFunction(input)
	trimmed, sites, err := TrimCalleeSaves(input)
	if err != nil {
		t.Fatal(err)
	}
	if sites != 3 {
		t.Fatalf("sites = %d, want one dead home and two unused saved registers", sites)
	}
	want := "sub sp, sp, #80\nmov w0, w2\nadd sp, sp, #80\nret\n"
	if got := text(trimmed.Items); got != want {
		t.Fatalf("trimmed frame:\n%s\nwant:\n%s", got, want)
	}
	if !reflect.DeepEqual(trimmed.Clobbers, []asm.Register{x(9)}) {
		t.Fatalf("clobbers = %v", trimmed.Clobbers)
	}
	if !reflect.DeepEqual(input, before) {
		t.Fatal("trimming changed its input")
	}
}

func TestTrimCalleeSavesNarrowsPairAtOriginalOffset(t *testing.T) {
	input := calleeSaveFixture(
		ins("mov", w(20), w(1)),
		ins("add", w(0), w(19), w(2)),
	)
	trimmed, sites, err := TrimCalleeSaves(input)
	if err != nil {
		t.Fatal(err)
	}
	if sites != 2 {
		t.Fatalf("sites = %d, want one dead home and x20", sites)
	}
	want := "sub sp, sp, #80\nstr x19, [sp,#16]\nadd w0, w19, w2\nldr x19, [sp,#16]\nadd sp, sp, #80\nret\n"
	if got := text(trimmed.Items); got != want {
		t.Fatalf("narrowed frame:\n%s\nwant:\n%s", got, want)
	}
	if !reflect.DeepEqual(trimmed.Clobbers, []asm.Register{x(9), x(19)}) {
		t.Fatalf("clobbers = %v", trimmed.Clobbers)
	}

	// Keeping the second member retains its own slot rather than moving it
	// into the first member's offset.
	second := calleeSaveFixture(ins("add", w(0), w(20), w(2)))
	trimmed, sites, err = TrimCalleeSaves(second)
	if err != nil || sites != 1 {
		t.Fatalf("second member: sites = %d, error = %v", sites, err)
	}
	want = "sub sp, sp, #80\nstr x20, [sp,#24]\nadd w0, w20, w2\nldr x20, [sp,#24]\nadd sp, sp, #80\nret\n"
	if got := text(trimmed.Items); got != want {
		t.Fatalf("second-member frame:\n%s\nwant:\n%s", got, want)
	}
}

func TestTrimCalleeSavesRefusesUnmatchedFrame(t *testing.T) {
	input := calleeSaveFixture(ins("mov", w(20), w(1)), ins("mov", w(0), w(2)))
	restore := input.Items[len(input.Items)-3].(asm.Instruction)
	restore.Operands[2] = mem(sp(), 32)
	input.Items[len(input.Items)-3] = restore
	before := cloneFunction(input)
	trimmed, sites, err := TrimCalleeSaves(input)
	if err != nil {
		t.Fatal(err)
	}
	if sites != 0 || !reflect.DeepEqual(trimmed, before) || !reflect.DeepEqual(input, before) {
		t.Fatalf("unmatched frame changed: sites=%d\n%s", sites, text(trimmed.Items))
	}
}

func TestTrimCalleeSavesRefusesMultipleReturns(t *testing.T) {
	input := calleeSaveFixture(ins("mov", w(20), w(1)), ins("mov", w(0), w(2)))
	input.Items = append(input.Items, label("again"), ins("ret"))
	before := cloneFunction(input)
	trimmed, sites, err := TrimCalleeSaves(input)
	if err != nil {
		t.Fatal(err)
	}
	if sites != 0 || !reflect.DeepEqual(trimmed, before) || !reflect.DeepEqual(input, before) {
		t.Fatalf("multi-return frame changed: sites=%d\n%s", sites, text(trimmed.Items))
	}
}
