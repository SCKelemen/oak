package machine

import (
	"reflect"
	"strings"
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

func TestLeafReallocationEnablesEmptyFrame(t *testing.T) {
	input := calleeSaveFixture(
		ins("add", w(19), w(0), w(1)),
		ins("lsl", w(20), w(19), imm(2)),
		ins("sub", w(0), w(20), w(19)),
	)
	stable, stableAllocation, err := Reallocate(input)
	if err != nil {
		t.Fatal(err)
	}
	if stableAllocation.LeafEvicted != 0 || stableAllocation.LeafRetained != 2 || !strings.Contains(text(stable.Items), "add w19, w0, w1") {
		t.Fatalf("default reallocation changed the stable coloring:\n%s", text(stable.Items))
	}
	reallocated, allocation, err := ReallocateWithOptions(input, nil, AllocationOptions{EvictLeafCalleeSaves: true})
	if err != nil {
		t.Fatal(err)
	}
	if allocation.Renamed != 2 || allocation.LeafEvicted != 2 {
		t.Fatalf("renamed/evicted = %d/%d, want 2/2\n%s", allocation.Renamed, allocation.LeafEvicted, text(reallocated.Items))
	}
	trimmed, sites, err := TrimCalleeSaves(reallocated)
	if err != nil {
		t.Fatal(err)
	}
	if sites != 2 {
		t.Fatalf("trimmed sites = %d, want x19 and x20\n%s", sites, text(trimmed.Items))
	}
	elided, frames, err := ElideEmptyFrame(trimmed)
	if err != nil {
		t.Fatal(err)
	}
	if frames != 1 || elided.Frame != 0 {
		t.Fatalf("elided frames = %d, frame = %d", frames, elided.Frame)
	}
	want := "add w9, w0, w1\nlsl w10, w9, #2\nsub w0, w10, w9\nret\n"
	if got := text(elided.Items); got != want {
		t.Fatalf("leaf frame remained:\n%s\nwant:\n%s", got, want)
	}
	if !reflect.DeepEqual(elided.Clobbers, []asm.Register{x(9), x(10), x(0)}) {
		t.Fatalf("clobbers = %v", elided.Clobbers)
	}
}

func TestLeafReallocationPrefersCopyCoalescing(t *testing.T) {
	input := calleeSaveFixture(
		ins("mov", w(19), w(0)),
		ins("add", w(0), w(19), w(1)),
	)
	reallocated, allocation, err := ReallocateWithOptions(input, nil, AllocationOptions{EvictLeafCalleeSaves: true})
	if err != nil {
		t.Fatal(err)
	}
	if allocation.Coalesced != 1 {
		t.Fatalf("coalesced = %d, want parameter copy removed\n%s", allocation.Coalesced, text(reallocated.Items))
	}
	if allocation.LeafEvicted != 0 {
		t.Fatalf("copy coalescing was counted as leaf eviction: %d", allocation.LeafEvicted)
	}
	trimmed, sites, err := TrimCalleeSaves(reallocated)
	if err != nil {
		t.Fatal(err)
	}
	if sites != 2 {
		t.Fatalf("trimmed sites = %d, want x19 and x20\n%s", sites, text(trimmed.Items))
	}
	elided, frames, err := ElideEmptyFrame(trimmed)
	if err != nil {
		t.Fatal(err)
	}
	if frames != 1 {
		t.Fatalf("elided frames = %d\n%s", frames, text(elided.Items))
	}
	want := "add w0, w0, w1\nret\n"
	if got := text(elided.Items); got != want {
		t.Fatalf("copy was not coalesced:\n%s\nwant:\n%s", got, want)
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
