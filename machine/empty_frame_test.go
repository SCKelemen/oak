package machine

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func emptyFrameFixture(body ...asm.Item) *asm.Function {
	items := []asm.Item{ins("sub", sp(), sp(), imm(80))}
	items = append(items, body...)
	items = append(items, label("return"), ins("add", sp(), sp(), imm(80)), ins("ret"))
	return &asm.Function{Name: "f", Arch: asm.ArchArm64, Frame: 80, Items: items, Clobbers: []asm.Register{x(9)}}
}

func TestElideEmptyFrameRemovesExactAdjustments(t *testing.T) {
	input := emptyFrameFixture(ins("mov", w(0), w(1)))
	before := cloneFunction(input)
	elided, frames, err := ElideEmptyFrame(input)
	if err != nil {
		t.Fatal(err)
	}
	if frames != 1 || elided.Frame != 0 {
		t.Fatalf("frames = %d, frame = %d", frames, elided.Frame)
	}
	want := "mov w0, w1\nreturn:\nret\n"
	if got := text(elided.Items); got != want {
		t.Fatalf("elided frame:\n%s\nwant:\n%s", got, want)
	}
	if !reflect.DeepEqual(input, before) {
		t.Fatal("empty-frame elision changed its input")
	}
}

func TestElideEmptyFrameRefusesStackUse(t *testing.T) {
	input := emptyFrameFixture(ins("ldr", x(0), mem(sp(), 16)))
	assertEmptyFrameUnchanged(t, input)
}

func TestElideEmptyFrameRefusesCalls(t *testing.T) {
	input := emptyFrameFixture(ins("bl", sym("callee")))
	assertEmptyFrameUnchanged(t, input)
}

func TestElideEmptyFrameRefusesMismatchedAdjustment(t *testing.T) {
	input := emptyFrameFixture(ins("mov", w(0), w(1)))
	grow := input.Items[len(input.Items)-2].(asm.Instruction)
	grow.Operands[2] = imm(96)
	input.Items[len(input.Items)-2] = grow
	assertEmptyFrameUnchanged(t, input)
}

func TestElideEmptyFrameRefusesMultipleReturns(t *testing.T) {
	input := emptyFrameFixture(ins("mov", w(0), w(1)))
	input.Items = append(input.Items, label("again"), ins("ret"))
	assertEmptyFrameUnchanged(t, input)
}

func TestElideEmptyFrameRefusesFrameAuthority(t *testing.T) {
	for name, decorate := range map[string]func(*asm.Function){
		"stack arguments": func(input *asm.Function) { input.StackArgs = 8 },
		"frame objects": func(input *asm.Function) {
			input.FrameObjects = []asm.FrameObject{{Offset: 16, Size: 8, Name: "local"}}
		},
	} {
		t.Run(name, func(t *testing.T) {
			input := emptyFrameFixture(ins("mov", w(0), w(1)))
			decorate(input)
			assertEmptyFrameUnchanged(t, input)
		})
	}
}

func assertEmptyFrameUnchanged(t *testing.T, input *asm.Function) {
	t.Helper()
	want := cloneFunction(input)
	elided, frames, err := ElideEmptyFrame(input)
	if err != nil {
		t.Fatal(err)
	}
	if frames != 0 || !reflect.DeepEqual(elided, want) || !reflect.DeepEqual(input, want) {
		t.Fatalf("refused frame changed: frames=%d\n%s", frames, text(elided.Items))
	}
}
