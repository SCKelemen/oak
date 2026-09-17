package asm

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func callResultLoop(t *testing.T, body string) (*pathExecutor, loopShape, int) {
	t.Helper()
	unit, errs := ParseUnit("loop.oakasm", "repeat: () -> u64 = {\nloop:\n"+body+"\n  b loop\ndone:\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	x := &pathExecutor{arch: ArchArm64, items: unit.Functions[0].Items, fn: unit.Functions[0]}
	shape := loopShape{header: 0, bodyStart: 1, bodyEnd: len(x.items) - 3}
	at := -1
	for pc, item := range x.items {
		if instr, ok := item.(Instruction); ok && instr.Mnemonic == "bl" && instr.Operands[0].(Symbol).Name == "make" {
			at = pc
		}
	}
	if at < 0 {
		t.Fatal("no call to make")
	}
	return x, shape, at
}

func TestLoopCallResultAddress(t *testing.T) {
	state := &symbolicState{disp: 80, regs: map[int]*term{21: frameAddressTerm(resultAreaBase)}}
	for _, tc := range []struct {
		name, body string
		want       int64
		ok         bool
	}{
		{"stack area", "add x8, sp, #32\nbl make", -48, true},
		{"address chain", "add x9, sp, #48\nsub x10, x9, #16\nmov x8, x10\nbl make", -48, true},
		{"parked result field", "add x8, x21, #8\nbl make", resultAreaBase + 8, true},
		{"base written later", "mov x8, x21\nbl make\nadd x21, x21, #8", 0, false},
		{"missing base", "mov x8, x22\nbl make", 0, false},
		{"caller saved across call", "add x9, sp, #32\nbl other\nmov x8, x9\nbl make", 0, false},
		{"pair load kills second", "add x8, sp, #32\nldp x9, x8, [sp]\nbl make", 0, false},
		{"writeback changes base", "add x8, sp, #32\nstr x9, [x8], #8\nbl make", 0, false},
		{"narrow pointer", "add x8, sp, #32\nmov w8, w8\nbl make", 0, false},
		{"variable offset", "add x8, sp, x0\nbl make", 0, false},
		{"join", "add x8, sp, #32\njoin:\nbl make", 0, false},
		{"moving stack", "sub sp, sp, #16\nadd x8, sp, #32\nbl make\nadd sp, sp, #16", 0, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			x, shape, at := callResultLoop(t, tc.body)
			got, ok := x.loopFrameAddress(shape, state, at, Register{Class: ClassX, Num: 8})
			if ok != tc.ok || ok && got != tc.want {
				t.Fatalf("got (%d, %v), want (%d, %v)", got, ok, tc.want, tc.ok)
			}
		})
	}
}

func TestLoopCallResultSlotWidths(t *testing.T) {
	x, shape, _ := callResultLoop(t, "add x8, sp, #32\nbl make")
	callee, err := parseSignatureWithBody("make: () -> R = R { a: u64(0), b: u64(0), flag: true, byte: u8(0), half: u16(0) }")
	if err != nil {
		t.Fatal(err)
	}
	x.fn.Callees = map[string]*ast.FunctionStatement{"make": callee}
	x.fn.Composites = map[string]Composite{"R": {Size: 24, Fields: []CompositeField{
		{Name: "a", Offset: 0, Size: 8, Scalar: "u64"},
		{Name: "b", Offset: 8, Size: 8, Scalar: "u64"},
		{Name: "flag", Offset: 16, Size: 4, Scalar: "Bool"},
		{Name: "byte", Offset: 20, Size: 1, Scalar: "u8"},
		{Name: "half", Offset: 22, Size: 2, Scalar: "u16"},
	}}}
	for _, overlap := range []bool{false, true} {
		slots := map[int64]int64{-80: 8} // an unrelated spill remains intact
		want := map[int64]int64{-80: 8, -48: 8, -40: 8, -32: 4, -28: 1, -26: 2}
		if overlap {
			slots[-32] = 8
			want[-27] = 1 // this byte is carried only for the explicit spill
		}
		if reason, ok := x.addCallResultSlots(shape, &symbolicState{disp: 80}, slots); !ok {
			t.Fatal(reason)
		}
		if !reflect.DeepEqual(slots, want) {
			t.Fatalf("overlap=%v: slots %v, want %v", overlap, slots, want)
		}
	}
}
