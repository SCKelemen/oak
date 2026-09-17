package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/opt"
)

func TestElideGlobalLoadMasksAtExactWidths(t *testing.T) {
	items := append(globalAddressPair(17, "byte"),
		ins("strb", wr(0), asm.Memory{Base: xr(17)}),
		ins("ldrb", wr(0), asm.Memory{Base: xr(17)}),
	)
	items = append(items, globalAddressPair(16, "half")...)
	items = append(items,
		ins("strh", wr(2), asm.Memory{Base: xr(16)}),
		ins("ldrh", wr(3), asm.Memory{Base: xr(16)}),
		ins("ret"),
	)
	fn := globalAddressFunction(items)
	fn.Globals = map[string]asm.Global{
		"byte": {Type: "u8", Bits: 8},
		"half": {Type: "u16", Bits: 16},
	}
	if n := forwardGlobalLoads(fn); n != 2 {
		t.Fatalf("forwarded %d loads, want two:\n%s", n, Describe(fn))
	}
	if n := elideGlobalLoadMasks(fn); n != 2 {
		t.Fatalf("elided %d masks, want two:\n%s", n, Describe(fn))
	}
	text := Describe(fn)
	if strings.Contains(text, "and") || strings.Contains(text, "mov w0, w0") ||
		!strings.Contains(text, "mov w3, w2") {
		t.Fatalf("unexpected normalized forwarding spelling:\n%s", text)
	}
	if n := elideGlobalLoadMasks(fn); n != 0 {
		t.Fatalf("pass is not idempotent: elided %d again", n)
	}

	transform, found := Registry().Lookup(TransformGlobalLoadMasks)
	if !found {
		t.Fatal("missing global-load mask-elision candidate")
	}
	if gated, ok := transform.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("global-load mask elision must require a semantic verdict")
	}
	plain := opt.Identity(PlainLane(Lane{Arch: asm.ArchArm64, Schedule: true}))
	if transform.Apply(plain) != nil {
		t.Fatal("global-load mask elision must wait for its forwarding parent")
	}
	parentLane := plain.Config.(Lane)
	parentLane.ForwardGlobalLoads = true
	parent := opt.Identity(parentLane)
	next := transform.Apply(parent)
	if next == nil || !next.Config.(Lane).ElideGlobalLoadMasks ||
		PlainLane(Lane{ElideGlobalLoadMasks: true}).ElideGlobalLoadMasks {
		t.Fatal("global-load mask-elision toggle or identity fallback")
	}
}

func TestElideGlobalLoadMaskRefusals(t *testing.T) {
	pair := func(global asm.Global, store, mask asm.Instruction) *asm.Function {
		items := append(globalAddressPair(17, "cell"), store, mask, ins("ret"))
		fn := globalAddressFunction(items)
		fn.Globals = map[string]asm.Global{"cell": global}
		return fn
	}
	byteStore := ins("strb", wr(0), asm.Memory{Base: xr(17)})
	byteMask := ins("and", wr(1), wr(0), asm.Immediate{Value: 0xff})
	for name, fn := range map[string]*asm.Function{
		"aggregate":        pair(asm.Global{Type: "[1]u8", Aggregate: true, Size: 1}, byteStore, byteMask),
		"wrong width":      pair(asm.Global{Type: "u16", Bits: 16}, byteStore, byteMask),
		"wrong mask":       pair(asm.Global{Type: "u8", Bits: 8}, byteStore, ins("and", wr(1), wr(0), asm.Immediate{Value: 0x7f})),
		"shifted mask":     pair(asm.Global{Type: "u8", Bits: 8}, byteStore, ins("and", wr(1), wr(0), asm.Immediate{Value: 0xff, Shift: 1})),
		"source mismatch":  pair(asm.Global{Type: "u8", Bits: 8}, byteStore, ins("and", wr(1), wr(2), asm.Immediate{Value: 0xff})),
		"wrong store":      pair(asm.Global{Type: "u8", Bits: 8}, ins("strh", wr(0), asm.Memory{Base: xr(17)}), byteMask),
		"offset store":     pair(asm.Global{Type: "u8", Bits: 8}, ins("strb", wr(0), asm.Memory{Base: xr(17), Offset: 1}), byteMask),
		"conditional mask": pair(asm.Global{Type: "u8", Bits: 8}, byteStore, asm.Instruction{Mnemonic: "and", Cond: "eq", Operands: byteMask.Operands}),
		"x registers":      pair(asm.Global{Type: "u8", Bits: 8}, ins("strb", xr(0), asm.Memory{Base: xr(17)}), ins("and", xr(1), xr(0), asm.Immediate{Value: 0xff})),
	} {
		t.Run(name, func(t *testing.T) {
			before := Describe(fn)
			if n := elideGlobalLoadMasks(fn); n != 0 || Describe(fn) != before {
				t.Fatalf("unsafe shape elided %d masks:\n%s", n, Describe(fn))
			}
		})
	}
	withLabel := pair(asm.Global{Type: "u8", Bits: 8}, byteStore, byteMask)
	withLabel.Items = append(withLabel.Items[:3], append([]asm.Item{asm.Label{Name: "join"}}, withLabel.Items[3:]...)...)
	if n := elideGlobalLoadMasks(withLabel); n != 0 {
		t.Fatalf("mask across a label elided %d times", n)
	}
	wrongSymbol := pair(asm.Global{Type: "u8", Bits: 8}, byteStore, byteMask)
	wrongSymbol.Items[1] = ins("add", xr(17), xr(17), asm.Symbol{Name: "other", Lo12: true})
	if n := elideGlobalLoadMasks(wrongSymbol); n != 0 {
		t.Fatalf("mismatched address materialization elided %d times", n)
	}
}
