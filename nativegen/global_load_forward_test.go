package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/opt"
)

func TestForwardGlobalLoadsAtExactWidths(t *testing.T) {
	var items []asm.Item
	for _, site := range []struct {
		name         string
		bits         int
		store, load  string
		source, dest asm.Register
	}{
		{"byte", 8, "strb", "ldrb", wr(0), wr(1)},
		{"half", 16, "strh", "ldrh", wr(2), wr(3)},
		{"word", 32, "str", "ldr", wr(4), wr(4)},
		{"double", 64, "str", "ldr", xr(5), xr(6)},
	} {
		items = append(items, globalAddressPair(17, site.name)...)
		items = append(items,
			ins(site.store, site.source, asm.Memory{Base: xr(17)}),
			ins(site.load, site.dest, asm.Memory{Base: xr(17)}),
		)
	}
	items = append(items, ins("ret"))
	fn := globalAddressFunction(items)
	fn.Globals = map[string]asm.Global{
		"byte": {Type: "u8", Bits: 8}, "half": {Type: "u16", Bits: 16},
		"word": {Type: "u32", Bits: 32}, "double": {Type: "u64", Bits: 64},
	}
	if n := forwardGlobalLoads(fn); n != 4 {
		t.Fatalf("forwarded %d global loads, want four:\n%s", n, Describe(fn))
	}
	text := Describe(fn)
	for _, want := range []string{"and w1, w0, #255", "and w3, w2, #65535", "mov x6, x5"} {
		if !strings.Contains(text, want) {
			t.Fatalf("missing %q after forwarding:\n%s", want, text)
		}
	}
	if strings.Contains(text, "ldr w4, [x17]") || strings.Count(text, "ldr") != 0 {
		t.Fatalf("full-width reloads survived:\n%s", text)
	}
	if n := forwardGlobalLoads(fn); n != 0 {
		t.Fatalf("pass is not idempotent: forwarded %d again", n)
	}
	transform, found := Registry().Lookup(TransformForwardGlobalLoads)
	if !found {
		t.Fatal("missing global-load forwarding candidate")
	}
	if gated, ok := transform.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("global-load forwarding must require a semantic verdict")
	}
	plain := opt.Identity(PlainLane(Lane{Arch: asm.ArchArm64, Schedule: true}))
	if transform.Apply(plain) == nil || !transform.Apply(plain).Config.(Lane).ForwardGlobalLoads ||
		PlainLane(Lane{ForwardGlobalLoads: true}).ForwardGlobalLoads {
		t.Fatal("global-load forwarding toggle or identity fallback")
	}
}

func TestForwardGlobalLoadRefusals(t *testing.T) {
	pair := func(global asm.Global, store, load asm.Instruction) *asm.Function {
		items := append(globalAddressPair(17, "cell"), store, load, ins("ret"))
		fn := globalAddressFunction(items)
		fn.Globals = map[string]asm.Global{"cell": global}
		return fn
	}
	byteStore := ins("strb", wr(0), asm.Memory{Base: xr(17)})
	byteLoad := ins("ldrb", wr(1), asm.Memory{Base: xr(17)})
	for name, fn := range map[string]*asm.Function{
		"aggregate":        pair(asm.Global{Type: "[1]u8", Aggregate: true, Size: 1}, byteStore, byteLoad),
		"wrong width":      pair(asm.Global{Type: "u16", Bits: 16}, byteStore, byteLoad),
		"different offset": pair(asm.Global{Type: "u8", Bits: 8}, byteStore, ins("ldrb", wr(1), asm.Memory{Base: xr(17), Offset: 1})),
		"different base":   pair(asm.Global{Type: "u8", Bits: 8}, byteStore, ins("ldrb", wr(1), asm.Memory{Base: xr(16)})),
		"indexed":          pair(asm.Global{Type: "u8", Bits: 8}, byteStore, ins("ldrb", wr(1), asm.Memory{Base: xr(17), Index: func() *asm.Register { r := wr(2); return &r }()})),
		"signed load":      pair(asm.Global{Type: "i8", Bits: 8}, byteStore, ins("ldrsb", wr(1), asm.Memory{Base: xr(17)})),
		"conditional":      pair(asm.Global{Type: "u8", Bits: 8}, byteStore, asm.Instruction{Mnemonic: "ldrb", Cond: "eq", Operands: byteLoad.Operands}),
	} {
		t.Run(name, func(t *testing.T) {
			before := Describe(fn)
			if n := forwardGlobalLoads(fn); n != 0 || Describe(fn) != before {
				t.Fatalf("unsafe shape forwarded %d loads:\n%s", n, Describe(fn))
			}
		})
	}
	withLabel := pair(asm.Global{Type: "u8", Bits: 8}, byteStore, byteLoad)
	withLabel.Items = append(withLabel.Items[:3], append([]asm.Item{asm.Label{Name: "join"}}, withLabel.Items[3:]...)...)
	if n := forwardGlobalLoads(withLabel); n != 0 {
		t.Fatalf("load across a label forwarded %d times", n)
	}
	wrongSymbol := pair(asm.Global{Type: "u8", Bits: 8}, byteStore, byteLoad)
	wrongSymbol.Items[1] = ins("add", xr(17), xr(17), asm.Symbol{Name: "other", Lo12: true})
	if n := forwardGlobalLoads(wrongSymbol); n != 0 {
		t.Fatalf("mismatched address materialization forwarded %d times", n)
	}
}

func TestForwardDominatedZeroGlobalLoadAcrossJoin(t *testing.T) {
	items := append(globalAddressPair(17, "cell"),
		ins("str", xr(31), asm.Memory{Base: xr(17)}),
		ins("cbz", wr(0), asm.Symbol{Name: "join"}),
		ins("add", xr(10), xr(1), asm.Immediate{Value: 1}),
		asm.Label{Name: "join"},
		ins("ldr", xr(10), asm.Memory{Base: xr(17)}),
		ins("str", xr(10), asm.Memory{Base: xr(17)}),
		ins("ret"),
	)
	fn := globalAddressFunction(items)
	fn.Globals = map[string]asm.Global{"cell": {Type: "u64", Bits: 64}}
	if n := forwardGlobalLoads(fn); n != 1 {
		t.Fatalf("forwarded %d dominated loads, want one:\n%s", n, Describe(fn))
	}
	if text := Describe(fn); strings.Contains(text, "ldr x10") || !strings.Contains(text, "mov x10, xzr") {
		t.Fatalf("dominated zero load was not forwarded:\n%s", text)
	}
	if n := postScheduleCleanup(fn); n != 1 {
		t.Fatalf("post-schedule cleanup removed %d zero carriers, want one:\n%s", n, Describe(fn))
	}
	if text := Describe(fn); strings.Contains(text, "mov x10, xzr") || strings.Count(text, "str xzr, [x17]") != 2 {
		t.Fatalf("forwarded zero carrier was not retargeted into the store:\n%s", text)
	}
}

func TestForwardDominatedZeroGlobalLoadRefusals(t *testing.T) {
	makeFunction := func(between ...asm.Item) *asm.Function {
		items := append(globalAddressPair(17, "cell"), ins("str", xr(31), asm.Memory{Base: xr(17)}))
		items = append(items, between...)
		items = append(items, ins("ldr", xr(10), asm.Memory{Base: xr(17)}), ins("ret"))
		fn := globalAddressFunction(items)
		fn.Globals = map[string]asm.Global{"cell": {Type: "u64", Bits: 64}}
		return fn
	}
	for name, fn := range map[string]*asm.Function{
		"intervening store": makeFunction(ins("str", xr(2), asm.Memory{Base: xr(3)})),
		"call":              makeFunction(ins("bl", asm.Symbol{Name: "callee"})),
		"base clobber":      makeFunction(ins("mov", xr(17), xr(2))),
	} {
		t.Run(name, func(t *testing.T) {
			before := Describe(fn)
			if n := forwardDominatedZeroGlobalLoads(fn); n != 0 || Describe(fn) != before {
				t.Fatalf("unsafe dominated load forwarded %d times:\n%s", n, Describe(fn))
			}
		})
	}

	bypass := globalAddressFunction(append(globalAddressPair(17, "cell"),
		ins("cbz", wr(0), asm.Symbol{Name: "join"}),
		ins("str", xr(31), asm.Memory{Base: xr(17)}),
		asm.Label{Name: "join"},
		ins("ldr", xr(10), asm.Memory{Base: xr(17)}),
		ins("ret"),
	))
	bypass.Globals = map[string]asm.Global{"cell": {Type: "u64", Bits: 64}}
	if n := forwardDominatedZeroGlobalLoads(bypass); n != 0 {
		t.Fatalf("non-dominating store forwarded %d loads:\n%s", n, Describe(bypass))
	}
}
