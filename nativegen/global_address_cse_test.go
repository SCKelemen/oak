package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/opt"
)

func globalAddressFunction(items []asm.Item) *asm.Function {
	return &asm.Function{
		Name:     "global_addresses",
		Arch:     asm.ArchArm64,
		Items:    items,
		Clobbers: []asm.Register{xr(9), xr(10), xr(11), xr(12), xr(13), xr(14), xr(15), xr(16), xr(17)},
		Globals:  map[string]asm.Global{"st": {Type: "u8", Bits: 8}, "other": {Type: "u8", Bits: 8}, "table": {Type: "[4]u8", Aggregate: true, Size: 4}},
	}
}

func globalAddressPair(reg int, symbol string) []asm.Item {
	return []asm.Item{
		ins("adrp", xr(reg), asm.Symbol{Name: symbol}),
		ins("add", xr(reg), xr(reg), asm.Symbol{Name: symbol, Lo12: true}),
	}
}

func TestShareGlobalAddressesAcrossAcyclicCFG(t *testing.T) {
	items := []asm.Item{
		ins("adrp", xr(9), asm.Symbol{Name: "st"}),
		ins("adrp", xr(10), asm.Symbol{Name: "st"}),
		ins("mov", wr(2), wr(2)),
		ins("add", xr(9), xr(9), asm.Symbol{Name: "st", Lo12: true}),
		ins("add", xr(10), xr(10), asm.Symbol{Name: "st", Lo12: true}),
		ins("strb", wr(0), asm.Memory{Base: xr(9)}),
		ins("ldrb", wr(1), asm.Memory{Base: xr(10)}),
		ins("cmp", wr(2), asm.Immediate{Value: 0}),
		asm.Instruction{Mnemonic: "b.", Cond: "eq", Operands: []asm.Operand{asm.Symbol{Name: "else"}}},
	}
	items = append(items, globalAddressPair(11, "st")...)
	items = append(items,
		ins("ldrb", wr(0), asm.Memory{Base: xr(11)}),
		ins("b", asm.Symbol{Name: "done"}),
		asm.Label{Name: "else"},
	)
	items = append(items, globalAddressPair(12, "st")...)
	items = append(items,
		ins("ldrb", wr(0), asm.Memory{Base: xr(12)}),
		asm.Label{Name: "done"},
		ins("ret"),
	)
	fn := globalAddressFunction(items)
	if n := shareGlobalAddresses(fn); n != 3 {
		t.Fatalf("shared %d global addresses, want three:\n%s", n, Describe(fn))
	}
	text := Describe(fn)
	if strings.Count(text, "adrp") != 1 || strings.Count(text, ":lo12:st") != 1 ||
		strings.Count(text, "[x17]") != 4 {
		t.Fatalf("the scalar global address was not carried in x17:\n%s", text)
	}
	if n := shareGlobalAddresses(fn); n != 0 {
		t.Fatalf("pass is not idempotent: shared %d again", n)
	}
	transform, found := Registry().Lookup(TransformGlobalAddresses)
	if !found {
		t.Fatal("missing scalar-global address candidate")
	}
	if gated, ok := transform.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("scalar-global address sharing must require a semantic verdict")
	}
	if !transform.Apply(opt.Identity(PlainLane(Lane{Arch: asm.ArchArm64}))).Config.(Lane).ShareGlobalAddresses ||
		PlainLane(Lane{ShareGlobalAddresses: true}).ShareGlobalAddresses {
		t.Fatal("scalar-global candidate toggle or identity fallback")
	}
}

func TestShareGlobalAddressesStopsAndRestartsAtCall(t *testing.T) {
	var items []asm.Item
	items = append(items, globalAddressPair(9, "st")...)
	items = append(items, ins("strb", wr(0), asm.Memory{Base: xr(9)}))
	items = append(items, globalAddressPair(10, "st")...)
	items = append(items,
		ins("ldrb", wr(1), asm.Memory{Base: xr(10)}),
		ins("bl", asm.Symbol{Name: "helper"}),
	)
	items = append(items, globalAddressPair(11, "st")...)
	items = append(items, ins("strb", wr(0), asm.Memory{Base: xr(11)}))
	items = append(items, globalAddressPair(12, "st")...)
	items = append(items,
		ins("ldrb", wr(1), asm.Memory{Base: xr(12)}),
		ins("ret"),
	)
	fn := globalAddressFunction(items)
	if n := shareGlobalAddresses(fn); n != 2 {
		t.Fatalf("shared %d call-delimited addresses, want two:\n%s", n, Describe(fn))
	}
	if text := Describe(fn); strings.Count(text, "adrp") != 2 || strings.Count(text, ":lo12:st") != 2 {
		t.Fatalf("the address must be recomputed after the call:\n%s", text)
	}
}

func TestShareGlobalAddressRefusals(t *testing.T) {
	base := func(symbol string) []asm.Item {
		var items []asm.Item
		items = append(items, globalAddressPair(9, symbol)...)
		items = append(items, ins("ldrb", wr(0), asm.Memory{Base: xr(9)}))
		items = append(items, globalAddressPair(10, symbol)...)
		items = append(items, ins("ldrb", wr(1), asm.Memory{Base: xr(10)}), ins("ret"))
		return items
	}
	tooWide := base("st")
	gap := make([]asm.Item, globalAddressMaterializationSpan)
	for i := range gap {
		gap[i] = ins("mov", wr(2), wr(2))
	}
	tooWide = append(append(append([]asm.Item(nil), tooWide[:1]...), gap...), tooWide[1:]...)
	allScratchUsed := base("st")
	for reg := 9; reg <= 17; reg++ {
		allScratchUsed = append(allScratchUsed[:len(allScratchUsed)-1], ins("mov", xr(reg), xr(reg)), allScratchUsed[len(allScratchUsed)-1])
	}
	liveAcrossLabel := []asm.Item{
		ins("adrp", xr(9), asm.Symbol{Name: "st"}),
		ins("add", xr(9), xr(9), asm.Symbol{Name: "st", Lo12: true}),
		ins("b", asm.Symbol{Name: "use"}),
		asm.Label{Name: "use"},
		ins("ldrb", wr(0), asm.Memory{Base: xr(9)}),
	}
	liveAcrossLabel = append(liveAcrossLabel, globalAddressPair(10, "st")...)
	liveAcrossLabel = append(liveAcrossLabel, ins("ldrb", wr(1), asm.Memory{Base: xr(10)}), ins("ret"))
	for name, items := range map[string][]asm.Item{
		"one site":                  base("st")[:3],
		"unknown symbol":            base("missing"),
		"aggregate global":          base("table"),
		"intervening read":          append(append([]asm.Item(nil), base("st")[:1]...), append([]asm.Item{ins("mov", xr(11), xr(9))}, base("st")[1:]...)...),
		"intervening write":         append(append([]asm.Item(nil), base("st")[:1]...), append([]asm.Item{ins("mov", xr(9), xr(11))}, base("st")[1:]...)...),
		"label inside pair":         append(append([]asm.Item(nil), base("st")[:1]...), append([]asm.Item{asm.Label{Name: "inside"}}, base("st")[1:]...)...),
		"materialization too wide":  tooWide,
		"destination crosses label": liveAcrossLabel,
		"machine loop":              append([]asm.Item{asm.Label{Name: "loop"}, ins("cbnz", wr(2), asm.Symbol{Name: "loop"})}, base("st")...),
		"no free scratch":           allScratchUsed,
	} {
		t.Run(name, func(t *testing.T) {
			fn := globalAddressFunction(items)
			before := Describe(fn)
			if n := shareGlobalAddresses(fn); n != 0 || Describe(fn) != before {
				t.Fatalf("unsafe shape shared %d addresses:\n%s", n, Describe(fn))
			}
		})
	}
	wrongLow := base("st")
	wrongLow[4] = ins("add", xr(10), xr(10), asm.Symbol{Name: "other", Lo12: true})
	fn := globalAddressFunction(wrongLow)
	if n := shareGlobalAddresses(fn); n != 0 {
		t.Fatalf("mismatched lo12 symbol shared %d addresses", n)
	}
	undeclared := globalAddressFunction(base("st"))
	undeclared.Clobbers = []asm.Register{xr(9), xr(10)}
	if n := shareGlobalAddresses(undeclared); n != 0 {
		t.Fatalf("undeclared scratch shared %d addresses", n)
	}
}
