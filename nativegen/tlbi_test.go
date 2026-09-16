package nativegen

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func TestTLBIClearsMemoryForwardingState(t *testing.T) {
	g := &generator{}
	g.hold(heldKey{base: spBase, off: 16}, heldSlot{reg: 9, wide: true})
	g.put(asm.Instruction{
		Mnemonic: "tlbi",
		Operands: []asm.Operand{asm.Option{Name: "vmalls12e1is"}},
	})
	if len(g.held) != 0 {
		t.Fatalf("TLBI retained %d forwarded memory values", len(g.held))
	}
	if len(g.items) != 1 {
		t.Fatalf("TLBI emitted %d items, want 1", len(g.items))
	}
	got, ok := g.items[0].(asm.Instruction)
	if !ok || got.Mnemonic != "tlbi" || len(got.Operands) != 1 {
		t.Fatalf("emitted TLBI changed: %#v", g.items[0])
	}
}
