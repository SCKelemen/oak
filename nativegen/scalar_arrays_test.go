package nativegen

import "testing"

// A scalar-replaced array owns only its hidden element homes. Its synthetic
// binding must not return offset zero (or any other phantom offset) to the
// frame-slot pool at its last use or when its scope closes.
func TestScalarArrayBindingDoesNotReleasePhantomSlot(t *testing.T) {
	newGenerator := func() *generator {
		return &generator{scopes: []map[string]slotBinding{{
			"acc": {sa: &scalarArray{elem: scalars["u32"], length: 2}},
		}}}
	}

	g := newGenerator()
	g.releaseDead(map[string]int{"acc": 3}, 3)
	if len(g.freeSlots8) != 0 || g.scopes[0]["acc"].freed {
		t.Fatalf("last-use release returned a scalar array's phantom slot: %v", g.freeSlots8)
	}

	g = newGenerator()
	g.popScope()
	if len(g.freeSlots8) != 0 {
		t.Fatalf("scope exit returned a scalar array's phantom slot: %v", g.freeSlots8)
	}
}
