package semir

import "testing"

func TestLegalAtomicOrder(t *testing.T) {
	cases := []struct {
		op    AtomicOperation
		order MemoryOrder
		want  bool
	}{
		{AtomicLoad, MemoryOrderRelaxed, true},
		{AtomicLoad, MemoryOrderAcquire, true},
		{AtomicLoad, MemoryOrderSeqCst, true},
		{AtomicLoad, MemoryOrderRelease, false},
		{AtomicLoad, MemoryOrderAcqRel, false},
		{AtomicStore, MemoryOrderRelaxed, true},
		{AtomicStore, MemoryOrderRelease, true},
		{AtomicStore, MemoryOrderSeqCst, true},
		{AtomicStore, MemoryOrderAcquire, false},
		{AtomicStore, MemoryOrderAcqRel, false},
		{AtomicRMW, MemoryOrderRelaxed, true},
		{AtomicRMW, MemoryOrderAcquire, true},
		{AtomicRMW, MemoryOrderRelease, true},
		{AtomicRMW, MemoryOrderAcqRel, true},
		{AtomicRMW, MemoryOrderSeqCst, true},
		{AtomicFence, MemoryOrderAcquire, true},
		{AtomicFence, MemoryOrderRelease, true},
		{AtomicFence, MemoryOrderAcqRel, true},
		{AtomicFence, MemoryOrderSeqCst, true},
		{AtomicFence, MemoryOrderRelaxed, false},
	}
	for _, tc := range cases {
		if got := LegalAtomicOrder(tc.op, tc.order); got != tc.want {
			t.Fatalf("LegalAtomicOrder(%q, %q) = %v, want %v", tc.op, tc.order, got, tc.want)
		}
	}
}

func TestAtomicEffectRetainsOrder(t *testing.T) {
	effect, err := AtomicEffect(AtomicRMW, MemoryOrderAcqRel)
	if err != nil {
		t.Fatal(err)
	}
	if effect.Namespace != "Memory" || effect.Name != "AtomicRMW" {
		t.Fatalf("unexpected effect: %#v", effect)
	}
	if len(effect.Parameters) != 1 || effect.Parameters[0] != "acq-rel" {
		t.Fatalf("atomic order lost from effect: %#v", effect)
	}
}

func TestAtomicCarrierAllowed(t *testing.T) {
	for _, base := range []string{"u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"} {
		if !AtomicCarrierAllowed(base) {
			t.Fatalf("expected %s to be allowed", base)
		}
	}
	for _, base := range []string{"int", "uint", "ptr", "uptr", "Bool", "record"} {
		if AtomicCarrierAllowed(base) {
			t.Fatalf("expected %s to be rejected", base)
		}
	}
}

func TestValidateAtomicType(t *testing.T) {
	if err := ValidateAtomicType(Type{Kind: TypeAtomic, Base: "u32"}); err != nil {
		t.Fatalf("valid atomic rejected: %v", err)
	}
	if err := ValidateAtomicType(Type{Kind: TypeAtomic, Base: "ptr"}); err == nil {
		t.Fatal("pointer atomic unexpectedly accepted in v1")
	}
}

func TestVolatileEffectIsNotAtomic(t *testing.T) {
	effect, err := VolatileEffect(VolatileRead)
	if err != nil {
		t.Fatal(err)
	}
	if effect.Namespace != "Memory" || effect.Name != "VolatileRead" || len(effect.Parameters) != 0 {
		t.Fatalf("unexpected volatile effect: %#v", effect)
	}
}
