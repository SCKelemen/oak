package semir

import "testing"

func TestMmioCatalogIsExactAndLegal(t *testing.T) {
	specs := Arm64MmioMembers()
	if len(specs) != 28 {
		t.Fatalf("MMIO catalog has %d members, want 28", len(specs))
	}
	seen := map[string]bool{}
	for _, spec := range specs {
		if seen[spec.Member] {
			t.Fatalf("duplicate MMIO member %q", spec.Member)
		}
		seen[spec.Member] = true
		if !spec.Legal() {
			t.Fatalf("catalog exposes illegal MMIO member %+v", spec)
		}
		if _, err := spec.Effect(); err != nil {
			t.Fatalf("catalog member %q has no effect: %v", spec.Member, err)
		}
	}
}

func TestMmioAuthoritySurfaceRejectsForbiddenAccesses(t *testing.T) {
	if _, ok := LookupArm64Mmio("mmio_read_wo_u32"); ok {
		t.Fatal("write-only u32 register unexpectedly exposes read")
	}
	if _, ok := LookupArm64Mmio("mmio_write_ro_u32"); ok {
		t.Fatal("read-only u32 register unexpectedly exposes write")
	}
	for _, name := range []string{
		"mmio_read_ro_u32", "mmio_read_rw_u32",
		"mmio_write_wo_u32", "mmio_write_rw_u32",
	} {
		if _, ok := LookupArm64Mmio(name); !ok {
			t.Fatalf("required MMIO member %q missing", name)
		}
	}
}

func TestMmioNaturalAlignment(t *testing.T) {
	cases := []struct {
		address uint64
		width   MmioWidth
		want    bool
	}{
		{0x1000, Mmio8, true},
		{0x1001, Mmio16, false},
		{0x1002, Mmio16, true},
		{0x1002, Mmio32, false},
		{0x1004, Mmio32, true},
		{0x1004, Mmio64, false},
		{0x1008, Mmio64, true},
	}
	for _, tc := range cases {
		if got := MmioAddressAligned(tc.address, tc.width); got != tc.want {
			t.Fatalf("aligned(%#x,%d)=%v want %v", tc.address, tc.width, got, tc.want)
		}
	}
}

func TestMmioLookupAllocatesNothing(t *testing.T) {
	allocs := testing.AllocsPerRun(1000, func() {
		spec, ok := LookupArm64Mmio("mmio_read_rw_u32")
		if !ok || spec.Operation != MmioRead || spec.Width != Mmio32 {
			panic("lookup failed")
		}
	})
	if allocs != 0 {
		t.Fatalf("MMIO lookup allocated %.2f objects per call; want zero", allocs)
	}
}
