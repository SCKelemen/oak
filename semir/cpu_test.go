package semir

import "testing"

func TestCPUFeatureCatalogIsExact(t *testing.T) {
	features := CPUFeatures()
	if len(features) != 3 {
		t.Fatalf("feature catalog has %d entries, want 3", len(features))
	}
	seenName, seenBit := map[string]bool{}, map[uint]bool{}
	for _, f := range features {
		if f.Name == "" || f.Arch == "" || f.BaselineMacro == "" || f.Attribute == "" {
			t.Fatalf("incomplete feature: %+v", f)
		}
		if seenName[f.Name] || seenBit[f.Bit] {
			t.Fatalf("duplicate feature name or bit: %+v", f)
		}
		seenName[f.Name], seenBit[f.Bit] = true, true
	}
	sve, ok := LookupCPUFeature("sve")
	if !ok || sve.Arch != "arm64" || sve.Macro() != "OAK_CPU_SVE" || sve.Mode != "sve" {
		t.Fatalf("sve: %+v %v", sve, ok)
	}
	if _, ok := LookupCPUFeature("neon"); ok {
		t.Fatal("neon is the AArch64 baseline, not a dispatch feature")
	}
}

func TestCPUFeatureLookupAllocatesNothing(t *testing.T) {
	allocs := testing.AllocsPerRun(1000, func() {
		if _, ok := LookupCPUFeature("rvv"); !ok {
			panic("missing rvv")
		}
	})
	if allocs != 0 {
		t.Fatalf("feature lookup allocated: %f", allocs)
	}
}
