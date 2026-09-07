package semir

import "testing"

func TestArm64EventControlCatalogIsExact(t *testing.T) {
	members := Arm64EventControlMembers()
	seen := map[string]bool{}
	for _, member := range members {
		if seen[member] {
			t.Fatalf("duplicate member %q", member)
		}
		seen[member] = true
		spec, ok := LookupArm64EventControl(member)
		if !ok {
			t.Fatalf("member %q is not resolvable", member)
		}
		if err := ValidateArm64EventControl(spec); err != nil {
			t.Fatalf("invalid %q: %v", member, err)
		}
		if spec.Effect().Namespace != "Machine" || spec.Effect().Name != "EventControl" {
			t.Fatalf("%q has wrong effect: %+v", member, spec.Effect())
		}
	}
}

func TestArm64EventControlLookupAllocatesNothing(t *testing.T) {
	if got := testing.AllocsPerRun(1000, func() {
		_, _ = LookupArm64EventControl("wfi")
	}); got != 0 {
		t.Fatalf("lookup allocated: %f", got)
	}
}
