package semir

import "testing"

func TestArm64BarrierCatalogIsValidAndExact(t *testing.T) {
	members := Arm64BarrierMembers()
	seen := map[string]bool{}
	for _, member := range members {
		if seen[member] {
			t.Fatalf("duplicate barrier member %q", member)
		}
		seen[member] = true
		spec, ok := LookupArm64Barrier(member)
		if !ok {
			t.Fatalf("catalog member %q is not recognized", member)
		}
		if spec.Member != member {
			t.Fatalf("lookup changed member identity: got %q want %q", spec.Member, member)
		}
		if err := ValidateArm64Barrier(spec); err != nil {
			t.Fatalf("barrier %q invalid: %v", member, err)
		}
		effect := spec.Effect()
		if effect.Namespace != "Machine" || effect.Name != "Barrier" {
			t.Fatalf("barrier %q effect = %#v", member, effect)
		}
	}
}

func TestArm64BarrierInstructionsAreExplicit(t *testing.T) {
	want := map[string]string{
		"dmb_ishld": "dmb ishld",
		"dmb_ish":   "dmb ish",
		"dmb_sy":    "dmb sy",
		"dsb_ish":   "dsb ish",
		"dsb_sy":    "dsb sy",
		"isb":       "isb",
	}
	for member, instruction := range want {
		spec, ok := LookupArm64Barrier(member)
		if !ok || spec.Instruction() != instruction {
			t.Fatalf("%s instruction = %q, want %q", member, spec.Instruction(), instruction)
		}
	}
}

func TestArm64BarrierLookupAllocatesNothing(t *testing.T) {
	allocs := testing.AllocsPerRun(1000, func() {
		spec, ok := LookupArm64Barrier("dsb_sy")
		if !ok || spec.Operation != BarrierDSB || spec.Scope != BarrierScopeSY {
			panic("barrier lookup failed")
		}
	})
	if allocs != 0 {
		t.Fatalf("barrier lookup allocated %.2f objects per call; want zero", allocs)
	}
}
