package semir

import "testing"

func TestArm64ControlTransferCatalogIsExact(t *testing.T) {
	members := Arm64ControlTransferMembers()
	if members != [1]string{"eret"} {
		t.Fatalf("unexpected control-transfer surface: %v", members)
	}
	spec, ok := LookupArm64ControlTransfer("eret")
	if !ok || spec.Instruction != "eret" {
		t.Fatalf("ERET semantic descriptor missing or wrong: %#v %v", spec, ok)
	}
	if _, ok := LookupArm64ControlTransfer("ret"); ok {
		t.Fatal("ordinary RET must not be part of the privileged control-transfer surface")
	}
}

func TestArm64ControlTransferLookupAllocatesNothing(t *testing.T) {
	allocs := testing.AllocsPerRun(1000, func() {
		if _, ok := LookupArm64ControlTransfer("eret"); !ok {
			panic("missing eret")
		}
	})
	if allocs != 0 {
		t.Fatalf("control-transfer lookup allocated: %f", allocs)
	}
}
