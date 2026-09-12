package semir

import "testing"

func TestArm64ControlTransferCatalogIsExact(t *testing.T) {
	members := Arm64ControlTransferMembers()
	if members != [2]string{"eret", "eret_x0"} {
		t.Fatalf("unexpected control-transfer surface: %v", members)
	}
	if spec, ok := LookupArm64ControlTransfer("eret_x0"); !ok || spec.Instruction != "eret" || spec.Arity() != 1 || spec.Carries[0] != "x0" {
		t.Fatalf("eret_x0 must be the same ERET carrying one value in x0: %#v %v", spec, ok)
	}
	if spec, _ := LookupArm64ControlTransfer("eret"); spec.Arity() != 0 {
		t.Fatalf("plain eret carries nothing: %#v", spec)
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
