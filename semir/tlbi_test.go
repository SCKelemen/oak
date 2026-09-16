package semir

import (
	"reflect"
	"testing"
)

func TestArm64TLBICatalogIsClosedAndExact(t *testing.T) {
	members := Arm64TLBIMembers()
	if members != [1]string{"tlbi_vmalls12e1is"} {
		t.Fatalf("TLBI members = %v", members)
	}
	spec, ok := LookupArm64TLBI(members[0])
	if !ok {
		t.Fatal("catalog member is not recognized")
	}
	if err := ValidateArm64TLBI(spec); err != nil {
		t.Fatal(err)
	}
	if spec.Instruction != "tlbi vmalls12e1is" {
		t.Fatalf("TLBI instruction = %q", spec.Instruction)
	}
	wantEffect := Effect{
		Namespace:  "Machine",
		Name:       "TranslationMaintenance",
		Parameters: []string{"tlbi", "vmalls12e1", "inner-shareable"},
	}
	if effect := spec.Effect(); !reflect.DeepEqual(effect, wantEffect) {
		t.Fatalf("TLBI effect = %#v, want %#v", effect, wantEffect)
	}
	for _, unknown := range []string{"tlbi", "tlbi_vmalls12e1", "vmalls12e1is"} {
		if _, ok := LookupArm64TLBI(unknown); ok {
			t.Fatalf("unknown TLBI member %q was accepted", unknown)
		}
	}
}

func TestArm64TLBIValidationRejectsDrift(t *testing.T) {
	valid, _ := LookupArm64TLBI("tlbi_vmalls12e1is")
	tests := []Arm64TLBISpec{
		{Operation: valid.Operation, Shareability: valid.Shareability, Instruction: valid.Instruction},
		{Member: valid.Member, Operation: "vmalls12e1is", Shareability: valid.Shareability, Instruction: valid.Instruction},
		{Member: valid.Member, Operation: valid.Operation, Shareability: "local", Instruction: valid.Instruction},
		{Member: valid.Member, Operation: valid.Operation, Shareability: valid.Shareability, Instruction: "tlbi vmalls12e1"},
	}
	for _, spec := range tests {
		if err := ValidateArm64TLBI(spec); err == nil {
			t.Fatalf("drifted TLBI spec accepted: %#v", spec)
		}
	}
}

func TestArm64TLBILookupAllocatesNothing(t *testing.T) {
	allocs := testing.AllocsPerRun(1000, func() {
		spec, ok := LookupArm64TLBI("tlbi_vmalls12e1is")
		if !ok || spec.Instruction != "tlbi vmalls12e1is" {
			panic("TLBI lookup failed")
		}
	})
	if allocs != 0 {
		t.Fatalf("TLBI lookup allocated %.2f objects per call; want zero", allocs)
	}
}
