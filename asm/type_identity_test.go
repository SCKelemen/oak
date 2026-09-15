package asm

import "testing"

func TestSameTypeStructuralIdentity(t *testing.T) {
	u32 := &oakType{kind: oakScalar, width: 32}
	u32Again := &oakType{kind: oakScalar, width: 32}
	f32 := &oakType{kind: oakScalar, width: 32, float: true}
	i32 := &oakType{kind: oakScalar, width: 32, signed: true}
	bytes4 := &oakType{kind: oakArray, length: 4, elem: &oakType{kind: oakScalar, width: 8}}
	bytes4Again := &oakType{kind: oakArray, length: 4, elem: &oakType{kind: oakScalar, width: 8}}
	bytes8 := &oakType{kind: oakArray, length: 8, elem: &oakType{kind: oakScalar, width: 8}}
	recordA := &oakType{kind: oakRecord, name: "A"}
	recordAAgain := &oakType{kind: oakRecord, name: "A"}
	recordB := &oakType{kind: oakRecord, name: "B"}

	for _, tc := range []struct {
		name string
		a, b *oakType
		want bool
	}{
		{"same pointer", u32, u32, true},
		{"equal scalars", u32, u32Again, true},
		{"integer and float", u32, f32, false},
		{"unsigned and signed", u32, i32, false},
		{"equal arrays", bytes4, bytes4Again, true},
		{"different array lengths", bytes4, bytes8, false},
		{"equal nominal records", recordA, recordAAgain, true},
		{"different nominal records", recordA, recordB, false},
		{"unnamed aggregates fail closed", &oakType{kind: oakRecord}, &oakType{kind: oakRecord}, false},
		{"nil and type", nil, u32, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if got := sameType(tc.a, tc.b); got != tc.want {
				t.Fatalf("sameType() = %v, want %v", got, tc.want)
			}
		})
	}
}
