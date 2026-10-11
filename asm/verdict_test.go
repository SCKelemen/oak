package asm

import (
	"reflect"
	"testing"
)

func TestComposeProvenPairRequiresBothProofs(t *testing.T) {
	kinds := []VerdictKind{VerdictTrusted, VerdictProven, VerdictWitnessed, VerdictMismatch}
	for _, firstKind := range kinds {
		for _, secondKind := range kinds {
			first := Verdict{Kind: firstKind, Message: "first", Callees: []string{"a"}, TransientResourceExhausted: firstKind == VerdictWitnessed}
			second := Verdict{Kind: secondKind, Message: "second", Callees: []string{"b"}, TransientResourceExhausted: secondKind == VerdictWitnessed}
			got := composeProvenPair(first, second, "joined")
			want := Verdict{Kind: VerdictProven, Message: "joined", Callees: []string{"a", "b"}}
			if firstKind != VerdictProven {
				want = first
			} else if secondKind != VerdictProven {
				want = second
			}
			if !reflect.DeepEqual(got, want) {
				t.Errorf("kinds %v/%v: got %#v, want %#v", firstKind, secondKind, got, want)
			}
		}
	}
}

func TestComposeProvenPairOwnsExactDependencies(t *testing.T) {
	first := Verdict{Kind: VerdictProven, Callees: []string{"shared", "first", "shared"}}
	second := Verdict{Kind: VerdictProven, Callees: []string{"second", "shared", "last"}}
	got := composeProvenPair(first, second, "both result chunks")
	want := []string{"shared", "first", "second", "last"}
	if !reflect.DeepEqual(got.Callees, want) {
		t.Fatalf("dependencies = %v, want %v", got.Callees, want)
	}
	first.Callees[0] = "mutated first"
	second.Callees[0] = "mutated second"
	if !reflect.DeepEqual(got.Callees, want) {
		t.Fatal("composed dependencies alias an input")
	}
	got.Callees[1] = "mutated result"
	if first.Callees[1] != "first" {
		t.Fatal("input dependencies alias the result")
	}
}

func TestVerdictWithCalleesPreservesRecordAndEmptyShape(t *testing.T) {
	original := Verdict{Kind: VerdictWitnessed, Message: "unchanged", TransientResourceExhausted: true, Callees: []string{"replaced"}}
	got := verdictWithCallees(original)
	if got.Kind != original.Kind || got.Message != original.Message || got.TransientResourceExhausted != original.TransientResourceExhausted {
		t.Fatalf("record changed: %#v", got)
	}
	if got.Callees == nil || len(got.Callees) != 0 {
		t.Fatalf("empty union shape changed: %#v", got.Callees)
	}
}

func BenchmarkComposeProvenPair(b *testing.B) {
	first := Verdict{Kind: VerdictProven, Callees: []string{"a", "shared"}}
	second := Verdict{Kind: VerdictProven, Callees: []string{"shared", "b"}}
	b.Run("previous-inline-union", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			benchmarkComposedVerdict = verdictWithCallees(Verdict{Kind: VerdictProven, Message: "joined"}, first.Callees, second.Callees)
		}
	})
	b.Run("composition-boundary", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			benchmarkComposedVerdict = composeProvenPair(first, second, "joined")
		}
	})
}

var benchmarkComposedVerdict Verdict
