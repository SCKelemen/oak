package semir

import (
	"strings"
	"testing"
)

// Declared layout specs (docs/spec/40-records.md): packed places fields
// densely at prefix-sum offsets; align raises record alignment without
// moving any field; under-alignment and non-power-of-two alignments are
// rejected, never approximated.

func wireFields() []RecordFieldRepresentation {
	return []RecordFieldRepresentation{
		{Name: "magic", Size: 4, Alignment: 4},
		{Name: "kind", Size: 1, Alignment: 1},
		{Name: "length", Size: 2, Alignment: 2},
	}
}

func TestPackedLayoutIsDense(t *testing.T) {
	got, err := RecordLayoutWithSpec(wireFields(), RecordLayoutSpec{Packed: true})
	if err != nil {
		t.Fatal(err)
	}
	wantOffsets := []uint32{0, 4, 5}
	for i, field := range got.Fields {
		if field.Offset != wantOffsets[i] {
			t.Fatalf("field %s offset = %d, want %d", field.Name, field.Offset, wantOffsets[i])
		}
	}
	if got.Size != 7 || got.Alignment != 1 {
		t.Fatalf("size/align = %d/%d, want 7/1 (natural would be 8/4)", got.Size, got.Alignment)
	}
}

func TestPackedLayoutWithExplicitAlignment(t *testing.T) {
	got, err := RecordLayoutWithSpec(wireFields(), RecordLayoutSpec{Packed: true, Align: 4})
	if err != nil {
		t.Fatal(err)
	}
	if got.Size != 8 || got.Alignment != 4 {
		t.Fatalf("size/align = %d/%d, want 8/4 (dense 7 rounded to align 4)", got.Size, got.Alignment)
	}
	if got.Fields[2].Offset != 5 {
		t.Fatalf("packed offsets must not move under explicit alignment; length at %d, want 5", got.Fields[2].Offset)
	}
}

func TestRaisedAlignmentKeepsNaturalOffsets(t *testing.T) {
	natural, err := NaturalRecordLayout(wireFields())
	if err != nil {
		t.Fatal(err)
	}
	raised, err := RecordLayoutWithSpec(wireFields(), RecordLayoutSpec{Align: 64})
	if err != nil {
		t.Fatal(err)
	}
	for i := range natural.Fields {
		if raised.Fields[i].Offset != natural.Fields[i].Offset {
			t.Fatalf("raising alignment moved field %s: %d != %d",
				natural.Fields[i].Name, raised.Fields[i].Offset, natural.Fields[i].Offset)
		}
	}
	if raised.Size != 64 || raised.Alignment != 64 {
		t.Fatalf("size/align = %d/%d, want 64/64", raised.Size, raised.Alignment)
	}
}

func TestUnderAlignmentRejected(t *testing.T) {
	_, err := RecordLayoutWithSpec(wireFields(), RecordLayoutSpec{Align: 2})
	if err == nil || !strings.Contains(err.Error(), "below the natural alignment") {
		t.Fatalf("under-alignment must be rejected, got %v", err)
	}
}

func TestNonPowerOfTwoAlignmentRejected(t *testing.T) {
	_, err := RecordLayoutWithSpec(wireFields(), RecordLayoutSpec{Align: 3})
	if err == nil || !strings.Contains(err.Error(), "power of two") {
		t.Fatalf("non-power-of-two alignment must be rejected, got %v", err)
	}
}

func TestNaturalSpecMatchesNaturalLayout(t *testing.T) {
	viaSpec, err := RecordLayoutWithSpec(wireFields(), RecordLayoutSpec{})
	if err != nil {
		t.Fatal(err)
	}
	direct, err := NaturalRecordLayout(wireFields())
	if err != nil {
		t.Fatal(err)
	}
	if viaSpec.Size != direct.Size || viaSpec.Alignment != direct.Alignment {
		t.Fatalf("empty spec must be the natural layout: %d/%d vs %d/%d",
			viaSpec.Size, viaSpec.Alignment, direct.Size, direct.Alignment)
	}
}
