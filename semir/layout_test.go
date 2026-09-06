package semir

import "testing"

func TestNaturalRecordLayoutPreservesOrderAndAlignment(t *testing.T) {
	got, err := NaturalRecordLayout([]RecordFieldRepresentation{
		{Name: "kind", Size: 1, Alignment: 1},
		{Name: "length", Size: 4, Alignment: 4},
		{Name: "flags", Size: 2, Alignment: 2},
	})
	if err != nil {
		t.Fatalf("NaturalRecordLayout failed: %v", err)
	}

	if got.Kind != RepresentationRecord {
		t.Fatalf("unexpected representation kind %q", got.Kind)
	}
	if got.Alignment != 4 || got.Size != 12 {
		t.Fatalf("unexpected record size/alignment: size=%d alignment=%d", got.Size, got.Alignment)
	}

	want := []FieldLayout{
		{Name: "kind", Offset: 0, Size: 1},
		{Name: "length", Offset: 4, Size: 4},
		{Name: "flags", Offset: 8, Size: 2},
	}
	if len(got.Fields) != len(want) {
		t.Fatalf("field count=%d, want %d", len(got.Fields), len(want))
	}
	for i := range want {
		if got.Fields[i] != want[i] {
			t.Fatalf("field %d=%#v, want %#v", i, got.Fields[i], want[i])
		}
	}
}

func TestNaturalRecordLayoutEmptyRecord(t *testing.T) {
	got, err := NaturalRecordLayout(nil)
	if err != nil {
		t.Fatalf("NaturalRecordLayout failed: %v", err)
	}
	if got.Size != 0 || got.Alignment != 1 || len(got.Fields) != 0 {
		t.Fatalf("unexpected empty layout: %#v", got)
	}
}

func TestNaturalRecordLayoutZeroSizedField(t *testing.T) {
	got, err := NaturalRecordLayout([]RecordFieldRepresentation{
		{Name: "tag", Size: 0, Alignment: 1},
		{Name: "value", Size: 4, Alignment: 4},
	})
	if err != nil {
		t.Fatalf("NaturalRecordLayout failed: %v", err)
	}
	if got.Fields[0].Offset != 0 || got.Fields[1].Offset != 0 {
		t.Fatalf("zero-sized field unexpectedly consumed storage: %#v", got.Fields)
	}
	if got.Size != 4 || got.Alignment != 4 {
		t.Fatalf("unexpected zero-sized-field layout: %#v", got)
	}
}

func TestNaturalRecordLayoutRejectsInvalidInput(t *testing.T) {
	tests := []struct {
		name   string
		fields []RecordFieldRepresentation
	}{
		{
			name: "empty name",
			fields: []RecordFieldRepresentation{
				{Name: "", Size: 1, Alignment: 1},
			},
		},
		{
			name: "duplicate name",
			fields: []RecordFieldRepresentation{
				{Name: "x", Size: 1, Alignment: 1},
				{Name: "x", Size: 1, Alignment: 1},
			},
		},
		{
			name: "zero alignment",
			fields: []RecordFieldRepresentation{
				{Name: "x", Size: 1, Alignment: 0},
			},
		},
		{
			name: "non power of two alignment",
			fields: []RecordFieldRepresentation{
				{Name: "x", Size: 1, Alignment: 3},
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if _, err := NaturalRecordLayout(tt.fields); err == nil {
				t.Fatal("expected layout error")
			}
		})
	}
}

func TestNaturalRecordLayoutRejectsOverflow(t *testing.T) {
	max := ^uint32(0)

	if _, err := NaturalRecordLayout([]RecordFieldRepresentation{
		{Name: "a", Size: max, Alignment: 1},
		{Name: "b", Size: 1, Alignment: 1},
	}); err == nil {
		t.Fatal("expected field-end overflow")
	}

	if _, err := NaturalRecordLayout([]RecordFieldRepresentation{
		{Name: "a", Size: max, Alignment: 2},
	}); err == nil {
		t.Fatal("expected final record-size overflow from alignment rounding")
	}
}

func TestNaturalRecordLayoutFieldsDoNotOverlap(t *testing.T) {
	got, err := NaturalRecordLayout([]RecordFieldRepresentation{
		{Name: "a", Size: 3, Alignment: 1},
		{Name: "b", Size: 8, Alignment: 8},
		{Name: "c", Size: 5, Alignment: 4},
	})
	if err != nil {
		t.Fatalf("NaturalRecordLayout failed: %v", err)
	}

	for i, field := range got.Fields {
		inputAlignment := []uint32{1, 8, 4}[i]
		if field.Offset%inputAlignment != 0 {
			t.Fatalf("field %q offset %d is not aligned to %d", field.Name, field.Offset, inputAlignment)
		}
		if i > 0 {
			previous := got.Fields[i-1]
			previousEnd := previous.Offset + previous.Size
			if field.Offset < previousEnd {
				t.Fatalf("fields overlap: previous=%#v current=%#v", previous, field)
			}
		}
	}
	if got.Size%got.Alignment != 0 {
		t.Fatalf("record size %d is not aligned to %d", got.Size, got.Alignment)
	}
}
