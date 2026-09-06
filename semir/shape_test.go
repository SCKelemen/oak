package semir

import "testing"

func recordType(fields ...Field) Type {
	return Type{Kind: TypeRecord, Fields: fields}
}

func TestRecordShapeSatisfactionAllowsExtraFieldsAndIgnoresOrder(t *testing.T) {
	shape := recordType(
		Field{Name: "x", Type: "f32"},
		Field{Name: "y", Type: "f32"},
	)
	candidate := recordType(
		Field{Name: "label", Type: "string"},
		Field{Name: "y", Type: "f32"},
		Field{Name: "x", Type: "f32"},
	)

	ok, err := SatisfiesRecordShape(candidate, shape)
	if err != nil {
		t.Fatalf("SatisfiesRecordShape failed: %v", err)
	}
	if !ok {
		t.Fatal("candidate with required fields plus extras should satisfy shape")
	}
}

func TestRecordShapeSatisfactionRejectsMissingOrWrongType(t *testing.T) {
	shape := recordType(
		Field{Name: "x", Type: "f32"},
		Field{Name: "y", Type: "f32"},
	)

	tests := []Type{
		recordType(Field{Name: "x", Type: "f32"}),
		recordType(Field{Name: "x", Type: "f32"}, Field{Name: "y", Type: "u32"}),
	}
	for _, candidate := range tests {
		ok, err := SatisfiesRecordShape(candidate, shape)
		if err != nil {
			t.Fatalf("SatisfiesRecordShape failed: %v", err)
		}
		if ok {
			t.Fatalf("candidate %#v unexpectedly satisfied shape %#v", candidate.Fields, shape.Fields)
		}
	}
}

func TestRecordShapeSatisfactionIgnoresRepresentation(t *testing.T) {
	shape := Definition{
		Name: "XY",
		Type: recordType(
			Field{Name: "x", Type: "f32"},
			Field{Name: "y", Type: "f32"},
		),
	}
	candidate := Definition{
		Name: "Point",
		Type: recordType(
			Field{Name: "x", Type: "f32"},
			Field{Name: "y", Type: "f32"},
			Field{Name: "z", Type: "f32"},
		),
		Representation: Representation{
			Kind:      RepresentationRecord,
			Policy:    RepresentationPolicyNaturalOrdered,
			Resolved:  true,
			Size:      12,
			Alignment: 4,
			Fields: []FieldLayout{
				{Name: "x", Offset: 0, Size: 4},
				{Name: "y", Offset: 4, Size: 4},
				{Name: "z", Offset: 8, Size: 4},
			},
		},
	}

	before, err := DefinitionSatisfiesRecordShape(candidate, shape)
	if err != nil {
		t.Fatalf("shape check failed: %v", err)
	}
	candidate.Representation = Representation{
		Kind:      RepresentationRecord,
		Policy:    RepresentationPolicyNaturalOrdered,
		Resolved:  false,
	}
	after, err := DefinitionSatisfiesRecordShape(candidate, shape)
	if err != nil {
		t.Fatalf("shape check after representation change failed: %v", err)
	}
	if !before || !after {
		t.Fatalf("representation changed semantic shape result: before=%v after=%v", before, after)
	}
}

func TestRecordShapeSatisfactionRejectsMalformedShapes(t *testing.T) {
	valid := recordType(Field{Name: "x", Type: "f32"})
	tests := []Type{
		{Kind: TypeScalar},
		recordType(Field{Name: "", Type: "f32"}),
		recordType(Field{Name: "x", Type: ""}),
		recordType(Field{Name: "x", Type: "f32"}, Field{Name: "x", Type: "f32"}),
	}
	for _, candidate := range tests {
		if _, err := SatisfiesRecordShape(candidate, valid); err == nil {
			t.Fatalf("expected malformed candidate error for %#v", candidate)
		}
	}

	if _, err := SatisfiesRecordShape(valid, recordType(
		Field{Name: "x", Type: "f32"},
		Field{Name: "x", Type: "f32"},
	)); err == nil {
		t.Fatal("expected duplicate required-field error")
	}
}
