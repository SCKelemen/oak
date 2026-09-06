package semir

import (
	"reflect"
	"strings"
	"testing"
)

func representationTestModule() Module {
	return Module{Definitions: []Definition{{
		Name: "Position",
		Type: Type{
			Kind: TypeRecord,
			Fields: []Field{
				{Name: "x", Type: "i32"},
				{Name: "y", Type: "i32"},
			},
		},
	}}}
}

func representationTestRegistry() RepresentationRegistry {
	return RepresentationRegistry{Bindings: []RepresentationBinding{
		{
			TypeName: "Position",
			Name:     "natural",
			Representation: Representation{
				Kind:      RepresentationRecord,
				Policy:    RepresentationPolicyNaturalOrdered,
				Resolved:  true,
				Size:      8,
				Alignment: 4,
				Fields: []FieldLayout{
					{Name: "x", Offset: 0, Size: 4},
					{Name: "y", Offset: 4, Size: 4},
				},
			},
		},
		{
			TypeName: "Position",
			Name:     "reversed",
			Representation: Representation{
				Kind:      RepresentationRecord,
				Policy:    RepresentationPolicyExplicitOffsets,
				Resolved:  true,
				Size:      8,
				Alignment: 4,
				Fields: []FieldLayout{
					{Name: "y", Offset: 0, Size: 4},
					{Name: "x", Offset: 4, Size: 4},
				},
			},
		},
	}}
}

func TestRepresentationRegistryAllowsManyLayoutsForOneSemanticRecord(t *testing.T) {
	module := representationTestModule()
	registry := representationTestRegistry()

	if err := registry.Validate(module); err != nil {
		t.Fatalf("valid representation registry rejected: %v", err)
	}

	choices := registry.BindingsFor("Position")
	if len(choices) != 2 {
		t.Fatalf("expected two representation choices, got %d", len(choices))
	}
	if reflect.DeepEqual(choices[0].Representation.Fields, choices[1].Representation.Fields) {
		t.Fatal("test requires physically distinct layouts")
	}
}

func TestSelectingRepresentationDoesNotChangeSemanticType(t *testing.T) {
	module := representationTestModule()
	registry := representationTestRegistry()

	natural, err := registry.Select(module, "Position", "natural")
	if err != nil {
		t.Fatal(err)
	}
	reversed, err := registry.Select(module, "Position", "reversed")
	if err != nil {
		t.Fatal(err)
	}

	if !reflect.DeepEqual(natural.Type, reversed.Type) {
		t.Fatalf("representation selection changed semantic type:\n%#v\n%#v", natural.Type, reversed.Type)
	}
	if reflect.DeepEqual(natural.Representation.Fields, reversed.Representation.Fields) {
		t.Fatal("expected selected representations to remain physically distinct")
	}
}

func TestRecordShapeSatisfactionIgnoresSelectedRepresentation(t *testing.T) {
	module := representationTestModule()
	registry := representationTestRegistry()
	shape := Definition{
		Name: "HasX",
		Type: Type{Kind: TypeRecord, Fields: []Field{{Name: "x", Type: "i32"}}},
	}

	for _, name := range []string{"natural", "reversed"} {
		selected, err := registry.Select(module, "Position", name)
		if err != nil {
			t.Fatal(err)
		}
		ok, err := DefinitionSatisfiesRecordShape(selected, shape)
		if err != nil {
			t.Fatal(err)
		}
		if !ok {
			t.Fatalf("representation %q changed record-shape satisfaction", name)
		}
	}
}

func TestRepresentationRegistryRejectsUnknownTypeAndDuplicateName(t *testing.T) {
	module := representationTestModule()

	unknown := RepresentationRegistry{Bindings: []RepresentationBinding{{
		TypeName: "Missing",
		Name:     "natural",
		Representation: Representation{
			Kind: RepresentationRecord,
		},
	}}}
	if err := unknown.Validate(module); err == nil || !strings.Contains(err.Error(), "unknown semantic type") {
		t.Fatalf("expected unknown-type error, got %v", err)
	}

	duplicate := representationTestRegistry()
	duplicate.Bindings = append(duplicate.Bindings, duplicate.Bindings[0])
	if err := duplicate.Validate(module); err == nil || !strings.Contains(err.Error(), "duplicate representation") {
		t.Fatalf("expected duplicate-representation error, got %v", err)
	}
}

func TestResolvedRecordRepresentationMustCoverSemanticFieldsExactlyOnce(t *testing.T) {
	module := representationTestModule()
	registry := RepresentationRegistry{Bindings: []RepresentationBinding{{
		TypeName: "Position",
		Name:     "broken",
		Representation: Representation{
			Kind:      RepresentationRecord,
			Policy:    RepresentationPolicyExplicitOffsets,
			Resolved:  true,
			Size:      4,
			Alignment: 4,
			Fields: []FieldLayout{
				{Name: "x", Offset: 0, Size: 4},
			},
		},
	}}}

	if err := registry.Validate(module); err == nil || !strings.Contains(err.Error(), "omits semantic field") {
		t.Fatalf("expected missing-semantic-field error, got %v", err)
	}
}
