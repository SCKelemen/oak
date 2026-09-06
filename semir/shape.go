package semir

import "fmt"

// SatisfiesRecordShape reports whether candidate provides every semantic field
// required by shape. It is intentionally representation-blind: offsets, size,
// alignment, packing, and representation policy do not participate.
//
// The initial relation requires exact semantic field type identity. Richer field
// compatibility (for example refinements or variance) can be layered on later
// through the type relation without changing shape membership itself.
func SatisfiesRecordShape(candidate, shape Type) (bool, error) {
	if candidate.Kind != TypeRecord {
		return false, fmt.Errorf("candidate type kind %q is not a record", candidate.Kind)
	}
	if shape.Kind != TypeRecord {
		return false, fmt.Errorf("shape type kind %q is not a record", shape.Kind)
	}
	if err := validateShapeFields("candidate", candidate.Fields); err != nil {
		return false, err
	}
	if err := validateShapeFields("shape", shape.Fields); err != nil {
		return false, err
	}

	available := make(map[string]string, len(candidate.Fields))
	for _, field := range candidate.Fields {
		available[field.Name] = field.Type
	}
	for _, required := range shape.Fields {
		actual, ok := available[required.Name]
		if !ok || actual != required.Type {
			return false, nil
		}
	}
	return true, nil
}

// DefinitionSatisfiesRecordShape is the definition-level relation used by
// semantic passes. Representation is deliberately ignored: rebinding a record
// to a different storage policy cannot change whether it satisfies a shape.
func DefinitionSatisfiesRecordShape(candidate, shape Definition) (bool, error) {
	return SatisfiesRecordShape(candidate.Type, shape.Type)
}

func validateShapeFields(kind string, fields []Field) error {
	seen := make(map[string]struct{}, len(fields))
	for _, field := range fields {
		if field.Name == "" {
			return fmt.Errorf("%s record shape has empty field name", kind)
		}
		if field.Type == "" {
			return fmt.Errorf("%s record shape field %q has empty type", kind, field.Name)
		}
		if _, exists := seen[field.Name]; exists {
			return fmt.Errorf("%s record shape has duplicate field %q", kind, field.Name)
		}
		seen[field.Name] = struct{}{}
	}
	return nil
}
