package semir

import "fmt"

// RepresentationPolicyExplicitOffsets selects a representation whose concrete
// field offsets are part of the representation contract rather than derived
// from Oak's natural ordered layout algorithm.
const RepresentationPolicyExplicitOffsets RepresentationPolicy = "explicit-offsets"

// RepresentationBinding associates one named runtime representation with one
// semantic type definition. Multiple bindings may reference the same TypeName:
// semantic identity is authoritative and representation is a separately chosen
// realization of that meaning.
type RepresentationBinding struct {
	TypeName       string
	Name           string
	Representation Representation
}

// RepresentationRegistry is the representation axis for semantic definitions.
// It deliberately lives beside Module rather than inside Type: adding, removing,
// or selecting a runtime representation must not mutate semantic type identity.
type RepresentationRegistry struct {
	Bindings []RepresentationBinding
}

// Validate checks that every representation binding names an existing semantic
// definition, has a unique name within that semantic type, and is itself a valid
// representation for the already-validated definition.
func (registry RepresentationRegistry) Validate(module Module) error {
	if err := module.Validate(); err != nil {
		return fmt.Errorf("semantic module: %w", err)
	}

	definitions := make(map[string]Definition, len(module.Definitions))
	for _, definition := range module.Definitions {
		definitions[definition.Name] = definition
	}

	seen := make(map[string]struct{}, len(registry.Bindings))
	for _, binding := range registry.Bindings {
		if binding.TypeName == "" {
			return fmt.Errorf("representation binding has empty semantic type name")
		}
		if binding.Name == "" {
			return fmt.Errorf("representation binding for %q has empty name", binding.TypeName)
		}
		definition, ok := definitions[binding.TypeName]
		if !ok {
			return fmt.Errorf("representation %q references unknown semantic type %q", binding.Name, binding.TypeName)
		}
		key := binding.TypeName + "\x00" + binding.Name
		if _, exists := seen[key]; exists {
			return fmt.Errorf("duplicate representation %q for semantic type %q", binding.Name, binding.TypeName)
		}
		seen[key] = struct{}{}

		if binding.Representation.Kind == RepresentationUnspecified {
			return fmt.Errorf("representation %q for %q has unspecified kind", binding.Name, binding.TypeName)
		}

		// Reuse Definition.Validate so representation facts obey the same checked
		// invariants whether selected inline by `struct` or named in a registry.
		candidate := definition
		candidate.Representation = binding.Representation
		if err := candidate.Validate(); err != nil {
			return fmt.Errorf("representation %q for %q: %w", binding.Name, binding.TypeName, err)
		}

		if err := validateSemanticRecordCoverage(definition.Type, binding.Representation); err != nil {
			return fmt.Errorf("representation %q for %q: %w", binding.Name, binding.TypeName, err)
		}
	}
	return nil
}

// BindingsFor returns the named representation choices for one semantic type in
// declaration order. The returned slice is independent of registry storage.
func (registry RepresentationRegistry) BindingsFor(typeName string) []RepresentationBinding {
	bindings := make([]RepresentationBinding, 0)
	for _, binding := range registry.Bindings {
		if binding.TypeName == typeName {
			bindings = append(bindings, binding)
		}
	}
	return bindings
}

// Select returns a concrete view of a semantic definition using one named
// representation. The semantic Type is copied unchanged; only the orthogonal
// Representation axis is rebound.
func (registry RepresentationRegistry) Select(module Module, typeName, representationName string) (Definition, error) {
	if err := registry.Validate(module); err != nil {
		return Definition{}, err
	}

	var definition *Definition
	for i := range module.Definitions {
		if module.Definitions[i].Name == typeName {
			candidate := module.Definitions[i]
			definition = &candidate
			break
		}
	}
	if definition == nil {
		return Definition{}, fmt.Errorf("unknown semantic type %q", typeName)
	}

	for _, binding := range registry.Bindings {
		if binding.TypeName == typeName && binding.Name == representationName {
			selected := *definition
			selected.Representation = binding.Representation
			return selected, nil
		}
	}
	return Definition{}, fmt.Errorf("semantic type %q has no representation %q", typeName, representationName)
}

// validateSemanticRecordCoverage ensures that an ordinary resolved record
// representation still realizes every semantic field exactly once. More exotic
// encodings (SoA, compressed/wire transforms, etc.) will require their own
// explicit representation kind plus a proof that establishes the semantic map;
// they must not silently masquerade as an ordinary record layout.
func validateSemanticRecordCoverage(semantic Type, representation Representation) error {
	if semantic.Kind != TypeRecord || representation.Kind != RepresentationRecord || !representation.Resolved {
		return nil
	}

	required := make(map[string]struct{}, len(semantic.Fields))
	for _, field := range semantic.Fields {
		required[field.Name] = struct{}{}
	}

	seen := make(map[string]struct{}, len(representation.Fields))
	for _, field := range representation.Fields {
		if _, duplicate := seen[field.Name]; duplicate {
			return fmt.Errorf("resolved record representation has duplicate field %q", field.Name)
		}
		seen[field.Name] = struct{}{}
		if _, exists := required[field.Name]; !exists {
			return fmt.Errorf("resolved record representation contains non-semantic field %q", field.Name)
		}
	}
	for name := range required {
		if _, exists := seen[name]; !exists {
			return fmt.Errorf("resolved record representation omits semantic field %q", name)
		}
	}
	return nil
}
