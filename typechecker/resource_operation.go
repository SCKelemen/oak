package typechecker

import (
	"fmt"
	"sort"
)

// normalizeResourceOperation keeps the legacy consumption projection and the
// parameter contract in agreement. Matching legacy entries are accepted because
// SemIR projection supplies both representations; conflicting entries fail closed.
func normalizeResourceOperation(op ResourceOperation) (ResourceOperation, error) {
	modes := make(map[int]ResourceParameterMode)
	for _, parameter := range op.Parameters {
		if parameter.Index < 0 || parameter.Mode < ResourceParameterBorrowed || parameter.Mode > ResourceParameterConsumed {
			return ResourceOperation{}, fmt.Errorf("invalid resource parameter %d mode %d", parameter.Index, parameter.Mode)
		}
		if _, exists := modes[parameter.Index]; exists {
			return ResourceOperation{}, fmt.Errorf("duplicate resource parameter %d", parameter.Index)
		}
		modes[parameter.Index] = parameter.Mode
	}
	legacy := make(map[int]bool)
	for _, index := range op.Consumes {
		if index < 0 || legacy[index] {
			return ResourceOperation{}, fmt.Errorf("invalid or duplicate consumed argument %d", index)
		}
		legacy[index] = true
		if mode, exists := modes[index]; exists && mode != ResourceParameterConsumed {
			return ResourceOperation{}, fmt.Errorf("argument %d has conflicting resource modes", index)
		}
		modes[index] = ResourceParameterConsumed
	}
	indices := make([]int, 0, len(modes))
	for index := range modes {
		indices = append(indices, index)
	}
	sort.Ints(indices)
	out := ResourceOperation{ReturnsFresh: op.ReturnsFresh}
	for _, index := range indices {
		mode := modes[index]
		out.Parameters = append(out.Parameters, ResourceParameterDeclaration{Index: index, Mode: mode})
		if mode == ResourceParameterConsumed {
			out.Consumes = append(out.Consumes, index)
		}
	}
	return out, nil
}
