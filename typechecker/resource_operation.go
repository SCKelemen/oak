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
	callables := make(map[int]*ResourceCallableContract)
	for _, parameter := range op.Parameters {
		if parameter.Callable != nil {
			if parameter.Index < 0 || parameter.Mode != ResourceParameterUnspecified {
				return ResourceOperation{}, fmt.Errorf("invalid callable contract on resource parameter %d", parameter.Index)
			}
			if _, exists := callables[parameter.Index]; exists {
				return ResourceOperation{}, fmt.Errorf("duplicate callable contract on parameter %d", parameter.Index)
			}
			callables[parameter.Index] = normalizeCallableContract(parameter.Callable)
			continue
		}
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
	if op.Receiver > ResourceParameterConsumed {
		return ResourceOperation{}, fmt.Errorf("invalid resource receiver mode %d", op.Receiver)
	}
	if op.ReturnsAlias && op.ReturnsFresh {
		return ResourceOperation{}, fmt.Errorf("a result cannot be both fresh and an alias of an argument")
	}
	if op.ReturnsAlias && op.AliasesArgument < 0 {
		return ResourceOperation{}, fmt.Errorf("invalid aliased argument %d", op.AliasesArgument)
	}
	if op.ReturnsBorrow && (op.ReturnsFresh || op.ReturnsAlias) {
		return ResourceOperation{}, fmt.Errorf("a borrowed result cannot also be fresh or an alias of an argument")
	}
	if op.ReturnsBorrow && op.BorrowsArgument < 0 {
		return ResourceOperation{}, fmt.Errorf("invalid borrowed argument %d", op.BorrowsArgument)
	}
	out := ResourceOperation{ReturnsFresh: op.ReturnsFresh, ReturnsAlias: op.ReturnsAlias, AliasesArgument: op.AliasesArgument, ReturnsBorrow: op.ReturnsBorrow, BorrowsArgument: op.BorrowsArgument, Receiver: op.Receiver}
	for _, index := range indices {
		if _, callable := callables[index]; callable {
			return ResourceOperation{}, fmt.Errorf("parameter %d has both a resource mode and a callable contract", index)
		}
		mode := modes[index]
		out.Parameters = append(out.Parameters, ResourceParameterDeclaration{Index: index, Mode: mode})
		if mode == ResourceParameterConsumed {
			out.Consumes = append(out.Consumes, index)
		}
	}
	callableIndices := make([]int, 0, len(callables))
	for index := range callables {
		callableIndices = append(callableIndices, index)
	}
	sort.Ints(callableIndices)
	for _, index := range callableIndices {
		out.Parameters = append(out.Parameters, ResourceParameterDeclaration{Index: index, Callable: callables[index]})
	}
	sort.Slice(out.Parameters, func(i, j int) bool { return out.Parameters[i].Index < out.Parameters[j].Index })
	return out, nil
}
