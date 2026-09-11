package typechecker

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

// ResourceModelFromSemIR derives the typechecker's executable resource model
// from checked semantic facts. Resource-bearing definitions are identified by
// their Authority.Resource axis; parameter authority modes and fresh-return
// semantics come from structured resource effects bound to resolved callables.
func ResourceModelFromSemIR(module semir.Module) (ResourceModel, error) {
	if err := module.Validate(); err != nil {
		return ResourceModel{}, fmt.Errorf("invalid semantic module: %w", err)
	}
	if err := module.ValidateResourceSemantics(); err != nil {
		return ResourceModel{}, err
	}

	model := NewResourceModel()
	protocolOf := make(map[string]string)
	for _, definition := range module.Definitions {
		switch definition.Authority.Resource {
		case semir.ResourceAuthorityUnspecified:
			continue
		case semir.ResourceAuthorityLive,
			semir.ResourceAuthorityConsumed,
			semir.ResourceAuthorityMaybeConsumed:
			model.MarkResourceType(definition.Name)
			protocolOf[definition.Name] = definition.Protocol
		default:
			return ResourceModel{}, fmt.Errorf(
				"definition %q has invalid resource authority %q",
				definition.Name,
				definition.Authority.Resource,
			)
		}
	}

	// Every state a callable's transitions enter, across protocols.
	targets := make(map[string]map[string]bool)
	for _, protocol := range module.Protocols {
		for _, transition := range protocol.Transitions {
			if transition.Callable == "" || transition.To == "" {
				continue
			}
			if targets[transition.Callable] == nil {
				targets[transition.Callable] = make(map[string]bool)
			}
			targets[transition.Callable][transition.To] = true
		}
		for typeName, protocolName := range protocolOf {
			if protocolName == protocol.Name && protocol.Initial != "" {
				model.MarkInitial(typeName, protocol.Initial)
			}
		}
	}
	sortedTargets := func(callable string) []string {
		out := make([]string, 0, len(targets[callable]))
		for state := range targets[callable] {
			out = append(out, state)
		}
		sort.Strings(out)
		return out
	}

	fullSemantics := make(map[string]semir.ResourceTransitionSemantics)
	for _, protocol := range module.Protocols {
		terminalStates := make(map[string]bool)
		for _, state := range protocol.TerminalStates() {
			terminalStates[state] = true
		}
		for _, transition := range protocol.Transitions {
			semantics, present, err := transition.ResourceSemantics()
			if err != nil {
				return ResourceModel{}, fmt.Errorf(
					"protocol %q transition %q: %w",
					protocol.Name,
					transition.Name,
					err,
				)
			}
			if !present {
				continue
			}

			callable := transition.Callable
			if existing, exists := fullSemantics[callable]; exists {
				if !sameResourceTransitionSemantics(existing, semantics) {
					return ResourceModel{}, fmt.Errorf(
						"resource callable %q has conflicting semantics across protocols",
						callable,
					)
				}
				continue
			}
			fullSemantics[callable] = semantics

			model.MarkOperation(callable, ResourceOperation{
				Parameters:       resourceParametersFromSemIR(semantics),
				Consumes:         append([]int(nil), semantics.Consumes...),
				ReturnsFresh:     semantics.ReturnsFresh,
				ReturnsAlias:     semantics.ReturnsAlias,
				AliasesArgument:  semantics.AliasesArgument,
				ReturnsBorrow:    semantics.ReturnsBorrow,
				BorrowsArguments: append([]int(nil), semantics.BorrowsArguments...),
				BorrowMutable:    semantics.BorrowMutable,
				Terminal:         terminalStates[transition.To],
				Targets:          sortedTargets(callable),
				Receiver:         receiverModeFromSemIR(semantics.Receiver),
			})
		}
	}

	// Terminal-state obligations: a protocol guaranteeing that a terminal
	// state is eventually reached obliges every resource type it governs to
	// reach one before its last name leaves scope; the closers are the
	// transitions into those states.
	for _, protocol := range module.Protocols {
		terminal := protocol.TerminalStates()
		if len(terminal) == 0 {
			continue
		}
		isTerminal := make(map[string]bool, len(terminal))
		for _, state := range terminal {
			isTerminal[state] = true
		}
		var closers []string
		for _, transition := range protocol.Transitions {
			if isTerminal[transition.To] && transition.Callable != "" {
				closers = append(closers, transition.Callable)
			}
		}
		sort.Strings(closers)
		types := make([]string, 0, len(protocolOf))
		for typeName, protocolName := range protocolOf {
			if protocolName == protocol.Name {
				types = append(types, typeName)
			}
		}
		sort.Strings(types)
		for _, typeName := range types {
			model.MarkObligation(typeName, ResourceObligation{Terminal: append([]string(nil), terminal...), Closers: closers})
		}
	}

	return model, nil
}

// receiverModeFromSemIR decodes the receiver effect name into a mode.
func receiverModeFromSemIR(name string) ResourceParameterMode {
	switch name {
	case semir.ResourceEffectBorrow:
		return ResourceParameterBorrowed
	case semir.ResourceEffectBorrowMut:
		return ResourceParameterBorrowedMut
	case semir.ResourceEffectConsume:
		return ResourceParameterConsumed
	}
	return ResourceParameterUnspecified
}

func resourceParametersFromSemIR(semantics semir.ResourceTransitionSemantics) []ResourceParameterDeclaration {
	parameters := make([]ResourceParameterDeclaration, 0,
		len(semantics.Borrowed)+len(semantics.BorrowedMut)+len(semantics.Consumes))
	for _, index := range semantics.Borrowed {
		parameters = append(parameters, ResourceParameterDeclaration{Index: index, Mode: ResourceParameterBorrowed})
	}
	for _, index := range semantics.BorrowedMut {
		parameters = append(parameters, ResourceParameterDeclaration{Index: index, Mode: ResourceParameterBorrowedMut})
	}
	for _, index := range semantics.Consumes {
		parameters = append(parameters, ResourceParameterDeclaration{Index: index, Mode: ResourceParameterConsumed})
	}
	for _, callable := range semantics.Callables {
		contract := &ResourceCallableContract{ReturnsFresh: callable.ReturnsFresh}
		for _, index := range callable.Borrowed {
			contract.Parameters = append(contract.Parameters, ResourceParameterDeclaration{Index: index, Mode: ResourceParameterBorrowed})
		}
		for _, index := range callable.BorrowedMut {
			contract.Parameters = append(contract.Parameters, ResourceParameterDeclaration{Index: index, Mode: ResourceParameterBorrowedMut})
		}
		for _, index := range callable.Consumes {
			contract.Parameters = append(contract.Parameters, ResourceParameterDeclaration{Index: index, Mode: ResourceParameterConsumed})
		}
		parameters = append(parameters, ResourceParameterDeclaration{Index: callable.Argument, Callable: normalizeCallableContract(contract)})
	}
	sort.Slice(parameters, func(i, j int) bool { return parameters[i].Index < parameters[j].Index })
	return parameters
}

// CheckProgramWithSemIR is the semantic-pipeline resource-checking entrypoint.
// Callers provide the already resolved SemIR module; no manual ResourceModel
// registration is required, and no source-level consume spelling is assumed.
func (tc *TypeChecker) CheckProgramWithSemIR(program *ast.Program, module semir.Module) error {
	model, err := ResourceModelFromSemIR(module)
	if err != nil {
		return err
	}
	tc.CheckProgramWithResources(program, model)
	return nil
}

func sameResourceOperation(left, right ResourceOperation) bool {
	if left.ReturnsFresh != right.ReturnsFresh ||
		len(left.Parameters) != len(right.Parameters) ||
		len(left.Consumes) != len(right.Consumes) {
		return false
	}
	for i := range left.Parameters {
		if left.Parameters[i] != right.Parameters[i] {
			return false
		}
	}
	for i := range left.Consumes {
		if left.Consumes[i] != right.Consumes[i] {
			return false
		}
	}
	return true
}

func sameResourceTransitionSemantics(left, right semir.ResourceTransitionSemantics) bool {
	if left.ReturnsFresh != right.ReturnsFresh || left.Receiver != right.Receiver ||
		left.ReturnsAlias != right.ReturnsAlias || (left.ReturnsAlias && left.AliasesArgument != right.AliasesArgument) ||
		left.ReturnsBorrow != right.ReturnsBorrow || (left.ReturnsBorrow && (!sameIndexSet(left.BorrowsArguments, right.BorrowsArguments) || left.BorrowMutable != right.BorrowMutable)) {
		return false
	}
	if len(left.Callables) != len(right.Callables) {
		return false
	}
	for i := range left.Callables {
		l, r := left.Callables[i], right.Callables[i]
		if l.Argument != r.Argument || l.ReturnsFresh != r.ReturnsFresh ||
			!sameIntSlice(l.Borrowed, r.Borrowed) || !sameIntSlice(l.BorrowedMut, r.BorrowedMut) || !sameIntSlice(l.Consumes, r.Consumes) {
			return false
		}
	}
	return sameIntSlice(left.Borrowed, right.Borrowed) &&
		sameIntSlice(left.BorrowedMut, right.BorrowedMut) &&
		sameIntSlice(left.Consumes, right.Consumes)
}

func sameIntSlice(left, right []int) bool {
	if len(left) != len(right) {
		return false
	}
	for i := range left {
		if left[i] != right[i] {
			return false
		}
	}
	return true
}
