package typechecker

import (
	"fmt"
	"sort"
	"strings"
)

// ResourceProtocolDeclaration is syntax-independent resource protocol input to
// semantic resolution. It is deliberately not an AST node: future source, ABI,
// or generated metadata can all project into this shape without making any one
// surface spelling authoritative.
type ResourceProtocolDeclaration struct {
	Name          string
	ResourceTypes []string
	States        []string
	Initial       string
	Transitions   []ResourceTransitionDeclaration
}

// ResourceTransitionDeclaration binds one protocol-local transition label to
// an explicit callable identity. Callable is never inferred from Name.
type ResourceTransitionDeclaration struct {
	Name             string
	Callable         string
	From             string
	To               string
	Consumes         []int
	ConsumesReceiver bool
	ReturnsFresh     bool
}

// ResolvedResourceProgram contains only resource facts that have been checked
// against Oak's semantic type environment.
type ResolvedResourceProgram struct {
	Types     []ResolvedResourceType
	Protocols []ResolvedResourceProtocol
}

type ResolvedResourceType struct {
	Name     string
	Protocol string
}

type ResolvedResourceProtocol struct {
	Name        string
	States      []string
	Initial     string
	Transitions []ResolvedResourceTransition
}

type ResolvedResourceTransition struct {
	Name             string
	Callable         string
	From             string
	To               string
	Consumes         []int
	ConsumesReceiver bool
	ReturnsFresh     bool
}

// ResolveResourceDeclarations resolves internal protocol facts against the
// already checked Oak environment. It never guesses resource authority from a
// function name or type-state-shaped signature.
func (tc *TypeChecker) ResolveResourceDeclarations(declarations []ResourceProtocolDeclaration) (ResolvedResourceProgram, error) {
	if tc == nil || tc.env == nil {
		return ResolvedResourceProgram{}, fmt.Errorf("resource resolution requires a checked type environment")
	}

	resolved := ResolvedResourceProgram{}
	protocolNames := make(map[string]bool, len(declarations))
	resourceProtocols := make(map[string]string)
	resourceTypes := make(map[string]bool)

	// Resolve resource-bearing nominal types first so transition validation may
	// refer across protocols without depending on declaration order.
	for _, declaration := range declarations {
		if declaration.Name == "" {
			return ResolvedResourceProgram{}, fmt.Errorf("resource protocol has empty name")
		}
		if protocolNames[declaration.Name] {
			return ResolvedResourceProgram{}, fmt.Errorf("duplicate resource protocol %q", declaration.Name)
		}
		protocolNames[declaration.Name] = true
		if len(declaration.ResourceTypes) == 0 {
			return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q has no resource types", declaration.Name)
		}

		localTypes := make(map[string]bool, len(declaration.ResourceTypes))
		for _, name := range declaration.ResourceTypes {
			if name == "" {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q has an empty resource type", declaration.Name)
			}
			if localTypes[name] {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q duplicates resource type %q", declaration.Name, name)
			}
			localTypes[name] = true

			typ, exists := tc.env.GetType(name)
			if !exists || typ == nil {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q references unknown type %q", declaration.Name, name)
			}
			if nominalTypeName(typ) != name {
				return ResolvedResourceProgram{}, fmt.Errorf("resource type %q must resolve to a concrete nominal Oak type, got %s", name, typ)
			}
			if previous, exists := resourceProtocols[name]; exists {
				return ResolvedResourceProgram{}, fmt.Errorf("resource type %q is bound to both protocols %q and %q", name, previous, declaration.Name)
			}
			resourceProtocols[name] = declaration.Name
			resourceTypes[name] = true
			resolved.Types = append(resolved.Types, ResolvedResourceType{Name: name, Protocol: declaration.Name})
		}
	}

	// A stable type order makes emitted semantic modules independent of map
	// iteration and of later resolver implementation details.
	sort.Slice(resolved.Types, func(i, j int) bool {
		if resolved.Types[i].Name != resolved.Types[j].Name {
			return resolved.Types[i].Name < resolved.Types[j].Name
		}
		return resolved.Types[i].Protocol < resolved.Types[j].Protocol
	})

	callableSemantics := make(map[string]ResourceOperation)
	for _, declaration := range declarations {
		stateNames := make(map[string]bool, len(declaration.States))
		states := make([]string, 0, len(declaration.States))
		for _, state := range declaration.States {
			if state == "" {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q has an empty state", declaration.Name)
			}
			if stateNames[state] {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q duplicates state %q", declaration.Name, state)
			}
			stateNames[state] = true
			states = append(states, state)
		}
		if len(states) == 0 {
			return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q has no states", declaration.Name)
		}
		if !stateNames[declaration.Initial] {
			return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q initial state %q does not exist", declaration.Name, declaration.Initial)
		}

		protocol := ResolvedResourceProtocol{
			Name:    declaration.Name,
			States:  states,
			Initial: declaration.Initial,
		}
		transitionNames := make(map[string]bool, len(declaration.Transitions))
		for _, transition := range declaration.Transitions {
			if transition.Name == "" {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q has a transition with empty name", declaration.Name)
			}
			if transitionNames[transition.Name] {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q duplicates transition %q", declaration.Name, transition.Name)
			}
			transitionNames[transition.Name] = true
			if transition.Callable == "" {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q transition %q has no resolved callable binding", declaration.Name, transition.Name)
			}
			if !stateNames[transition.From] {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q transition %q references unknown source state %q", declaration.Name, transition.Name, transition.From)
			}
			if !stateNames[transition.To] {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q transition %q references unknown target state %q", declaration.Name, transition.Name, transition.To)
			}

			callableType, exists := tc.env.GetType(transition.Callable)
			if !exists || callableType == nil {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q transition %q references unknown callable %q", declaration.Name, transition.Name, transition.Callable)
			}
			function, ok := callableType.(*FunctionType)
			if !ok {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q transition %q binds %q, which is not a function", declaration.Name, transition.Name, transition.Callable)
			}

			consumes := append([]int(nil), transition.Consumes...)
			sort.Ints(consumes)
			for i, index := range consumes {
				if index < 0 || index >= len(function.Parameters) {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q consumes argument %d outside its %d parameters", transition.Callable, index, len(function.Parameters))
				}
				if i > 0 && consumes[i-1] == index {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q consumes argument %d more than once", transition.Callable, index)
				}
				parameterName := nominalTypeName(function.Parameters[index])
				if !resourceTypes[parameterName] {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q argument %d has non-resource type %s", transition.Callable, index, function.Parameters[index])
				}
			}
			if transition.ConsumesReceiver {
				receiverName := resourceCallableReceiverName(tc.env, transition.Callable)
				if receiverName == "" {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q consumes its receiver but has no resolved nominal receiver identity", transition.Callable)
				}
				if !resourceTypes[receiverName] {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q consumes receiver of non-resource type %q", transition.Callable, receiverName)
				}
			}
			if transition.ReturnsFresh {
				returnName := nominalTypeName(function.ReturnType)
				if !resourceTypes[returnName] {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q marks a fresh return but returns non-resource type %s", transition.Callable, function.ReturnType)
				}
			}

			operation := ResourceOperation{
				Consumes:         consumes,
				ConsumesReceiver: transition.ConsumesReceiver,
				ReturnsFresh:     transition.ReturnsFresh,
			}
			if previous, exists := callableSemantics[transition.Callable]; exists && !sameResourceOperation(previous, operation) {
				return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q has conflicting semantics across protocols", transition.Callable)
			}
			callableSemantics[transition.Callable] = operation
			protocol.Transitions = append(protocol.Transitions, ResolvedResourceTransition{
				Name:             transition.Name,
				Callable:         transition.Callable,
				From:             transition.From,
				To:               transition.To,
				Consumes:         consumes,
				ConsumesReceiver: transition.ConsumesReceiver,
				ReturnsFresh:     transition.ReturnsFresh,
			})
		}
		resolved.Protocols = append(resolved.Protocols, protocol)
	}

	return resolved, nil
}

// resourceCallableReceiverName projects the nominal receiver component from
// the typechecker's canonical method identity Receiver::method. It validates
// the receiver against the semantic environment, so arbitrary text containing
// "::" cannot manufacture receiver authority.
func resourceCallableReceiverName(env *TypeEnvironment, callable string) string {
	if env == nil {
		return ""
	}
	separator := strings.LastIndex(callable, "::")
	if separator <= 0 || separator+2 >= len(callable) {
		return ""
	}
	receiver := callable[:separator]
	typ, exists := env.GetType(receiver)
	if !exists || typ == nil || nominalTypeName(typ) != receiver {
		return ""
	}
	return receiver
}

// nominalTypeName returns the authority-bearing nominal base. Structural
// records and interface contracts deliberately return empty: letting either opt
// into non-duplicable resource semantics would allow structural compatibility
// or dynamic abstraction to bypass the authority class model.
func nominalTypeName(typ Type) string {
	switch t := typ.(type) {
	case *RecordType:
		if !t.Struct {
			return ""
		}
		return t.Name
	case *ADTType:
		return t.Name
	case *GenericType:
		return t.Name
	case *NarrowedADTVariantType:
		return t.ADTName
	default:
		return ""
	}
}
