package typechecker

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
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

// ResourceParameterMode describes how one callable parameter participates in
// resource authority. These are semantic/ABI facts, not source-level syntax.
type ResourceParameterMode uint8

const (
	ResourceParameterUnspecified ResourceParameterMode = iota
	ResourceParameterBorrowed
	ResourceParameterBorrowedMut
	ResourceParameterConsumed
)

func (mode ResourceParameterMode) String() string {
	switch mode {
	case ResourceParameterBorrowed:
		return "borrowed"
	case ResourceParameterBorrowedMut:
		return "borrowed-mut"
	case ResourceParameterConsumed:
		return "consumed"
	default:
		return "unspecified"
	}
}

// ResourceParameterDeclaration assigns one resource-authority mode to a
// zero-based callable parameter.
type ResourceParameterDeclaration struct {
	Index int
	Mode  ResourceParameterMode
}

// ResourceTransitionDeclaration binds one protocol-local transition label to
// an explicit callable identity. Callable is never inferred from Name.
type ResourceTransitionDeclaration struct {
	Name       string
	Callable   string
	From       string
	To         string
	Parameters []ResourceParameterDeclaration
	// Consumes is the compatibility input for callers that predate explicit
	// parameter modes. Resolution normalizes it to ResourceParameterConsumed.
	Consumes     []int
	ReturnsFresh bool
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

type ResolvedResourceParameter struct {
	Index int
	Mode  ResourceParameterMode
}

type ResolvedResourceTransition struct {
	Name       string
	Callable   string
	From       string
	To         string
	Parameters []ResolvedResourceParameter
	// Consumes is retained as the executable permanent-authority projection.
	Consumes     []int
	ReturnsFresh bool
}

type resolvedCallableResourceSemantics struct {
	Parameters   []ResolvedResourceParameter
	ReturnsFresh bool
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

	sort.Slice(resolved.Types, func(i, j int) bool {
		if resolved.Types[i].Name != resolved.Types[j].Name {
			return resolved.Types[i].Name < resolved.Types[j].Name
		}
		return resolved.Types[i].Protocol < resolved.Types[j].Protocol
	})

	callableSemantics := make(map[string]resolvedCallableResourceSemantics)
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

		protocol := ResolvedResourceProtocol{Name: declaration.Name, States: states, Initial: declaration.Initial}
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
				// A generic template has no environment type; its signature
				// is read from the declaration, with type parameters as
				// variables. The contract then holds for every specialization
				// (docs/spec/50-borrowing.md section 9).
				if templateType, isTemplate := tc.templateSignature(transition.Callable); isTemplate {
					callableType, exists = templateType, true
				}
			}
			if !exists || callableType == nil {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q transition %q references unknown callable %q", declaration.Name, transition.Name, transition.Callable)
			}
			function, ok := callableType.(*FunctionType)
			if !ok {
				return ResolvedResourceProgram{}, fmt.Errorf("resource protocol %q transition %q binds %q, which is not a function", declaration.Name, transition.Name, transition.Callable)
			}

			parameters, consumes, err := resolveResourceParameters(transition, function, resourceTypes)
			if err != nil {
				return ResolvedResourceProgram{}, err
			}
			if transition.ReturnsFresh {
				returnName := nominalTypeName(function.ReturnType)
				if !resourceTypes[returnName] {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q marks a fresh return but returns non-resource type %s", transition.Callable, function.ReturnType)
				}
			}

			semantics := resolvedCallableResourceSemantics{Parameters: parameters, ReturnsFresh: transition.ReturnsFresh}
			if previous, exists := callableSemantics[transition.Callable]; exists && !sameResolvedCallableResourceSemantics(previous, semantics) {
				return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q has conflicting semantics across protocols", transition.Callable)
			}
			callableSemantics[transition.Callable] = semantics
			protocol.Transitions = append(protocol.Transitions, ResolvedResourceTransition{
				Name:         transition.Name,
				Callable:     transition.Callable,
				From:         transition.From,
				To:           transition.To,
				Parameters:   parameters,
				Consumes:     consumes,
				ReturnsFresh: transition.ReturnsFresh,
			})
		}
		resolved.Protocols = append(resolved.Protocols, protocol)
	}

	return resolved, nil
}

// templateSignature builds the signature of a generic function template
// for contract resolution: concrete parameter and return types are parsed,
// type parameters become variables (never resource types, so a contract
// cannot mark a parameter whose type is the template's own parameter).
func (tc *TypeChecker) templateSignature(name string) (*FunctionType, bool) {
	template, isTemplate := tc.functionTemplates[name]
	if !isTemplate || template == nil {
		return nil, false
	}
	typeParams := make(map[string]bool, len(template.TypeParams))
	for _, tp := range template.TypeParams {
		if tp != nil && tp.Name != nil {
			typeParams[tp.Name.Value] = true
		}
	}
	resolve := func(expr ast.Expression) Type {
		if ident, isIdent := expr.(*ast.Identifier); isIdent && typeParams[ident.Value] {
			return &TypeVar{Name: ident.Value}
		}
		if expr == nil {
			return &UnitType{}
		}
		if typ := tc.parseTypeExpression(expr); typ != nil {
			return typ
		}
		return &TypeVar{Name: expr.String()}
	}
	function := &FunctionType{}
	for _, parameter := range template.Parameters {
		if parameter == nil {
			continue
		}
		function.Parameters = append(function.Parameters, resolve(parameter.Type))
	}
	function.ReturnType = resolve(template.ReturnType)
	return function, true
}

func resolveResourceParameters(
	transition ResourceTransitionDeclaration,
	function *FunctionType,
	resourceTypes map[string]bool,
) ([]ResolvedResourceParameter, []int, error) {
	seen := make(map[int]ResourceParameterMode)
	parameters := make([]ResolvedResourceParameter, 0, len(transition.Parameters)+len(transition.Consumes))

	validate := func(index int, mode ResourceParameterMode) error {
		if mode == ResourceParameterUnspecified || mode > ResourceParameterConsumed {
			return fmt.Errorf("resource callable %q argument %d has invalid parameter mode %d", transition.Callable, index, mode)
		}
		if index < 0 || index >= len(function.Parameters) {
			return fmt.Errorf("resource callable %q marks argument %d outside its %d parameters", transition.Callable, index, len(function.Parameters))
		}
		if previous, exists := seen[index]; exists {
			return fmt.Errorf("resource callable %q argument %d has both %s and %s modes", transition.Callable, index, previous, mode)
		}
		parameterName := nominalTypeName(function.Parameters[index])
		if !resourceTypes[parameterName] {
			return fmt.Errorf("resource callable %q argument %d has non-resource type %s", transition.Callable, index, function.Parameters[index])
		}
		seen[index] = mode
		parameters = append(parameters, ResolvedResourceParameter{Index: index, Mode: mode})
		return nil
	}

	for _, parameter := range transition.Parameters {
		if err := validate(parameter.Index, parameter.Mode); err != nil {
			return nil, nil, err
		}
	}

	legacyConsumes := append([]int(nil), transition.Consumes...)
	sort.Ints(legacyConsumes)
	for i, index := range legacyConsumes {
		if i > 0 && legacyConsumes[i-1] == index {
			return nil, nil, fmt.Errorf("resource callable %q consumes argument %d more than once", transition.Callable, index)
		}
		if _, exists := seen[index]; exists {
			return nil, nil, fmt.Errorf("resource callable %q argument %d is specified by both parameter modes and legacy consumes", transition.Callable, index)
		}
		if err := validate(index, ResourceParameterConsumed); err != nil {
			return nil, nil, err
		}
	}

	sort.Slice(parameters, func(i, j int) bool { return parameters[i].Index < parameters[j].Index })
	consumes := make([]int, 0, len(parameters))
	for _, parameter := range parameters {
		if parameter.Mode == ResourceParameterConsumed {
			consumes = append(consumes, parameter.Index)
		}
	}
	return parameters, consumes, nil
}

func sameResolvedCallableResourceSemantics(left, right resolvedCallableResourceSemantics) bool {
	if left.ReturnsFresh != right.ReturnsFresh || len(left.Parameters) != len(right.Parameters) {
		return false
	}
	for i := range left.Parameters {
		if left.Parameters[i] != right.Parameters[i] {
			return false
		}
	}
	return true
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
