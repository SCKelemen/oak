package typechecker

import (
	"fmt"
	"sort"
	"strings"

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
// zero-based callable parameter, or — for a function-typed parameter — the
// callable contract any function value passed for it must carry
// (docs/spec/50-borrowing.md section 9, contracts on function types).
// Exactly one of Mode and Callable is set.
type ResourceParameterDeclaration struct {
	Index    int
	Mode     ResourceParameterMode
	Callable *ResourceCallableContract
}

// ResourceCallableContract is the contract a function-typed parameter
// requires of the function values passed for it: the modes of the
// callable's own resource parameters and whether it returns fresh
// authority. Agreement is exact after normalization; an uncontracted or
// unknown function value does not satisfy a contract with any mode.
type ResourceCallableContract struct {
	Parameters   []ResourceParameterDeclaration
	ReturnsFresh bool
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
	// ReturnsAlias marks a result that is an alias of the argument at
	// AliasesArgument: the same authority class, no wider permission
	// (docs/spec/50-borrowing.md section 9, result identity). Exclusive
	// with ReturnsFresh.
	ReturnsAlias    bool
	AliasesArgument int
	// ReturnsBorrow marks a result that is a shared borrow dependent on
	// the arguments at BorrowsArguments: its own authority, read permission
	// only, alive no longer than its scope, and while it lives none of those
	// arguments may be mutated, consumed, or rebound
	// (docs/spec/50-borrowing.md section 9, borrowed results). Exclusive
	// with ReturnsFresh and ReturnsAlias; every listed argument must be
	// borrowed or borrowed-mut, and the list is non-empty without duplicates.
	ReturnsBorrow    bool
	BorrowsArguments []int
	// BorrowMutable makes the borrowed result a mutable reborrow: it may be
	// passed to borrowed-mut positions, and while it lives its owners are
	// suspended entirely (docs/spec/50-borrowing.md section 9, borrowed
	// results). Requires ReturnsBorrow; every origin must be borrowed-mut.
	BorrowMutable bool
	// Receiver is the authority mode of a method's receiver
	// (docs/spec/50-borrowing.md section 9): its own slot, so the explicit
	// parameter indices above never shift. Unspecified for plain functions
	// and for methods whose receiver carries no contract.
	Receiver ResourceParameterMode
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
	Index    int
	Mode     ResourceParameterMode
	Callable *ResourceCallableContract
}

type ResolvedResourceTransition struct {
	Name       string
	Callable   string
	From       string
	To         string
	Parameters []ResolvedResourceParameter
	// Consumes is retained as the executable permanent-authority projection.
	Consumes         []int
	ReturnsFresh     bool
	ReturnsAlias     bool
	AliasesArgument  int
	ReturnsBorrow    bool
	BorrowsArguments []int
	BorrowMutable    bool
	Receiver         ResourceParameterMode
}

type resolvedCallableResourceSemantics struct {
	Parameters       []ResolvedResourceParameter
	ReturnsFresh     bool
	ReturnsAlias     bool
	AliasesArgument  int
	ReturnsBorrow    bool
	BorrowsArguments []int
	BorrowMutable    bool
	Receiver         ResourceParameterMode
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
			if (!exists || typ == nil) && tc.adtTypes != nil {
				// Tagged unions are registered in the checker's ADT table
				// rather than the value environment; they are nominal
				// resource types like structs (methods require them today).
				if _, isADT := tc.adtTypes[name]; isADT {
					typ, exists = &ADTType{Name: name}, true
				}
			}
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

			if transition.Receiver != ResourceParameterUnspecified {
				if transition.Receiver > ResourceParameterConsumed {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q has invalid receiver mode %d", transition.Callable, transition.Receiver)
				}
				receiverType, _, isMethod := strings.Cut(transition.Callable, "::")
				if !isMethod {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q marks a receiver mode but is not a method (Type::name)", transition.Callable)
				}
				if !resourceTypes[receiverType] {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q marks a receiver mode but its receiver type %s is not a resource type", transition.Callable, receiverType)
				}
			}
			if transition.ReturnsAlias {
				if transition.ReturnsFresh {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q cannot both return fresh authority and alias an argument", transition.Callable)
				}
				if transition.AliasesArgument < 0 || transition.AliasesArgument >= len(function.Parameters) {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q aliases argument %d outside its %d parameters", transition.Callable, transition.AliasesArgument, len(function.Parameters))
				}
				if !resourceTypes[nominalTypeName(function.Parameters[transition.AliasesArgument])] {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q aliases argument %d, which has non-resource type %s", transition.Callable, transition.AliasesArgument, function.Parameters[transition.AliasesArgument])
				}
				if !resourceTypes[nominalTypeName(function.ReturnType)] {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q marks an alias return but returns non-resource type %s", transition.Callable, function.ReturnType)
				}
			}
			borrows := normalizeIndexSet(transition.BorrowsArguments)
			if transition.ReturnsBorrow {
				if transition.ReturnsFresh || transition.ReturnsAlias {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q cannot return a borrowed result and also fresh or aliased authority", transition.Callable)
				}
				if len(borrows) == 0 {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q marks a borrowed result but names no borrowed argument", transition.Callable)
				}
				if len(borrows) != len(transition.BorrowsArguments) {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q lists a borrowed argument twice", transition.Callable)
				}
				if !resourceTypes[nominalTypeName(function.ReturnType)] {
					return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q marks a borrowed result but returns non-resource type %s", transition.Callable, function.ReturnType)
				}
				for _, index := range borrows {
					if index < 0 || index >= len(function.Parameters) {
						return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q borrows argument %d outside its %d parameters", transition.Callable, index, len(function.Parameters))
					}
					if !resourceTypes[nominalTypeName(function.Parameters[index])] {
						return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q borrows argument %d, which has non-resource type %s", transition.Callable, index, function.Parameters[index])
					}
					sourceMode := ResourceParameterUnspecified
					for _, parameter := range parameters {
						if parameter.Index == index {
							sourceMode = parameter.Mode
						}
					}
					if sourceMode != ResourceParameterBorrowed && sourceMode != ResourceParameterBorrowedMut {
						return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q borrows argument %d, which must be declared borrowed or borrowed-mut (a borrow of consumed or unmarked input is not admitted)", transition.Callable, index)
					}
					if transition.BorrowMutable && sourceMode != ResourceParameterBorrowedMut {
						return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q returns a mutable reborrow of argument %d, which must be declared borrowed-mut (mutable authority cannot be minted from a shared borrow)", transition.Callable, index)
					}
				}
			} else if transition.BorrowMutable {
				return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q marks a mutable reborrow without a borrowed result", transition.Callable)
			} else if len(borrows) != 0 {
				return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q names borrowed arguments without marking a borrowed result", transition.Callable)
			}
			semantics := resolvedCallableResourceSemantics{Parameters: parameters, ReturnsFresh: transition.ReturnsFresh, ReturnsAlias: transition.ReturnsAlias, AliasesArgument: transition.AliasesArgument, ReturnsBorrow: transition.ReturnsBorrow, BorrowsArguments: borrows, BorrowMutable: transition.BorrowMutable, Receiver: transition.Receiver}
			if previous, exists := callableSemantics[transition.Callable]; exists && !sameResolvedCallableResourceSemantics(previous, semantics) {
				return ResolvedResourceProgram{}, fmt.Errorf("resource callable %q has conflicting semantics across protocols", transition.Callable)
			}
			callableSemantics[transition.Callable] = semantics
			protocol.Transitions = append(protocol.Transitions, ResolvedResourceTransition{
				Name:             transition.Name,
				Callable:         transition.Callable,
				From:             transition.From,
				To:               transition.To,
				Parameters:       parameters,
				Consumes:         consumes,
				ReturnsFresh:     transition.ReturnsFresh,
				ReturnsAlias:     transition.ReturnsAlias,
				AliasesArgument:  transition.AliasesArgument,
				ReturnsBorrow:    transition.ReturnsBorrow,
				BorrowsArguments: borrows,
				BorrowMutable:    transition.BorrowMutable,
				Receiver:         transition.Receiver,
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

// validateCallableContract checks a function-typed parameter's required
// contract against that function type: every marked index is a parameter
// of resource type, and a fresh return names a resource result.
func validateCallableContract(callable string, index int, contract *ResourceCallableContract, function *FunctionType, resourceTypes map[string]bool) error {
	seen := make(map[int]bool)
	for _, inner := range contract.Parameters {
		if inner.Callable != nil {
			return fmt.Errorf("resource callable %q argument %d: nested callable contracts are not supported", callable, index)
		}
		if inner.Mode == ResourceParameterUnspecified || inner.Mode > ResourceParameterConsumed {
			return fmt.Errorf("resource callable %q argument %d: callable contract parameter %d has invalid mode %d", callable, index, inner.Index, inner.Mode)
		}
		if inner.Index < 0 || inner.Index >= len(function.Parameters) {
			return fmt.Errorf("resource callable %q argument %d: callable contract marks parameter %d outside the function type's %d parameters", callable, index, inner.Index, len(function.Parameters))
		}
		if seen[inner.Index] {
			return fmt.Errorf("resource callable %q argument %d: callable contract marks parameter %d twice", callable, index, inner.Index)
		}
		seen[inner.Index] = true
		if !resourceTypes[nominalTypeName(function.Parameters[inner.Index])] {
			return fmt.Errorf("resource callable %q argument %d: callable contract parameter %d has non-resource type %s", callable, index, inner.Index, function.Parameters[inner.Index])
		}
	}
	if contract.ReturnsFresh && !resourceTypes[nominalTypeName(function.ReturnType)] {
		return fmt.Errorf("resource callable %q argument %d: callable contract marks a fresh return but the function type returns %s", callable, index, function.ReturnType)
	}
	return nil
}

// normalizeCallableContract sorts a callable contract's parameters by index.
func normalizeCallableContract(contract *ResourceCallableContract) *ResourceCallableContract {
	out := &ResourceCallableContract{ReturnsFresh: contract.ReturnsFresh}
	out.Parameters = append(out.Parameters, contract.Parameters...)
	sort.Slice(out.Parameters, func(i, j int) bool { return out.Parameters[i].Index < out.Parameters[j].Index })
	return out
}

// sameCallableContract is exact normalized agreement of two callable
// contracts; nil equals nil only.
func sameCallableContract(left, right *ResourceCallableContract) bool {
	if left == nil || right == nil {
		return left == right
	}
	if left.ReturnsFresh != right.ReturnsFresh || len(left.Parameters) != len(right.Parameters) {
		return false
	}
	for i := range left.Parameters {
		if left.Parameters[i].Index != right.Parameters[i].Index || left.Parameters[i].Mode != right.Parameters[i].Mode {
			return false
		}
	}
	return true
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
		if parameter.Callable != nil {
			if parameter.Mode != ResourceParameterUnspecified {
				return nil, nil, fmt.Errorf("resource callable %q argument %d has both a resource mode and a callable contract", transition.Callable, parameter.Index)
			}
			if parameter.Index < 0 || parameter.Index >= len(function.Parameters) {
				return nil, nil, fmt.Errorf("resource callable %q marks argument %d outside its %d parameters", transition.Callable, parameter.Index, len(function.Parameters))
			}
			callableType, isFunction := function.Parameters[parameter.Index].(*FunctionType)
			if !isFunction {
				return nil, nil, fmt.Errorf("resource callable %q argument %d carries a callable contract but has non-function type %s", transition.Callable, parameter.Index, function.Parameters[parameter.Index])
			}
			if err := validateCallableContract(transition.Callable, parameter.Index, parameter.Callable, callableType, resourceTypes); err != nil {
				return nil, nil, err
			}
			if _, exists := seen[parameter.Index]; exists {
				return nil, nil, fmt.Errorf("resource callable %q argument %d is declared twice", transition.Callable, parameter.Index)
			}
			seen[parameter.Index] = ResourceParameterUnspecified
			parameters = append(parameters, ResolvedResourceParameter{Index: parameter.Index, Callable: normalizeCallableContract(parameter.Callable)})
			continue
		}
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
	if left.ReturnsFresh != right.ReturnsFresh || left.Receiver != right.Receiver || len(left.Parameters) != len(right.Parameters) ||
		left.ReturnsAlias != right.ReturnsAlias || (left.ReturnsAlias && left.AliasesArgument != right.AliasesArgument) ||
		left.ReturnsBorrow != right.ReturnsBorrow || (left.ReturnsBorrow && (!sameIndexSet(left.BorrowsArguments, right.BorrowsArguments) || left.BorrowMutable != right.BorrowMutable)) {
		return false
	}
	for i := range left.Parameters {
		if left.Parameters[i].Index != right.Parameters[i].Index || left.Parameters[i].Mode != right.Parameters[i].Mode ||
			!sameCallableContract(left.Parameters[i].Callable, right.Parameters[i].Callable) {
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

// normalizeIndexSet sorts indices and drops duplicates; the caller compares
// lengths to detect a repeated index.
func normalizeIndexSet(indices []int) []int {
	seen := make(map[int]bool, len(indices))
	out := make([]int, 0, len(indices))
	for _, index := range indices {
		if seen[index] {
			continue
		}
		seen[index] = true
		out = append(out, index)
	}
	sort.Ints(out)
	return out
}

func sameIndexSet(left, right []int) bool {
	left, right = normalizeIndexSet(left), normalizeIndexSet(right)
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
