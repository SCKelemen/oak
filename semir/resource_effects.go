package semir

import (
	"fmt"
	"sort"
	"strconv"
	"strings"
)

const (
	// ResourceEffectNamespace owns semantic effects that describe or change
	// resource authority. These are SemIR facts, not source syntax.
	ResourceEffectNamespace = "resource"

	// Parameter effects describe how a callable may use one resource argument.
	// Borrowed and borrowed-mutable parameters preserve permanent authority;
	// consumed parameters permanently invalidate the old authority class.
	ResourceEffectBorrow      = "borrow"
	ResourceEffectBorrowMut   = "borrow-mut"
	ResourceEffectConsume     = "consume"
	ResourceEffectReturnFresh = "return-fresh"
	// ResourceEffectReturnAlias marks a result that aliases the argument
	// arg:N: same authority class, no wider permission.
	ResourceEffectReturnAlias = "return-alias"
	// ResourceEffectReturnBorrow marks a result that is a shared borrow
	// dependent on the argument arg:N: while it lives the argument may not
	// be mutated, consumed, or rebound.
	ResourceEffectReturnBorrow = "return-borrow"
	// ResourceEffectReturnBorrowMut marks a result that is a mutable
	// reborrow of the argument arg:N: it may be mutated through
	// borrowed-mut contracts, and while it lives the argument is suspended.
	ResourceEffectReturnBorrowMut = "return-borrow-mut"
	// Callable-contract effects describe what a function-typed parameter
	// (arg:N) requires of the function values passed for it: the mode of
	// the callable's own parameter param:M, or a fresh result.
	ResourceEffectCallableBorrow      = "callable-borrow"
	ResourceEffectCallableBorrowMut   = "callable-borrow-mut"
	ResourceEffectCallableConsume     = "callable-consume"
	ResourceEffectCallableReturnFresh = "callable-return-fresh"
)

// ResourceCallableSemantics is the contract required of a function value
// passed for one function-typed parameter.
type ResourceCallableSemantics struct {
	Argument     int
	Borrowed     []int
	BorrowedMut  []int
	Consumes     []int
	ReturnsFresh bool
}

// ResourceReturnAlias constructs the effect for a result that aliases the
// argument at index.
func ResourceReturnAlias(index int) Effect {
	return Effect{Namespace: ResourceEffectNamespace, Name: ResourceEffectReturnAlias, Parameters: []string{"arg:" + strconv.Itoa(index)}}
}

// ResourceReturnBorrow constructs the effect for a result that is a shared
// borrow of the argument at index.
func ResourceReturnBorrow(index int) Effect {
	return Effect{Namespace: ResourceEffectNamespace, Name: ResourceEffectReturnBorrow, Parameters: []string{"arg:" + strconv.Itoa(index)}}
}

// ResourceTerminalGuarantee names the protocol guarantee that encodes a
// terminal-state obligation: eventually one of the listed states holds.
const ResourceTerminalGuarantee = "terminal"

// EventuallyStates builds the formula eventually(s1 or s2 or ...).
func EventuallyStates(states []string) TemporalExpr {
	if len(states) == 1 {
		return TemporalExpr{Kind: TemporalEventually, Args: []TemporalExpr{{Kind: TemporalAtom, Atom: states[0]}}}
	}
	disjunction := TemporalExpr{Kind: TemporalOr}
	for _, state := range states {
		disjunction.Args = append(disjunction.Args, TemporalExpr{Kind: TemporalAtom, Atom: state})
	}
	return TemporalExpr{Kind: TemporalEventually, Args: []TemporalExpr{disjunction}}
}

// TerminalStates decodes a protocol's terminal-state obligation from its
// guarantees: the states under the "terminal" guarantee's eventually(...)
// formula, or nil when the protocol declares none.
func (p Protocol) TerminalStates() []string {
	for _, guarantee := range p.Guarantees {
		if guarantee.Name != ResourceTerminalGuarantee || guarantee.Formula.Kind != TemporalEventually || len(guarantee.Formula.Args) != 1 {
			continue
		}
		body := guarantee.Formula.Args[0]
		switch body.Kind {
		case TemporalAtom:
			return []string{body.Atom}
		case TemporalOr:
			var states []string
			for _, arg := range body.Args {
				if arg.Kind == TemporalAtom {
					states = append(states, arg.Atom)
				}
			}
			return states
		}
	}
	return nil
}

// ResourceReturnBorrowMut constructs the effect for a result that is a
// mutable reborrow of the argument at index.
func ResourceReturnBorrowMut(index int) Effect {
	return Effect{Namespace: ResourceEffectNamespace, Name: ResourceEffectReturnBorrowMut, Parameters: []string{"arg:" + strconv.Itoa(index)}}
}

// ResourceCallableEffect constructs the effect requiring mode name (one of
// borrow, borrow-mut, consume) of parameter param of the function value
// passed as argument arg.
func ResourceCallableEffect(name string, arg, param int) Effect {
	return Effect{Namespace: ResourceEffectNamespace, Name: "callable-" + name,
		Parameters: []string{"arg:" + strconv.Itoa(arg), "param:" + strconv.Itoa(param)}}
}

// ResourceCallableReturnFresh constructs the effect requiring a fresh
// result of the function value passed as argument arg.
func ResourceCallableReturnFresh(arg int) Effect {
	return Effect{Namespace: ResourceEffectNamespace, Name: ResourceEffectCallableReturnFresh,
		Parameters: []string{"arg:" + strconv.Itoa(arg)}}
}

// ResourceTransitionSemantics is the resource-authority projection of one
// protocol transition. Parameter index lists are zero-based callable argument
// indices and are sorted deterministically. ReturnsFresh means the result
// carries a new live authority class rather than reviving any consumed input.
type ResourceTransitionSemantics struct {
	Borrowed     []int
	BorrowedMut  []int
	Consumes     []int
	ReturnsFresh bool
	// ReturnsAlias and AliasesArgument record a result declared to alias
	// one argument.
	ReturnsAlias    bool
	AliasesArgument int
	// ReturnsBorrow and BorrowsArguments record a result declared to be a
	// shared borrow of the listed arguments (sorted, no duplicates).
	ReturnsBorrow    bool
	BorrowsArguments []int
	// BorrowMutable records that the borrowed result is a mutable reborrow
	// (every origin carried return-borrow-mut rather than return-borrow).
	BorrowMutable bool
	// Callables are the contracts required of function-typed parameters,
	// sorted by argument index.
	Callables []ResourceCallableSemantics
	// Receiver is the authority mode of a method's receiver — one of the
	// resource effect names borrow, borrow-mut, or consume — or empty when
	// the receiver carries no resource contract. It is its own slot: it
	// never shifts the explicit argument indices above.
	Receiver string
}

// ResourceReceiverParameter is the effect parameter spelling that marks a
// method's receiver rather than an explicit argument.
const ResourceReceiverParameter = "receiver"

// ResourceBorrowReceiver, ResourceBorrowMutReceiver, and
// ResourceConsumeReceiver construct the canonical effects for a method's
// receiver authority.
func ResourceBorrowReceiver() Effect    { return resourceReceiverEffect(ResourceEffectBorrow) }
func ResourceBorrowMutReceiver() Effect { return resourceReceiverEffect(ResourceEffectBorrowMut) }
func ResourceConsumeReceiver() Effect   { return resourceReceiverEffect(ResourceEffectConsume) }

func resourceReceiverEffect(name string) Effect {
	return Effect{Namespace: ResourceEffectNamespace, Name: name, Parameters: []string{ResourceReceiverParameter}}
}

// ResourceBorrowArgument constructs the canonical semantic effect for a shared
// borrowed resource parameter.
func ResourceBorrowArgument(index int) Effect {
	return resourceArgumentEffect(ResourceEffectBorrow, index)
}

// ResourceBorrowMutArgument constructs the canonical semantic effect for a
// mutable borrowed resource parameter.
func ResourceBorrowMutArgument(index int) Effect {
	return resourceArgumentEffect(ResourceEffectBorrowMut, index)
}

// ResourceConsumeArgument constructs the canonical semantic effect for a
// consuming parameter. Negative indices are retained so validation can reject
// malformed generated SemIR instead of silently rewriting it.
func ResourceConsumeArgument(index int) Effect {
	return resourceArgumentEffect(ResourceEffectConsume, index)
}

func resourceArgumentEffect(name string, index int) Effect {
	return Effect{
		Namespace:  ResourceEffectNamespace,
		Name:       name,
		Parameters: []string{"arg:" + strconv.Itoa(index)},
	}
}

// ResourceReturnFresh constructs the canonical semantic effect for a
// transition that returns a new resource authority class.
func ResourceReturnFresh() Effect {
	return Effect{Namespace: ResourceEffectNamespace, Name: ResourceEffectReturnFresh}
}

// ResourceSemantics decodes structured resource effects from a transition.
// Effects outside the resource namespace are ignored. Unknown/malformed
// resource effects are rejected so typos cannot silently weaken authority.
func (t Transition) ResourceSemantics() (ResourceTransitionSemantics, bool, error) {
	result := ResourceTransitionSemantics{}
	seenParameter := make(map[int]string)
	seenFresh := false
	present := false

	for _, effect := range t.Effects {
		if effect.Namespace != ResourceEffectNamespace {
			continue
		}
		present = true
		switch effect.Name {
		case ResourceEffectBorrow, ResourceEffectBorrowMut, ResourceEffectConsume:
			if len(effect.Parameters) == 1 && effect.Parameters[0] == ResourceReceiverParameter {
				if result.Receiver != "" {
					return ResourceTransitionSemantics{}, true,
						fmt.Errorf("resource receiver has both %s and %s modes", result.Receiver, effect.Name)
				}
				result.Receiver = effect.Name
				continue
			}
			index, err := decodeResourceArgument(effect)
			if err != nil {
				return ResourceTransitionSemantics{}, true, err
			}
			if previous, exists := seenParameter[index]; exists {
				return ResourceTransitionSemantics{}, true,
					fmt.Errorf("resource argument %d has both %s and %s modes", index, previous, effect.Name)
			}
			seenParameter[index] = effect.Name
			switch effect.Name {
			case ResourceEffectBorrow:
				result.Borrowed = append(result.Borrowed, index)
			case ResourceEffectBorrowMut:
				result.BorrowedMut = append(result.BorrowedMut, index)
			case ResourceEffectConsume:
				result.Consumes = append(result.Consumes, index)
			}

		case ResourceEffectCallableBorrow, ResourceEffectCallableBorrowMut, ResourceEffectCallableConsume, ResourceEffectCallableReturnFresh:
			if err := decodeCallableEffect(effect, &result); err != nil {
				return ResourceTransitionSemantics{}, true, err
			}

		case ResourceEffectReturnAlias:
			index, err := decodeResourceArgument(effect)
			if err != nil {
				return ResourceTransitionSemantics{}, true, err
			}
			if result.ReturnsAlias {
				return ResourceTransitionSemantics{}, true, fmt.Errorf("resource.return-alias is duplicated")
			}
			result.ReturnsAlias, result.AliasesArgument = true, index

		case ResourceEffectReturnBorrow, ResourceEffectReturnBorrowMut:
			index, err := decodeResourceArgument(effect)
			if err != nil {
				return ResourceTransitionSemantics{}, true, err
			}
			for _, existing := range result.BorrowsArguments {
				if existing == index {
					return ResourceTransitionSemantics{}, true, fmt.Errorf("resource.%s arg:%d is duplicated", effect.Name, index)
				}
			}
			mutable := effect.Name == ResourceEffectReturnBorrowMut
			if result.ReturnsBorrow && result.BorrowMutable != mutable {
				return ResourceTransitionSemantics{}, true, fmt.Errorf("a result cannot mix return-borrow and return-borrow-mut origins")
			}
			result.ReturnsBorrow = true
			result.BorrowMutable = mutable
			result.BorrowsArguments = append(result.BorrowsArguments, index)

		case ResourceEffectReturnFresh:
			if len(effect.Parameters) != 0 {
				return ResourceTransitionSemantics{}, true,
					fmt.Errorf("resource.return-fresh does not accept parameters")
			}
			if seenFresh {
				return ResourceTransitionSemantics{}, true,
					fmt.Errorf("resource.return-fresh is duplicated")
			}
			seenFresh = true
			result.ReturnsFresh = true

		default:
			return ResourceTransitionSemantics{}, true,
				fmt.Errorf("unknown resource effect %q", effect.Name)
		}
	}

	if result.ReturnsAlias && result.ReturnsFresh {
		return ResourceTransitionSemantics{}, true, fmt.Errorf("a result cannot be both return-fresh and return-alias")
	}
	if result.ReturnsBorrow && (result.ReturnsFresh || result.ReturnsAlias) {
		return ResourceTransitionSemantics{}, true, fmt.Errorf("a result cannot be return-borrow and also return-fresh or return-alias")
	}
	sort.Ints(result.Borrowed)
	sort.Ints(result.BorrowedMut)
	sort.Ints(result.Consumes)
	sort.Ints(result.BorrowsArguments)
	for i := range result.Callables {
		sort.Ints(result.Callables[i].Borrowed)
		sort.Ints(result.Callables[i].BorrowedMut)
		sort.Ints(result.Callables[i].Consumes)
	}
	sort.Slice(result.Callables, func(i, j int) bool { return result.Callables[i].Argument < result.Callables[j].Argument })
	return result, present, nil
}

// decodeCallableEffect folds one callable-contract effect into the
// semantics of its arg:N function-typed parameter.
func decodeCallableEffect(effect Effect, result *ResourceTransitionSemantics) error {
	if len(effect.Parameters) == 0 || !strings.HasPrefix(effect.Parameters[0], "arg:") {
		return fmt.Errorf("resource.%s expects an arg:<index> parameter first", effect.Name)
	}
	arg, err := strconv.Atoi(strings.TrimPrefix(effect.Parameters[0], "arg:"))
	if err != nil || arg < 0 {
		return fmt.Errorf("resource.%s parameter %q has invalid argument index", effect.Name, effect.Parameters[0])
	}
	var callable *ResourceCallableSemantics
	for i := range result.Callables {
		if result.Callables[i].Argument == arg {
			callable = &result.Callables[i]
		}
	}
	if callable == nil {
		result.Callables = append(result.Callables, ResourceCallableSemantics{Argument: arg})
		callable = &result.Callables[len(result.Callables)-1]
	}
	if effect.Name == ResourceEffectCallableReturnFresh {
		if len(effect.Parameters) != 1 {
			return fmt.Errorf("resource.%s takes only arg:<index>", effect.Name)
		}
		if callable.ReturnsFresh {
			return fmt.Errorf("resource.%s is duplicated for argument %d", effect.Name, arg)
		}
		callable.ReturnsFresh = true
		return nil
	}
	if len(effect.Parameters) != 2 || !strings.HasPrefix(effect.Parameters[1], "param:") {
		return fmt.Errorf("resource.%s expects arg:<index> and param:<index>", effect.Name)
	}
	param, err := strconv.Atoi(strings.TrimPrefix(effect.Parameters[1], "param:"))
	if err != nil || param < 0 {
		return fmt.Errorf("resource.%s parameter %q has invalid parameter index", effect.Name, effect.Parameters[1])
	}
	for _, listed := range [][]int{callable.Borrowed, callable.BorrowedMut, callable.Consumes} {
		for _, existing := range listed {
			if existing == param {
				return fmt.Errorf("callable parameter %d of argument %d has two modes", param, arg)
			}
		}
	}
	switch effect.Name {
	case ResourceEffectCallableBorrow:
		callable.Borrowed = append(callable.Borrowed, param)
	case ResourceEffectCallableBorrowMut:
		callable.BorrowedMut = append(callable.BorrowedMut, param)
	case ResourceEffectCallableConsume:
		callable.Consumes = append(callable.Consumes, param)
	}
	return nil
}

func decodeResourceArgument(effect Effect) (int, error) {
	if len(effect.Parameters) != 1 {
		return 0, fmt.Errorf("resource.%s expects exactly one arg:<index> parameter", effect.Name)
	}
	parameter := effect.Parameters[0]
	if !strings.HasPrefix(parameter, "arg:") {
		return 0, fmt.Errorf("resource.%s parameter %q must be arg:<index>", effect.Name, parameter)
	}
	index, err := strconv.Atoi(strings.TrimPrefix(parameter, "arg:"))
	if err != nil || index < 0 {
		return 0, fmt.Errorf("resource.%s parameter %q has invalid argument index", effect.Name, parameter)
	}
	return index, nil
}

// ValidateResourceSemantics validates every resource-specific transition fact
// in the module. Resource effects require an explicit resolved Callable so a
// protocol-local transition label cannot accidentally affect an unrelated
// source callable with the same spelling.
func (m Module) ValidateResourceSemantics() error {
	for _, protocol := range m.Protocols {
		for _, transition := range protocol.Transitions {
			_, present, err := transition.ResourceSemantics()
			if err != nil {
				return fmt.Errorf("protocol %q transition %q: %w", protocol.Name, transition.Name, err)
			}
			if present && transition.Callable == "" {
				return fmt.Errorf(
					"protocol %q transition %q has resource effects but no resolved callable",
					protocol.Name,
					transition.Name,
				)
			}
		}
	}
	return nil
}
