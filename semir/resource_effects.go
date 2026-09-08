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
)

// ResourceTransitionSemantics is the resource-authority projection of one
// protocol transition. Parameter index lists are zero-based callable argument
// indices and are sorted deterministically. ReturnsFresh means the result
// carries a new live authority class rather than reviving any consumed input.
type ResourceTransitionSemantics struct {
	Borrowed     []int
	BorrowedMut  []int
	Consumes     []int
	ReturnsFresh bool
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

	sort.Ints(result.Borrowed)
	sort.Ints(result.BorrowedMut)
	sort.Ints(result.Consumes)
	return result, present, nil
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
