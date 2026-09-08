package semir

import (
	"fmt"
	"sort"
	"strconv"
	"strings"
)

const (
	// ResourceEffectNamespace owns semantic effects that change resource
	// authority. These are SemIR facts, not source syntax.
	ResourceEffectNamespace   = "resource"
	ResourceEffectConsume     = "consume"
	ResourceEffectReturnFresh = "return-fresh"
)

// ResourceTransitionSemantics is the resource-authority projection of one
// protocol transition. Consumes contains zero-based callable argument indices;
// ReturnsFresh means the transition's result carries new live authority rather
// than reviving any consumed input value.
type ResourceTransitionSemantics struct {
	Consumes     []int
	ReturnsFresh bool
}

// ResourceConsumeArgument constructs the canonical semantic effect for a
// consuming parameter. Negative indices are retained so validation can reject
// malformed generated SemIR instead of silently rewriting it.
func ResourceConsumeArgument(index int) Effect {
	return Effect{
		Namespace:  ResourceEffectNamespace,
		Name:       ResourceEffectConsume,
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
// resource effects are rejected so typos cannot silently weaken consumption.
func (t Transition) ResourceSemantics() (ResourceTransitionSemantics, bool, error) {
	result := ResourceTransitionSemantics{}
	seenConsume := make(map[int]bool)
	seenFresh := false
	present := false

	for _, effect := range t.Effects {
		if effect.Namespace != ResourceEffectNamespace {
			continue
		}
		present = true
		switch effect.Name {
		case ResourceEffectConsume:
			if len(effect.Parameters) != 1 {
				return ResourceTransitionSemantics{}, true,
					fmt.Errorf("resource.consume expects exactly one arg:<index> parameter")
			}
			parameter := effect.Parameters[0]
			if !strings.HasPrefix(parameter, "arg:") {
				return ResourceTransitionSemantics{}, true,
					fmt.Errorf("resource.consume parameter %q must be arg:<index>", parameter)
			}
			index, err := strconv.Atoi(strings.TrimPrefix(parameter, "arg:"))
			if err != nil || index < 0 {
				return ResourceTransitionSemantics{}, true,
					fmt.Errorf("resource.consume parameter %q has invalid argument index", parameter)
			}
			if seenConsume[index] {
				return ResourceTransitionSemantics{}, true,
					fmt.Errorf("resource.consume duplicates argument %d", index)
			}
			seenConsume[index] = true
			result.Consumes = append(result.Consumes, index)

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

	sort.Ints(result.Consumes)
	return result, present, nil
}

// ValidateResourceSemantics validates every resource-specific transition fact
// in the module. Module.Validate owns the generic SemIR schema; this method is
// the resource protocol refinement consumed by resource-aware frontends.
func (m Module) ValidateResourceSemantics() error {
	for _, protocol := range m.Protocols {
		for _, transition := range protocol.Transitions {
			if _, _, err := transition.ResourceSemantics(); err != nil {
				return fmt.Errorf("protocol %q transition %q: %w", protocol.Name, transition.Name, err)
			}
		}
	}
	return nil
}
