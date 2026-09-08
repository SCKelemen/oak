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
// protocol transition. Consumes contains zero-based explicit callable argument
// indices; ConsumesReceiver marks the receiver authority independently of those
// arguments. ReturnsFresh means the transition's result carries new live
// authority rather than reviving any consumed input value.
type ResourceTransitionSemantics struct {
	Consumes         []int
	ConsumesReceiver bool
	ReturnsFresh     bool
}

// ResourceConsumeArgument constructs the canonical semantic effect for a
// consuming explicit parameter. Negative indices are retained so validation
// can reject malformed generated SemIR instead of silently rewriting it.
func ResourceConsumeArgument(index int) Effect {
	return Effect{
		Namespace:  ResourceEffectNamespace,
		Name:       ResourceEffectConsume,
		Parameters: []string{"arg:" + strconv.Itoa(index)},
	}
}

// ResourceConsumeReceiver constructs the canonical semantic effect for a
// consuming method receiver. The receiver is a distinct authority target, not
// argument zero: method FunctionType parameters contain only explicit args.
func ResourceConsumeReceiver() Effect {
	return Effect{
		Namespace:  ResourceEffectNamespace,
		Name:       ResourceEffectConsume,
		Parameters: []string{"receiver"},
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
	seenReceiver := false
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
					fmt.Errorf("resource.consume expects exactly one receiver or arg:<index> parameter")
			}
			parameter := effect.Parameters[0]
			if parameter == "receiver" {
				if seenReceiver {
					return ResourceTransitionSemantics{}, true,
						fmt.Errorf("resource.consume duplicates receiver")
				}
				seenReceiver = true
				result.ConsumesReceiver = true
				continue
			}
			if !strings.HasPrefix(parameter, "arg:") {
				return ResourceTransitionSemantics{}, true,
					fmt.Errorf("resource.consume parameter %q must be receiver or arg:<index>", parameter)
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

func resourceReceiverFromCallable(callable string) string {
	separator := strings.LastIndex(callable, "::")
	if separator <= 0 || separator+2 >= len(callable) {
		return ""
	}
	return callable[:separator]
}

// ValidateResourceSemantics validates every resource-specific transition fact
// in the module. Resource effects require an explicit resolved Callable so a
// protocol-local transition label cannot accidentally affect an unrelated
// source callable with the same spelling. Receiver consumption additionally
// requires a receiver-qualified callable whose receiver is resource-bearing.
func (m Module) ValidateResourceSemantics() error {
	resourceDefinitions := make(map[string]bool)
	for _, definition := range m.Definitions {
		if definition.Authority.Resource != ResourceAuthorityUnspecified {
			resourceDefinitions[definition.Name] = true
		}
	}

	for _, protocol := range m.Protocols {
		for _, transition := range protocol.Transitions {
			semantics, present, err := transition.ResourceSemantics()
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
			if semantics.ConsumesReceiver {
				receiver := resourceReceiverFromCallable(transition.Callable)
				if receiver == "" {
					return fmt.Errorf(
						"protocol %q transition %q consumes a receiver but callable %q has no receiver identity",
						protocol.Name,
						transition.Name,
						transition.Callable,
					)
				}
				if !resourceDefinitions[receiver] {
					return fmt.Errorf(
						"protocol %q transition %q consumes receiver %q without a resource-bearing definition",
						protocol.Name,
						transition.Name,
						receiver,
					)
				}
			}
		}
	}
	return nil
}
