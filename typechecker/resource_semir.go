package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

// ResourceModelFromSemIR derives the typechecker's executable resource model
// from checked semantic facts. Resource-bearing definitions are identified by
// their Authority.Resource axis; consuming/fresh-return operations come from
// structured resource effects bound to resolved protocol callables.
func ResourceModelFromSemIR(module semir.Module) (ResourceModel, error) {
	if err := module.Validate(); err != nil {
		return ResourceModel{}, fmt.Errorf("invalid semantic module: %w", err)
	}
	if err := module.ValidateResourceSemantics(); err != nil {
		return ResourceModel{}, err
	}

	model := NewResourceModel()
	for _, definition := range module.Definitions {
		switch definition.Authority.Resource {
		case semir.ResourceAuthorityUnspecified:
			continue
		case semir.ResourceAuthorityLive,
			semir.ResourceAuthorityConsumed,
			semir.ResourceAuthorityMaybeConsumed:
			model.MarkResourceType(definition.Name)
		default:
			return ResourceModel{}, fmt.Errorf(
				"definition %q has invalid resource authority %q",
				definition.Name,
				definition.Authority.Resource,
			)
		}
	}

	fullSemantics := make(map[string]semir.ResourceTransitionSemantics)
	for _, protocol := range module.Protocols {
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
				Consumes:     append([]int(nil), semantics.Consumes...),
				ReturnsFresh: semantics.ReturnsFresh,
			})
		}
	}

	return model, nil
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
	if left.ReturnsFresh != right.ReturnsFresh || len(left.Consumes) != len(right.Consumes) {
		return false
	}
	for i := range left.Consumes {
		if left.Consumes[i] != right.Consumes[i] {
			return false
		}
	}
	return true
}

func sameResourceTransitionSemantics(left, right semir.ResourceTransitionSemantics) bool {
	if left.ReturnsFresh != right.ReturnsFresh {
		return false
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
