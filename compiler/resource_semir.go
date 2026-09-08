package compiler

import (
	"fmt"

	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

// ResourceSemanticIR is the checked resource slice of Oak's semantic IR. The
// compiler does not yet claim to project every language feature into SemIR;
// this stage makes the resource authority path production-backed first.
type ResourceSemanticIR struct {
	Model     *SemanticModel
	Module    semir.Module
	Resources typechecker.ResolvedResourceProgram
}

// ResourceSemIR checks the program, resolves syntax-independent resource
// declarations against the checked type environment, emits canonical SemIR,
// and runs the path-sensitive resource checker from that emitted module.
//
// Resource declarations remain an internal semantic input until Oak freezes a
// source or ABI spelling. The projection below is therefore reusable by either
// future frontend without teaching the AST to guess ownership semantics.
func (comp Compilation) ResourceSemIR(declarations []typechecker.ResourceProtocolDeclaration) Stage[*ResourceSemanticIR] {
	return comp.Check().Then(func(model *SemanticModel) (*ResourceSemanticIR, error) {
		resolved, err := model.TypeChecker.ResolveResourceDeclarations(declarations)
		if err != nil {
			return nil, fmt.Errorf("resource resolution failed: %w", err)
		}

		module, err := emitResourceSemIR(resolved)
		if err != nil {
			return nil, fmt.Errorf("resource SemIR emission failed: %w", err)
		}

		resourceModel, err := typechecker.ResourceModelFromSemIR(module)
		if err != nil {
			return nil, fmt.Errorf("resource SemIR projection failed: %w", err)
		}
		// Check() already performed ordinary type checking. Run only resource
		// flow here so diagnostics are not duplicated by a second CheckProgram.
		model.TypeChecker.CheckResourceFlow(model.Tree.Root, resourceModel)
		if err := comp.gate("resource", model.TypeChecker.Diagnostics()); err != nil {
			return nil, err
		}

		return &ResourceSemanticIR{
			Model:     model,
			Module:    module,
			Resources: resolved,
		}, nil
	})
}

func emitResourceSemIR(resources typechecker.ResolvedResourceProgram) (semir.Module, error) {
	module := semir.Module{}
	for _, resourceType := range resources.Types {
		// This projection asserts only the axes established by resource
		// resolution. Type shape, representation, and temporary ownership stay
		// unspecified: permanent resource liveness is orthogonal to them.
		module.Definitions = append(module.Definitions, semir.Definition{
			Name: resourceType.Name,
			Type: semir.Type{Kind: semir.TypeOpaque},
			Authority: semir.Authority{
				Resource: semir.ResourceAuthorityLive,
			},
			Protocol: resourceType.Protocol,
		})
	}

	for _, resourceProtocol := range resources.Protocols {
		protocol := semir.Protocol{
			Name:    resourceProtocol.Name,
			Initial: resourceProtocol.Initial,
		}
		for _, state := range resourceProtocol.States {
			protocol.States = append(protocol.States, semir.State{Name: state})
		}
		for _, resourceTransition := range resourceProtocol.Transitions {
			transition := semir.Transition{
				Name:     resourceTransition.Name,
				Callable: resourceTransition.Callable,
				From:     resourceTransition.From,
				To:       resourceTransition.To,
			}
			for _, index := range resourceTransition.Consumes {
				transition.Effects = append(transition.Effects, semir.ResourceConsumeArgument(index))
			}
			if resourceTransition.ReturnsFresh {
				transition.Effects = append(transition.Effects, semir.ResourceReturnFresh())
			}
			protocol.Transitions = append(protocol.Transitions, transition)
		}
		module.Protocols = append(module.Protocols, protocol)
	}

	if err := module.Validate(); err != nil {
		return semir.Module{}, err
	}
	if err := module.ValidateResourceSemantics(); err != nil {
		return semir.Module{}, err
	}
	return module, nil
}
