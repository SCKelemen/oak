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
// The declarations passed to this explicit stage are authoritative for the
// stage. Compilation-level resource configuration is intentionally not run a
// second time. Resource declarations remain an internal semantic input until
// Oak freezes a source or ABI spelling.
func (comp Compilation) ResourceSemIR(declarations []typechecker.ResourceProtocolDeclaration) Stage[*ResourceSemanticIR] {
	return comp.check(nil).Then(func(model *SemanticModel) (*ResourceSemanticIR, error) {
		resolved, module, err := comp.checkResourceProtocols(model, declarations)
		if err != nil {
			return nil, err
		}

		return &ResourceSemanticIR{
			Model:     model,
			Module:    module,
			Resources: resolved,
		}, nil
	})
}

func (comp Compilation) checkResourceProtocols(
	model *SemanticModel,
	declarations []typechecker.ResourceProtocolDeclaration,
) (typechecker.ResolvedResourceProgram, semir.Module, error) {
	resolved, err := model.TypeChecker.ResolveResourceDeclarations(declarations)
	if err != nil {
		return typechecker.ResolvedResourceProgram{}, semir.Module{}, fmt.Errorf("resource resolution failed: %w", err)
	}

	module, err := emitResourceSemIR(resolved)
	if err != nil {
		return typechecker.ResolvedResourceProgram{}, semir.Module{}, fmt.Errorf("resource SemIR emission failed: %w", err)
	}

	resourceModel, err := typechecker.ResourceModelFromSemIR(module)
	if err != nil {
		return typechecker.ResolvedResourceProgram{}, semir.Module{}, fmt.Errorf("resource SemIR projection failed: %w", err)
	}
	// Ordinary type checking has already populated the environment. Run only
	// resource flow here so diagnostics are not duplicated by CheckProgram.
	model.TypeChecker.CheckResourceFlow(model.Tree.Root, resourceModel)
	if err := comp.gate("resource", model.TypeChecker.Diagnostics(), model.Tree.Modules); err != nil {
		return typechecker.ResolvedResourceProgram{}, semir.Module{}, err
	}

	return resolved, module, nil
}

func cloneResourceProtocolDeclarations(declarations []typechecker.ResourceProtocolDeclaration) []typechecker.ResourceProtocolDeclaration {
	if len(declarations) == 0 {
		return nil
	}
	cloned := make([]typechecker.ResourceProtocolDeclaration, len(declarations))
	for i, declaration := range declarations {
		cloned[i] = declaration
		cloned[i].ResourceTypes = append([]string(nil), declaration.ResourceTypes...)
		cloned[i].States = append([]string(nil), declaration.States...)
		cloned[i].Transitions = make([]typechecker.ResourceTransitionDeclaration, len(declaration.Transitions))
		for j, transition := range declaration.Transitions {
			cloned[i].Transitions[j] = transition
			cloned[i].Transitions[j].Parameters = append([]typechecker.ResourceParameterDeclaration(nil), transition.Parameters...)
			cloned[i].Transitions[j].Consumes = append([]int(nil), transition.Consumes...)
		}
	}
	return cloned
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
			for _, parameter := range resourceTransition.Parameters {
				if parameter.Callable != nil {
					for _, inner := range parameter.Callable.Parameters {
						name := ""
						switch inner.Mode {
						case typechecker.ResourceParameterBorrowed:
							name = "borrow"
						case typechecker.ResourceParameterBorrowedMut:
							name = "borrow-mut"
						case typechecker.ResourceParameterConsumed:
							name = "consume"
						default:
							return semir.Module{}, fmt.Errorf("resource callable %q argument %d has an unresolved callable contract mode %d", resourceTransition.Callable, parameter.Index, inner.Mode)
						}
						transition.Effects = append(transition.Effects, semir.ResourceCallableEffect(name, parameter.Index, inner.Index))
					}
					if parameter.Callable.ReturnsFresh {
						transition.Effects = append(transition.Effects, semir.ResourceCallableReturnFresh(parameter.Index))
					}
					continue
				}
				switch parameter.Mode {
				case typechecker.ResourceParameterBorrowed:
					transition.Effects = append(transition.Effects, semir.ResourceBorrowArgument(parameter.Index))
				case typechecker.ResourceParameterBorrowedMut:
					transition.Effects = append(transition.Effects, semir.ResourceBorrowMutArgument(parameter.Index))
				case typechecker.ResourceParameterConsumed:
					transition.Effects = append(transition.Effects, semir.ResourceConsumeArgument(parameter.Index))
				default:
					return semir.Module{}, fmt.Errorf("resource callable %q has unresolved parameter mode %d", resourceTransition.Callable, parameter.Mode)
				}
			}
			switch resourceTransition.Receiver {
			case typechecker.ResourceParameterUnspecified:
			case typechecker.ResourceParameterBorrowed:
				transition.Effects = append(transition.Effects, semir.ResourceBorrowReceiver())
			case typechecker.ResourceParameterBorrowedMut:
				transition.Effects = append(transition.Effects, semir.ResourceBorrowMutReceiver())
			case typechecker.ResourceParameterConsumed:
				transition.Effects = append(transition.Effects, semir.ResourceConsumeReceiver())
			default:
				return semir.Module{}, fmt.Errorf("resource callable %q has unresolved receiver mode %d", resourceTransition.Callable, resourceTransition.Receiver)
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
