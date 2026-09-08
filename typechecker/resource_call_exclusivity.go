package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
)

type resourceCallArgument struct {
	index   int
	mode    ResourceParameterMode
	name    string
	node    ast.Node
	tracked bool
}

func resourceParameterModesCompatible(left, right ResourceParameterMode) bool {
	if left == ResourceParameterUnspecified || right == ResourceParameterUnspecified {
		return true
	}
	return left == ResourceParameterBorrowed && right == ResourceParameterBorrowed
}

func (a *typedResourceAnalysis) checkCallResourceExclusivity(expr *ast.InvocationExpression, op ResourceOperation) bool {
	if a == nil || a.flow == nil || expr == nil || len(op.Parameters) == 0 {
		return true
	}

	participants := make([]resourceCallArgument, 0, len(op.Parameters))
	for _, parameter := range op.Parameters {
		if parameter.Index < 0 || parameter.Index >= len(expr.Arguments) {
			continue
		}
		argument := expr.Arguments[parameter.Index]
		if !a.isResourceValue(argument) {
			continue
		}

		participant := resourceCallArgument{
			index: parameter.Index,
			mode:  parameter.Mode,
			node:  argument,
		}
		if ident, ok := argument.(*ast.Identifier); ok && ident != nil && a.flow.Registered(ident.Value) && a.flow.CanUse(ident.Value) {
			participant.name = ident.Value
			participant.tracked = true
		}
		participants = append(participants, participant)

		// Permanent consumption must identify the authority class that becomes
		// unavailable after the call. Until aggregate/field resource provenance
		// is modeled, consuming an untracked resource expression would silently
		// fail to invalidate anything, so reject it rather than weaken authority.
		if parameter.Mode == ResourceParameterConsumed && !participant.tracked {
			a.reportUntrackedResourceArgument(expr, participant, "consuming")
			return false
		}
	}

	for i := 0; i < len(participants); i++ {
		for j := i + 1; j < len(participants); j++ {
			left, right := participants[i], participants[j]
			if resourceParameterModesCompatible(left.mode, right.mode) {
				continue
			}
			if left.tracked && right.tracked {
				if !a.flow.Aliases(left.name, right.name) {
					continue
				}
				a.reportCallAliasConflict(expr, left, right)
				return false
			}

			// An exclusive mode paired with resource-valued expressions whose
			// authority classes are not tracked cannot prove the arguments distinct.
			// Fail closed instead of accepting field projections or other expressions
			// that may denote the same underlying resource.
			primary := left
			if left.mode == ResourceParameterBorrowed && right.mode != ResourceParameterBorrowed {
				primary = right
			}
			a.reportUntrackedResourceArgument(expr, primary, resourceParameterModeAccess(primary.mode))
			return false
		}
	}
	return true
}

func (a *typedResourceAnalysis) isResourceValue(expr ast.Expression) bool {
	if a == nil || a.tc == nil || a.tc.env == nil || expr == nil {
		return false
	}
	typ := a.tc.env.CheckedExpressionType(expr)
	name := nominalTypeName(typ)
	return name != "" && a.model.ResourceTypes[name]
}

func (a *typedResourceAnalysis) reportCallAliasConflict(expr *ast.InvocationExpression, left, right resourceCallArgument) {
	primary, other := left, right
	if left.mode == ResourceParameterBorrowed && right.mode != ResourceParameterBorrowed {
		primary, other = right, left
	}

	callable, _ := a.callableIdentity(expr)
	title := fmt.Sprintf(
		"resource argument %d to %q requires %s authority, but argument %d aliases the same resource",
		primary.index+1,
		callable,
		resourceParameterModeAccess(primary.mode),
		other.index+1,
	)
	d := a.tc.addResourceDiagnosticWithCode(primary.node, CodeResourceCallAliasConflict, title)
	d.AddSecondary(diagnostic.NodeToRange(other.node), fmt.Sprintf(
		"argument %d uses the same authority through %q",
		other.index+1,
		other.name,
	))
	for _, edge := range a.flow.AliasPath(primary.name, other.name) {
		message := fmt.Sprintf("resource alias %q derives authority from %q", edge.Child, edge.Parent)
		if edge.Origin != nil {
			d.AddSecondary(diagnostic.NodeToRange(edge.Origin), message)
		} else {
			d.AddNote(message)
		}
	}
	d.AddNote("shared resource borrows may alias; mutable borrows and consuming parameters require exclusive authority for the duration of the call")
	d.AddHelp("pass distinct resource authority classes, or use shared-borrowed parameters when aliasing is intended and semantically valid")
}

func (a *typedResourceAnalysis) reportUntrackedResourceArgument(expr *ast.InvocationExpression, argument resourceCallArgument, access string) {
	callable, _ := a.callableIdentity(expr)
	title := fmt.Sprintf(
		"resource argument %d to %q requires %s authority, but its resource provenance is not traceable",
		argument.index+1,
		callable,
		access,
	)
	d := a.tc.addResourceDiagnosticWithCode(argument.node, CodeResourceCallAliasConflict, title)
	d.AddNote("Oak must know the resource authority class to prove call-local exclusivity and to record permanent consumption")
	d.AddHelp("pass a resource whose authority class is already tracked, or obtain a fresh resource from an operation declared to return fresh authority")
}

func resourceParameterModeAccess(mode ResourceParameterMode) string {
	switch mode {
	case ResourceParameterBorrowedMut:
		return "exclusive mutable"
	case ResourceParameterConsumed:
		return "exclusive consuming"
	case ResourceParameterBorrowed:
		return "shared borrowed"
	default:
		return "resource"
	}
}
