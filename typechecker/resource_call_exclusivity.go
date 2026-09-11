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
	fresh   bool
}

func resourceParameterModesCompatible(left, right ResourceParameterMode) bool {
	if left == ResourceParameterUnspecified || right == ResourceParameterUnspecified {
		return true
	}
	return left == ResourceParameterBorrowed && right == ResourceParameterBorrowed
}

func (a *typedResourceAnalysis) checkCallResourceExclusivity(expr *ast.InvocationExpression, op ResourceOperation) bool {
	if a == nil || a.flow == nil || expr == nil || (len(op.Parameters) == 0 && op.Receiver == ResourceParameterUnspecified) {
		return true
	}

	// The receiver of a method call participates under the contract's
	// receiver slot (index -1), alongside the explicit arguments, so a
	// consuming receiver and a borrowed argument naming one resource
	// conflict exactly as two arguments would.
	type slot struct {
		index    int
		mode     ResourceParameterMode
		argument ast.Expression
	}
	slots := make([]slot, 0, len(op.Parameters)+1)
	if receiver := methodReceiver(expr); receiver != nil && op.Receiver != ResourceParameterUnspecified {
		slots = append(slots, slot{index: -1, mode: op.Receiver, argument: receiver})
	}
	for _, parameter := range op.Parameters {
		if parameter.Index < 0 || parameter.Index >= len(expr.Arguments) {
			a.tc.addResourceDiagnosticWithCode(expr, CodeResourceCallAliasConflict,
				"resource contract refers to an argument outside this call")
			return false
		}
		slots = append(slots, slot{index: parameter.Index, mode: parameter.Mode, argument: expr.Arguments[parameter.Index]})
	}

	participants := make([]resourceCallArgument, 0, len(slots))
	for _, parameter := range slots {
		argument := parameter.argument
		if !a.isResourceValue(argument) {
			continue
		}

		participant := resourceCallArgument{
			index: parameter.index,
			mode:  parameter.mode,
			node:  argument,
		}
		if ident, ok := argument.(*ast.Identifier); ok && ident != nil && a.flow.Registered(ident.Value) {
			if !a.flow.CanUse(ident.Value) {
				// Ordinary argument evaluation owns the use-after-consume diagnostic.
				a.use(ident.Value, ident)
				return false
			}
			participant.name = ident.Value
			participant.tracked = !a.unknownResources[ident.Value]
		}
		if call, ok := argument.(*ast.InvocationExpression); ok && a.freshCalls[call] {
			// Each successfully evaluated fresh result has independent authority.
			// It needs no source binding and cannot revive an input authority class.
			participant.tracked = true
			participant.fresh = true
		}
		participants = append(participants, participant)

		// Permanent consumption must identify the authority class that becomes
		// unavailable after the call. Until aggregate/field resource provenance
		// is modeled, consuming an untracked resource expression would silently
		// fail to invalidate anything, so reject it rather than weaken authority.
		if parameter.mode == ResourceParameterConsumed && !participant.tracked {
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
			// A checked fresh result establishes independent authority even when
			// the other participant's provenance is unknown. Unknown consuming
			// participants have already been rejected above.
			if left.fresh || right.fresh {
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
			unknown := left
			if left.tracked {
				unknown = right
			}
			a.reportUntrackedResourcePair(expr, primary, unknown)
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
		"resource %s to %q requires %s authority, but %s aliases the same resource",
		positionLabel(primary.index),
		callable,
		resourceParameterModeAccess(primary.mode),
		positionLabel(other.index),
	)
	d := a.tc.addResourceDiagnosticWithCode(primary.node, CodeResourceCallAliasConflict, title)
	d.AddSecondary(diagnostic.NodeToRange(other.node), fmt.Sprintf(
		"%s uses the same authority through %q",
		positionLabel(other.index),
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
		"resource %s to %q requires %s authority, but its resource provenance is not traceable",
		positionLabel(argument.index),
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

func (a *typedResourceAnalysis) reportUntrackedResourcePair(expr *ast.InvocationExpression, exclusive, unknown resourceCallArgument) {
	callable, _ := a.callableIdentity(expr)
	d := a.tc.addResourceDiagnosticWithCode(exclusive.node, CodeResourceCallAliasConflict,
		fmt.Sprintf("resource %s to %q requires %s authority, but %s resource provenance is not traceable",
			positionLabel(exclusive.index), callable, resourceParameterModeAccess(exclusive.mode), positionLabel(unknown.index)))
	d.AddSecondary(diagnostic.NodeToRange(unknown.node),
		fmt.Sprintf("%s has unknown resource provenance", positionLabel(unknown.index)))
	d.AddNote("unknown provenance cannot establish distinct resource authority classes")
	d.AddHelp("provide traceable resource provenance; introducing a local name alone does not establish independence")
}

// positionLabel names a call position in diagnostics: the receiver slot
// (index -1) or a one-based explicit argument.
func positionLabel(index int) string {
	if index < 0 {
		return "receiver"
	}
	return fmt.Sprintf("argument %d", index+1)
}
