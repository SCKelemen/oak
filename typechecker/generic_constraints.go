package typechecker

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

const constraintBindingPrefix = "\x00oak.constraint."

// constraintSetType is checker-only lexical metadata. It is deliberately not
// embedded in TypeVar, so qualified-type requirements do not become part of
// type identity, substitution, layout, or runtime representation.
type constraintSetType struct {
	Requirements []string
}

func (t *constraintSetType) String() string { return strings.Join(t.Requirements, " & ") }
func (t *constraintSetType) Equals(other Type) bool {
	o, ok := other.(*constraintSetType)
	if !ok || len(t.Requirements) != len(o.Requirements) {
		return false
	}
	for i := range t.Requirements {
		if t.Requirements[i] != o.Requirements[i] {
			return false
		}
	}
	return true
}

func constraintBindingName(typeVarName string) string {
	return constraintBindingPrefix + typeVarName
}

// constraintRequirements returns the named requirements attached to one type variable.
// Constraint.Interfaces is the historical field name; requirements may now be either
// method interfaces or semantic record shapes.
func constraintRequirements(varName string, constraints []Constraint) []string {
	var requirements []string
	for _, constraint := range constraints {
		if constraint.Var != varName {
			continue
		}
		requirements = append(requirements, constraint.Interfaces...)
	}
	return requirements
}

func (c Constraint) String() string {
	return fmt.Sprintf("%s: %s", c.Var, strings.Join(c.Interfaces, " & "))
}

// bindConstrainedTypeVars makes source-level type parameters visible while the
// generic function signature and body are checked. Requirements are stored in
// a checker-only lexical binding next to the TypeVar binding.
func bindConstrainedTypeVars(env *TypeEnvironment, typeVars []string, constraints []Constraint) {
	unifier := NewUnifier()
	for _, name := range typeVars {
		env.SetType(name, unifier.FreshTypeVar(name))
		env.SetType(constraintBindingName(name), &constraintSetType{
			Requirements: constraintRequirements(name, constraints),
		})
	}
}

func (tc *TypeChecker) validateGenericConstraints(constraints []Constraint, env *TypeEnvironment, node ast.Node) bool {
	valid := true
	for _, constraint := range constraints {
		for _, requirementName := range constraint.Interfaces {
			requirement, ok := env.GetType(requirementName)
			if !ok {
				tc.addTypeDiagnostic(
					node,
					CodeConstraintRequirementMissing,
					fmt.Sprintf("constraint `%s` refers to unknown requirement `%s`", constraint.Var, requirementName),
				).AddHelp(fmt.Sprintf("define `%s` as a record shape or interface before using it as a constraint", requirementName))
				valid = false
				continue
			}
			switch requirement.(type) {
			case *InterfaceType, *RecordType:
				// Static method interface or static semantic record-shape requirement.
			default:
				tc.addTypeDiagnostic(
					node,
					CodeConstraintRequirementInvalid,
					fmt.Sprintf("`%s` cannot be used as a generic constraint", requirementName),
				).AddNote("generic requirements must name a semantic record shape or interface")
				valid = false
			}
		}
	}
	return valid
}

// parseTypeExpressionInEnv resolves a type expression in a specific lexical
// environment without changing the caller's long-lived environment.
func (tc *TypeChecker) parseTypeExpressionInEnv(expr ast.Expression, env *TypeEnvironment) Type {
	old := tc.env
	tc.env = env
	defer func() { tc.env = old }()
	return tc.parseTypeExpression(expr)
}

// recordSatisfiesShape is the type-checker projection of Oak's semantic
// record-shape relation. Extra candidate fields are allowed; order and physical
// representation are absent from this layer by construction.
func recordSatisfiesShape(candidate, required *RecordType) bool {
	if candidate == nil || required == nil {
		return false
	}
	for name, requiredType := range required.Fields {
		candidateType, ok := candidate.Fields[name]
		if !ok || !candidateType.Equals(requiredType) {
			return false
		}
	}
	return true
}

func (tc *TypeChecker) asRecordType(typ Type) (*RecordType, bool) {
	if record, ok := typ.(*RecordType); ok {
		return record, true
	}
	if named, ok := typ.(*ADTType); ok {
		resolved, found := tc.env.GetType(named.Name)
		if !found {
			return nil, false
		}
		record, ok := resolved.(*RecordType)
		return record, ok
	}
	return nil, false
}

// constrainedFieldType returns a field that is guaranteed by at least one
// semantic record-shape requirement on the type variable. If two requirements
// guarantee the same name with incompatible types, the field is not usable.
func (tc *TypeChecker) constrainedFieldType(typeVar *TypeVar, fieldName string) (Type, bool) {
	binding, ok := tc.env.GetType(constraintBindingName(typeVar.Name))
	if !ok {
		return nil, false
	}
	set, ok := binding.(*constraintSetType)
	if !ok {
		return nil, false
	}

	var result Type
	found := false
	for _, requirementName := range set.Requirements {
		requirement, ok := tc.env.GetType(requirementName)
		if !ok {
			continue
		}
		shape, ok := requirement.(*RecordType)
		if !ok {
			continue
		}
		fieldType, ok := shape.Fields[fieldName]
		if !ok {
			continue
		}
		if !found {
			result = fieldType
			found = true
			continue
		}
		if !result.Equals(fieldType) {
			return nil, false
		}
	}
	return result, found
}

// constraintMismatchDetail explains one deterministic record-shape mismatch in
// source-level terms. Method-interface details will receive the same treatment
// when method constraint discharge is migrated to first-class diagnostics.
func (tc *TypeChecker) constraintMismatchDetail(concreteType Type, constraint Constraint) string {
	candidate, ok := tc.asRecordType(concreteType)
	if !ok {
		return ""
	}

	for _, requirementName := range constraint.Interfaces {
		requirement, ok := tc.env.GetType(requirementName)
		if !ok {
			continue
		}
		shape, ok := requirement.(*RecordType)
		if !ok {
			continue
		}

		names := make([]string, 0, len(shape.Fields))
		for name := range shape.Fields {
			names = append(names, name)
		}
		sort.Strings(names)

		for _, name := range names {
			requiredType := shape.Fields[name]
			candidateType, present := candidate.Fields[name]
			if !present {
				return fmt.Sprintf("`%s` requires field `%s: %s`, but the inferred type has no `%s` field", requirementName, name, requiredType, name)
			}
			if !candidateType.Equals(requiredType) {
				return fmt.Sprintf("`%s` requires `%s: %s`, but the inferred type provides `%s: %s`", requirementName, name, requiredType, name, candidateType)
			}
		}
	}
	return ""
}

// monomorphicConstraintBinding resolves a blocked scheme's original binder by
// identity. Enclosing expression transactions may have staged its solution
// without committing it to scheme.Monomorphic yet.
func (tc *TypeChecker) monomorphicConstraintBinding(scheme *TypeScheme, bindings Substitution, name string) (Type, bool) {
	var variable *TypeVar
	for _, candidate := range typeVarsIn(scheme.Type) {
		if candidate.Name != name {
			continue
		}
		if variable != nil {
			return nil, false
		}
		variable = candidate
	}
	if variable == nil {
		return nil, false
	}

	concreteType := scheme.Monomorphic.Apply(variable)
	concreteType = tc.applyPendingMonomorphic(concreteType)
	concreteType = bindings.Apply(concreteType)
	concreteType = tc.applyPendingMonomorphic(concreteType)
	if len(typeVarsIn(concreteType)) != 0 {
		return nil, false
	}
	return concreteType, true
}

// checkFunctionConstraintBindings discharges the qualified-type obligations
// after generic argument inference has produced concrete type bindings.
func (tc *TypeChecker) checkFunctionConstraintBindings(scheme *TypeScheme, bindings Substitution, expr ast.Node) {
	for _, constraint := range scheme.Constraints {
		concreteType, ok := bindings.LookupName(constraint.Var)
		if scheme.Monomorphic != nil {
			concreteType, ok = tc.monomorphicConstraintBinding(scheme, bindings, constraint.Var)
		}
		if !ok {
			tc.addTypeDiagnostic(
				expr,
				CodeConstraintInferenceFailed,
				fmt.Sprintf("cannot infer type argument `%s` required by `%s`", constraint.Var, constraint),
			).AddNote("the call does not provide enough information to choose one sound type argument").
				AddHelp(fmt.Sprintf("add a local annotation or pass an argument that determines `%s`", constraint.Var))
			continue
		}
		if !tc.SatisfiesConstraint(concreteType, constraint) {
			d := tc.addTypeDiagnostic(
				expr,
				CodeConstraintUnsatisfied,
				fmt.Sprintf("inferred type `%s` does not satisfy `%s`", concreteType, constraint),
			)
			d.AddNote(fmt.Sprintf("inference chose `%s = %s` for this call", constraint.Var, concreteType))
			if detail := tc.constraintMismatchDetail(concreteType, constraint); detail != "" {
				d.AddNote(detail)
			}
			d.AddHelp("pass a value that satisfies the declared requirement or change the generic contract explicitly")
		}
	}
}
