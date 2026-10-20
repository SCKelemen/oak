package typechecker

import (
	"fmt"
)

// TypeScheme represents a polymorphic type scheme: ∀α₁...αₙ. C => τ
// Where C is a set of constraints (interface requirements)
// This is the basis for HM-style type inference with qualified types
type TypeScheme struct {
	// Type variables that are quantified over (∀α₁...αₙ)
	TypeVars []string
	// QuantifiedBinders records the actual binder identities for inferred
	// schemes. Explicit legacy schemes may use TypeVars alone until migrated.
	// Never resolve inferred quantification by the variable's printed name.
	QuantifiedBinders []*TypeVar
	// Constraints: interface requirements (e.g., "T: Reader & Writer")
	// These are checked at instantiation time
	Constraints []Constraint
	// The underlying type (τ)
	Type Type
	// GeneralizationBarriers preserves authority/effect evidence independently
	// of whether this scheme has any locally free variables to specialize.
	GeneralizationBarriers GeneralizationBarrier
	// Monomorphic is non-nil for a generalization-blocked scheme with locally
	// free variables. Its substitution is shared by every use.
	Monomorphic Substitution
}

// Constraint represents an interface constraint on a type variable
// e.g., "T: Reader & Writer" becomes [Constraint{Var: "T", Interfaces: ["Reader", "Writer"]}]
// For intersection types, multiple interfaces are listed
type Constraint struct {
	Var        string   // Type variable name (e.g., "T", "U")
	Interfaces []string // Required interfaces (e.g., ["Reader", "Writer"])
}

// SatisfiesConstraint checks if a concrete type satisfies an interface constraint
// This is used when instantiating a polymorphic function with interface constraints
// Note: This function needs access to TypeChecker, so it's defined in typechecker.go
// We'll add a method to TypeChecker instead

func (s *TypeScheme) String() string {
	if len(s.TypeVars) == 0 && len(s.Constraints) == 0 {
		return s.Type.String()
	}

	var out string
	if len(s.TypeVars) > 0 {
		out += "∀"
		for i, v := range s.TypeVars {
			if i > 0 {
				out += ", "
			}
			out += v
		}
		out += ". "
	}

	if len(s.Constraints) > 0 {
		for i, c := range s.Constraints {
			if i > 0 {
				out += ", "
			}
			out += fmt.Sprintf("%s: %v", c.Var, c.Interfaces)
		}
		out += " => "
	}

	out += s.Type.String()
	return out
}

// monomorphicGroup is deliberately non-zero-sized so distinct allocations
// have distinct pointer identity under the Go specification.
type monomorphicGroup struct{ identity byte }

// TypeVar represents a type variable (α, β, γ, ...)
// Used during type inference
type TypeVar struct {
	Name string // e.g., "α", "β", or "T", "U"
	ID   int    // Unique identifier for fresh type variables

	// Monomorphic is shared by every occurrence descended from a blocked
	// binding. It makes the variable participate persistently in unification
	// even through aliases and higher-order arguments.
	Monomorphic      Substitution
	monomorphicGroup *monomorphicGroup
}

func (tv *TypeVar) String() string {
	if tv.Name != "" {
		return tv.Name
	}
	return fmt.Sprintf("α%d", tv.ID)
}

func (tv *TypeVar) Equals(other Type) bool {
	otherTV, ok := other.(*TypeVar)
	return ok && tv == otherTV
}

// Substitution represents a type substitution: [α₁ ↦ τ₁, α₂ ↦ τ₂, ...]
type Substitution map[*TypeVar]Type

// Apply applies a substitution to a type, returning a new type
func (sub Substitution) Apply(typ Type) Type {
	switch t := typ.(type) {
	case *TypeVar:
		if replacement, ok := sub[t]; ok {
			if replacement == t {
				return t
			}
			return sub.Apply(replacement)
		}
		if t.Monomorphic != nil {
			if replacement, ok := t.Monomorphic[t]; ok {
				if replacement == t {
					return t
				}
				return t.Monomorphic.Apply(replacement)
			}
		}
		return t
	case *PrimitiveType:
		return t // Primitives are unchanged
	case *StringType:
		return t
	case *BoolType:
		return t
	case *UnitType:
		return t
	case *ADTType:
		return t // ADT names are unchanged
	case *RecordType:
		// Apply substitution to all field types; nominal name and
		// declaration order survive (layout-significant metadata).
		newFields := make(map[string]Type)
		for name, fieldType := range t.Fields {
			newFields[name] = sub.Apply(fieldType)
		}
		return &RecordType{Fields: newFields, Name: t.Name, Order: t.Order, Struct: t.Struct, Open: t.Open, Row: t.Row}
	case *FunctionType:
		// Apply substitution to parameter and return types
		newParams := make([]Type, len(t.Parameters))
		for i, param := range t.Parameters {
			newParams[i] = sub.Apply(param)
		}
		return &FunctionType{
			Parameters: newParams,
			ReturnType: sub.Apply(t.ReturnType),
			Variadic:   t.Variadic,
		}
	case *ArrayType:
		return &ArrayType{
			Length:      t.Length,
			IsSlice:     t.IsSlice,
			IsSpan:      t.IsSpan,
			ElementType: sub.Apply(t.ElementType),
			Align:       t.Align,
		}
	case *GenericType:
		// Apply substitution to type arguments
		newArgs := make([]Type, len(t.TypeArgs))
		for i, arg := range t.TypeArgs {
			newArgs[i] = sub.Apply(arg)
		}
		return &GenericType{
			Name:     t.Name,
			TypeArgs: newArgs,
		}
	case *UnionType:
		result := *t
		result.Types = sub.applyTypeList(t.Types)
		return &result
	case *IntersectionType:
		result := *t
		result.Types = sub.applyTypeList(t.Types)
		return &result
	case *NarrowedADTVariantType:
		result := *t
		result.TypeArgs = sub.applyTypeList(t.TypeArgs)
		return &result
	case *BufferType:
		result := *t
		result.Element = sub.Apply(t.Element)
		return &result
	case *AtomicType:
		result := *t
		result.Element = sub.Apply(t.Element)
		return &result
	case *CFnType:
		result := *t
		result.Parameters = sub.applyTypeList(t.Parameters)
		result.ReturnType = sub.Apply(t.ReturnType)
		return &result
	default:
		return t // Unknown type, return as-is
	}
}

// LookupName resolves a human-facing quantified variable name only when exactly
// one binder with that name is present in the substitution. Ambiguous names fail
// closed; substitution identity itself is always the *TypeVar binder pointer.
func (sub Substitution) LookupName(name string) (Type, bool) {
	var result Type
	found := false
	for variable, value := range sub {
		if variable == nil || variable.Name != name {
			continue
		}
		if found {
			return nil, false
		}
		result = value
		found = true
	}
	return result, found
}

// Compose composes two substitutions: sub2 ∘ sub1
func (sub1 Substitution) Compose(sub2 Substitution) Substitution {
	result := make(Substitution)
	// First, apply sub2 to all values in sub1
	for k, v := range sub1 {
		result[k] = sub2.Apply(v)
	}
	// Then add all mappings from sub2 that aren't in sub1
	for k, v := range sub2 {
		if _, exists := sub1[k]; !exists {
			result[k] = v
		}
	}
	return result
}

// Commit composes bindings into this substitution without replacing the map.
// Blocked schemes and their type variables share the same map identity.
func (sub Substitution) Commit(bindings Substitution) {
	composed := sub.Compose(bindings)
	clear(sub)
	for variable, typ := range composed {
		sub[variable] = typ
	}
}

// Generalize converts a type to a type scheme by quantifying over free type variables
// This is used for let-bound variables in HM inference
func Generalize(typ Type, env *TypeEnvironment) *TypeScheme {
	// Aliasing a blocked value cannot re-generalize its persistent variables.
	if persistent := findMonomorphicSubstitution(typ); persistent != nil {
		return makeMonomorphicScheme(typ, nil)
	}

	// Generalize by binder identity, not by printed variable name.
	freeBinders := freeTypeVarBinders(typ, env)
	freeVars := make([]string, 0, len(freeBinders))
	for _, variable := range freeBinders {
		freeVars = append(freeVars, variable.Name)
	}

	// Create constraints for any interface requirements
	// (This will be expanded when we implement interface checking)
	constraints := []Constraint{}

	return &TypeScheme{
		TypeVars:          freeVars,
		QuantifiedBinders: freeBinders,
		Constraints:       constraints,
		Type:              typ,
	}
}

func typeVarsIn(typ Type) []*TypeVar {
	var variables []*TypeVar
	walkTypeVariables(typ, func(variable *TypeVar) bool {
		variables = append(variables, variable)
		return false
	})
	return variables
}

func findMonomorphicSubstitution(typ Type) Substitution {
	var found Substitution
	walkTypeVariables(typ, func(variable *TypeVar) bool {
		if variable.Monomorphic != nil {
			found = variable.Monomorphic
			return true
		}
		return false
	})
	return found
}

func findMonomorphicGroup(typ Type) *monomorphicGroup {
	for _, variable := range typeVarsIn(typ) {
		if variable.monomorphicGroup != nil {
			return variable.monomorphicGroup
		}
	}
	return nil
}

func markMonomorphicTypeVars(typ Type, persistent Substitution, group *monomorphicGroup) {
	walkTypeVariables(typ, func(variable *TypeVar) bool {
		if variable.Monomorphic == nil {
			variable.Monomorphic = persistent
			variable.monomorphicGroup = group
		}
		return false
	})
}

func makeMonomorphicScheme(typ Type, constraints []Constraint) *TypeScheme {
	return makeMonomorphicSchemeFor(typ, constraints, typeVarsIn(typ))
}

func makeMonomorphicSchemeInEnv(typ Type, constraints []Constraint, env *TypeEnvironment) *TypeScheme {
	return makeMonomorphicSchemeFor(typ, constraints, freeTypeVarBinders(typ, env))
}

func makeMonomorphicSchemeFor(typ Type, constraints []Constraint, variables []*TypeVar) *TypeScheme {
	var persistent Substitution
	var group *monomorphicGroup
	for _, variable := range variables {
		if persistent == nil && variable.Monomorphic != nil {
			persistent = variable.Monomorphic
			group = variable.monomorphicGroup
		}
	}
	if len(variables) == 0 {
		return &TypeScheme{
			TypeVars:    []string{},
			Constraints: constraints,
			Type:        typ,
		}
	}
	if persistent == nil {
		persistent = make(Substitution)
	}
	if group == nil {
		group = &monomorphicGroup{}
	}
	for _, variable := range variables {
		if variable.Monomorphic == nil {
			variable.Monomorphic = persistent
			variable.monomorphicGroup = group
		}
	}
	return &TypeScheme{
		TypeVars:    []string{},
		Constraints: constraints,
		Type:        typ,
		Monomorphic: persistent,
	}
}

// findFreeTypeVars finds all type variables in a type that are not bound in the environment
// freeTypeVarBinders implements FV(type) minus FV(environment) by binder
// identity. Variables quantified by an environment scheme are not free in
// that scheme; for legacy explicit schemes, TypeVars names identify only
// that scheme's own quantified variables.
func freeTypeVarBinders(typ Type, env *TypeEnvironment) []*TypeVar {
	bound := make(map[*TypeVar]bool)
	for current := env; current != nil; current = current.outer {
		for _, scheme := range current.store {
			if scheme == nil {
				continue
			}
			quantified := make(map[*TypeVar]bool)
			if len(scheme.QuantifiedBinders) != 0 {
				for _, binder := range scheme.QuantifiedBinders {
					quantified[binder] = true
				}
			} else if len(scheme.TypeVars) != 0 {
				labels := make(map[string]bool, len(scheme.TypeVars))
				for _, label := range scheme.TypeVars {
					labels[label] = true
				}
				for _, binder := range typeVarsIn(scheme.Type) {
					if labels[binder.Name] {
						quantified[binder] = true
					}
				}
			}
			for _, binder := range typeVarsIn(scheme.Type) {
				if !quantified[binder] {
					bound[binder] = true
				}
			}
		}
	}
	var free []*TypeVar
	for _, binder := range typeVarsIn(typ) {
		if !bound[binder] {
			free = append(free, binder)
		}
	}
	return free
}

func findFreeTypeVars(typ Type, env *TypeEnvironment) []string {
	binders := freeTypeVarBinders(typ, env)
	out := make([]string, 0, len(binders))
	for _, binder := range binders {
		out = append(out, binder.Name)
	}
	return out
}

// collectTypeVars collects all type variable names from a type
func collectTypeVars(typ Type) []string {
	var vars []string
	visited := make(map[*TypeVar]bool)
	collectTypeVarsRec(typ, &vars, visited)
	return vars
}

func collectTypeVarsRec(typ Type, vars *[]string, visited map[*TypeVar]bool) {
	walkTypeVariables(typ, func(variable *TypeVar) bool {
		if !visited[variable] {
			visited[variable] = true
			*vars = append(*vars, variable.Name)
		}
		return false
	})
}

// quantifiedSubstitution binds the actual TypeVar identities found in a scheme
// to one fresh/provided replacement per quantified source name. Source names are
// only binder labels here; the resulting substitution is keyed by binder identity.
func quantifiedSubstitution(typ Type, quantified []string, replacements map[string]Type, unifier *Unifier) Substitution {
	wanted := make(map[string]struct{}, len(quantified))
	for _, name := range quantified {
		wanted[name] = struct{}{}
	}

	resolved := make(map[string]Type, len(quantified))
	sub := make(Substitution)
	walkTypeVariables(typ, func(current *TypeVar) bool {
		if _, ok := wanted[current.Name]; !ok {
			return false
		}
		replacement, ok := resolved[current.Name]
		if !ok {
			replacement, ok = replacements[current.Name]
			if !ok {
				replacement = unifier.FreshTypeVar(current.Name)
			}
			resolved[current.Name] = replacement
		}
		sub[current] = replacement
		return false
	})
	return sub
}

// instantiateSchemeSubstitution uses exact binder identities for inferred
// schemes. Explicit generic declarations retain the legacy name-based path
// until their scheme constructors carry explicit binder lists.
func instantiateSchemeSubstitution(scheme *TypeScheme, replacements map[string]Type, unifier *Unifier) Substitution {
	if len(scheme.QuantifiedBinders) == 0 {
		return quantifiedSubstitution(scheme.Type, scheme.TypeVars, replacements, unifier)
	}
	out := make(Substitution, len(scheme.QuantifiedBinders))
	for _, binder := range scheme.QuantifiedBinders {
		replacement, ok := replacements[binder.Name]
		if !ok {
			replacement = unifier.FreshTypeVar(binder.Name)
		}
		out[binder] = replacement
	}
	return out
}

// Instantiate creates a fresh instance of a type scheme by replacing
// quantified type variables with fresh type variables
// For qualified types (with constraints), constraints are checked but not enforced here
// (They will be checked when the instantiated type is actually used)
func Instantiate(scheme *TypeScheme, unifier *Unifier) Type {
	if scheme.Monomorphic != nil {
		return scheme.Monomorphic.Apply(scheme.Type)
	}
	if len(scheme.TypeVars) == 0 && len(scheme.Constraints) == 0 {
		return scheme.Type
	}

	// Bind the quantified variables by their actual binder identities.
	sub := instantiateSchemeSubstitution(scheme, nil, unifier)
	return sub.Apply(scheme.Type)
}

// InstantiateWithConstraints instantiates a type scheme and checks interface constraints
// This is used when instantiating polymorphic functions with explicit type arguments
// that must satisfy interface constraints
func InstantiateWithConstraints(scheme *TypeScheme, typeArgs map[string]Type, unifier *Unifier, tc *TypeChecker) (Type, bool) {
	// Check that all constraints are satisfied
	for _, constraint := range scheme.Constraints {
		concreteType, ok := typeArgs[constraint.Var]
		if !ok {
			// Type variable not provided - this shouldn't happen in well-formed code
			tc.addError(nil, "type variable %s not provided for constraint", constraint.Var)
			return nil, false
		}

		if !tc.SatisfiesConstraint(concreteType, constraint) {
			tc.addError(nil, "type %s does not satisfy constraint: %s", concreteType, constraint)
			return nil, false
		}
	}

	// Bind provided arguments (and freshen any remaining quantified binders)
	// using the scheme's actual TypeVar identities.
	sub := instantiateSchemeSubstitution(scheme, typeArgs, unifier)
	return sub.Apply(scheme.Type), true
}
