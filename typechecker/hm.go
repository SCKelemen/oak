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
	// Constraints: interface requirements (e.g., "T: Reader & Writer")
	// These are checked at instantiation time
	Constraints []Constraint
	// The underlying type (τ)
	Type Type
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

// TypeVar represents a type variable (α, β, γ, ...)
// Used during type inference
type TypeVar struct {
	Name string // e.g., "α", "β", or "T", "U"
	ID   int    // Unique identifier for fresh type variables
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
			return replacement
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
		// IsSpan must survive substitution: dropping it silently strips
		// write authority from span-typed bindings (docs/spec/50-borrowing).
		return &ArrayType{
			Length:      t.Length,
			IsSlice:     t.IsSlice,
			IsSpan:      t.IsSpan,
			ElementType: sub.Apply(t.ElementType),
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

// Unifier performs unification of types
type Unifier struct {
	nextVarID int
	errors    []string
}

func NewUnifier() *Unifier {
	return &Unifier{
		nextVarID: 0,
		errors:    []string{},
	}
}

func (u *Unifier) Errors() []string {
	return u.errors
}

// FreshTypeVar creates a fresh type variable
func (u *Unifier) FreshTypeVar(name string) *TypeVar {
	tv := &TypeVar{
		Name: name,
		ID:   u.nextVarID,
	}
	u.nextVarID++
	return tv
}

// Unify attempts to unify two types, returning a substitution
// that makes them equal, or nil if unification fails
func (u *Unifier) Unify(t1, t2 Type) Substitution {
	// If types are equal, no substitution needed
	if t1.Equals(t2) {
		return make(Substitution)
	}

	// Handle type variables
	if tv1, ok := t1.(*TypeVar); ok {
		return u.unifyVar(tv1, t2)
	}
	if tv2, ok := t2.(*TypeVar); ok {
		return u.unifyVar(tv2, t1)
	}

	// Handle function types
	if fn1, ok := t1.(*FunctionType); ok {
		if fn2, ok := t2.(*FunctionType); ok {
			return u.unifyFunction(fn1, fn2)
		}
	}

	// Handle record types
	if rec1, ok := t1.(*RecordType); ok {
		if rec2, ok := t2.(*RecordType); ok {
			return u.unifyRecord(rec1, rec2)
		}
	}

	// Handle array types
	if arr1, ok := t1.(*ArrayType); ok {
		if arr2, ok := t2.(*ArrayType); ok {
			return u.unifyArray(arr1, arr2)
		}
	}

	// Handle generic types
	if gen1, ok := t1.(*GenericType); ok {
		if gen2, ok := t2.(*GenericType); ok {
			return u.unifyGeneric(gen1, gen2)
		}
	}

	// Types cannot be unified
	u.errors = append(u.errors, fmt.Sprintf("cannot unify %s with %s", t1, t2))
	return nil
}

func (u *Unifier) unifyVar(tv *TypeVar, t Type) Substitution {
	// Check for occurs check: if tv appears in t, we have a circular constraint
	if u.occursIn(tv, t) {
		u.errors = append(u.errors, fmt.Sprintf("circular type constraint: %s occurs in %s", tv, t))
		return nil
	}

	// Create substitution: tv ↦ t
	sub := make(Substitution)
	sub[tv] = t
	return sub
}

func (u *Unifier) occursIn(tv *TypeVar, t Type) bool {
	switch typ := t.(type) {
	case *TypeVar:
		return tv == typ
	case *RecordType:
		for _, fieldType := range typ.Fields {
			if u.occursIn(tv, fieldType) {
				return true
			}
		}
	case *FunctionType:
		for _, param := range typ.Parameters {
			if u.occursIn(tv, param) {
				return true
			}
		}
		if u.occursIn(tv, typ.ReturnType) {
			return true
		}
	case *ArrayType:
		return u.occursIn(tv, typ.ElementType)
	case *GenericType:
		for _, arg := range typ.TypeArgs {
			if u.occursIn(tv, arg) {
				return true
			}
		}
	}
	return false
}

func (u *Unifier) unifyFunction(fn1, fn2 *FunctionType) Substitution {
	if len(fn1.Parameters) != len(fn2.Parameters) {
		u.errors = append(u.errors, fmt.Sprintf("function arity mismatch: %d vs %d", len(fn1.Parameters), len(fn2.Parameters)))
		return nil
	}

	sub := make(Substitution)

	// Each equation is solved under all bindings learned from earlier
	// parameters. This preserves repeated-variable consistency without mutating
	// either input function type.
	for i := 0; i < len(fn1.Parameters); i++ {
		paramSub := u.Unify(sub.Apply(fn1.Parameters[i]), sub.Apply(fn2.Parameters[i]))
		if paramSub == nil {
			return nil
		}
		sub = sub.Compose(paramSub)
	}

	// The result equation sees the same accumulated substitution.
	retSub := u.Unify(sub.Apply(fn1.ReturnType), sub.Apply(fn2.ReturnType))
	if retSub == nil {
		return nil
	}

	return sub.Compose(retSub)
}

func (u *Unifier) unifyRecord(rec1, rec2 *RecordType) Substitution {
	// Declared STRUCTS are nominal: two named struct types unify only by
	// name (Idx[Thread] never unifies with Idx[Timer], whatever the
	// shape). Semantic record types stay structural shapes — a struct
	// satisfies a record shape whatever its field order.
	if rec1.Name != "" && rec2.Name != "" && rec1.Struct && rec2.Struct && rec1.Name != rec2.Name {
		u.errors = append(u.errors, fmt.Sprintf("distinct record types %s and %s", rec1.Name, rec2.Name))
		return nil
	}
	if len(rec1.Fields) != len(rec2.Fields) {
		u.errors = append(u.errors, fmt.Sprintf("record field count mismatch: %d vs %d", len(rec1.Fields), len(rec2.Fields)))
		return nil
	}

	sub := make(Substitution)

	for name, field1 := range rec1.Fields {
		field2, ok := rec2.Fields[name]
		if !ok {
			u.errors = append(u.errors, fmt.Sprintf("record field %s missing in second record", name))
			return nil
		}

		fieldSub := u.Unify(sub.Apply(field1), sub.Apply(field2))
		if fieldSub == nil {
			return nil
		}
		sub = sub.Compose(fieldSub)
	}

	return sub
}

func (u *Unifier) unifyArray(arr1, arr2 *ArrayType) Substitution {
	if arr1.IsSlice != arr2.IsSlice {
		u.errors = append(u.errors, "cannot unify array with slice")
		return nil
	}

	// A writable span never unifies with a read-only view or an owned
	// array: write authority is part of the type (docs/spec/50-borrowing).
	if arr1.IsSpan != arr2.IsSpan {
		u.errors = append(u.errors, "cannot unify span with non-span")
		return nil
	}

	if !arr1.IsSlice && !arr1.IsSpan && arr1.Length != arr2.Length {
		u.errors = append(u.errors, fmt.Sprintf("array length mismatch: %d vs %d", arr1.Length, arr2.Length))
		return nil
	}

	return u.Unify(arr1.ElementType, arr2.ElementType)
}

func (u *Unifier) unifyGeneric(gen1, gen2 *GenericType) Substitution {
	if gen1.Name != gen2.Name {
		u.errors = append(u.errors, fmt.Sprintf("generic type name mismatch: %s vs %s", gen1.Name, gen2.Name))
		return nil
	}

	if len(gen1.TypeArgs) != len(gen2.TypeArgs) {
		u.errors = append(u.errors, fmt.Sprintf("generic type argument count mismatch: %d vs %d", len(gen1.TypeArgs), len(gen2.TypeArgs)))
		return nil
	}

	sub := make(Substitution)

	for i := 0; i < len(gen1.TypeArgs); i++ {
		argSub := u.Unify(sub.Apply(gen1.TypeArgs[i]), sub.Apply(gen2.TypeArgs[i]))
		if argSub == nil {
			return nil
		}
		sub = sub.Compose(argSub)
	}

	return sub
}

// Generalize converts a type to a type scheme by quantifying over free type variables
// This is used for let-bound variables in HM inference
func Generalize(typ Type, env *TypeEnvironment) *TypeScheme {
	// Find all free type variables in typ that are not bound in env
	freeVars := findFreeTypeVars(typ, env)

	// Create constraints for any interface requirements
	// (This will be expanded when we implement interface checking)
	constraints := []Constraint{}

	return &TypeScheme{
		TypeVars:    freeVars,
		Constraints: constraints,
		Type:        typ,
	}
}

// findFreeTypeVars finds all type variables in a type that are not bound in the environment
func findFreeTypeVars(typ Type, env *TypeEnvironment) []string {
	// Collect all type variables in the type
	vars := collectTypeVars(typ)

	// Extract bound type variables from environment schemes
	boundVars := extractBoundTypeVars(env)

	freeVars := []string{}
	for _, v := range vars {
		if !boundVars[v] {
			freeVars = append(freeVars, v)
		}
	}

	return freeVars
}

// extractBoundTypeVars extracts all bound type variables from the environment
// This includes type variables from all schemes in the current and outer environments
func extractBoundTypeVars(env *TypeEnvironment) map[string]bool {
	boundVars := make(map[string]bool)

	// Traverse the environment chain (current and outer environments)
	currentEnv := env
	for currentEnv != nil {
		// Extract type variables from all schemes in this environment
		for _, scheme := range currentEnv.store {
			if scheme != nil {
				for _, tv := range scheme.TypeVars {
					boundVars[tv] = true
				}
			}
		}
		currentEnv = currentEnv.outer
	}

	return boundVars
}

// collectTypeVars collects all type variable names from a type
func collectTypeVars(typ Type) []string {
	var vars []string
	visited := make(map[*TypeVar]bool)
	collectTypeVarsRec(typ, &vars, visited)
	return vars
}

func collectTypeVarsRec(typ Type, vars *[]string, visited map[*TypeVar]bool) {
	switch t := typ.(type) {
	case *TypeVar:
		if !visited[t] {
			visited[t] = true
			*vars = append(*vars, t.Name)
		}
	case *RecordType:
		for _, fieldType := range t.Fields {
			collectTypeVarsRec(fieldType, vars, visited)
		}
	case *FunctionType:
		for _, param := range t.Parameters {
			collectTypeVarsRec(param, vars, visited)
		}
		collectTypeVarsRec(t.ReturnType, vars, visited)
	case *ArrayType:
		collectTypeVarsRec(t.ElementType, vars, visited)
	case *GenericType:
		for _, arg := range t.TypeArgs {
			collectTypeVarsRec(arg, vars, visited)
		}
	}
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
	var visit func(Type)
	visit = func(current Type) {
		switch current := current.(type) {
		case *TypeVar:
			if _, ok := wanted[current.Name]; !ok {
				return
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
		case *RecordType:
			for _, field := range current.Fields {
				visit(field)
			}
		case *FunctionType:
			for _, parameter := range current.Parameters {
				visit(parameter)
			}
			visit(current.ReturnType)
		case *ArrayType:
			visit(current.ElementType)
		case *GenericType:
			for _, argument := range current.TypeArgs {
				visit(argument)
			}
		}
	}
	visit(typ)
	return sub
}

// Instantiate creates a fresh instance of a type scheme by replacing
// quantified type variables with fresh type variables
// For qualified types (with constraints), constraints are checked but not enforced here
// (They will be checked when the instantiated type is actually used)
func Instantiate(scheme *TypeScheme, unifier *Unifier) Type {
	if len(scheme.TypeVars) == 0 && len(scheme.Constraints) == 0 {
		return scheme.Type
	}

	// Bind the quantified variables by their actual binder identities.
	sub := quantifiedSubstitution(scheme.Type, scheme.TypeVars, nil, unifier)
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
	sub := quantifiedSubstitution(scheme.Type, scheme.TypeVars, typeArgs, unifier)
	return sub.Apply(scheme.Type), true
}
