package typechecker

import "fmt"

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
// that makes them equal, or nil if unification fails. It does not mutate
// persistent scheme state: the enclosing successful use commits the complete
// accumulated substitution transactionally.
func (u *Unifier) Unify(t1, t2 Type) Substitution {
	// Resolve solutions learned by earlier uses before solving this equation.
	empty := make(Substitution)
	t1 = empty.Apply(t1)
	t2 = empty.Apply(t2)

	// Record admission must precede compatibility's equality shortcut.
	// Equals is intentionally broader than nominal identity, and its empty
	// record cases do not enforce row openness. Unit must enter through its
	// closed empty record view in either operand position, not that shortcut.
	if left, ok := recordUnificationView(t1); ok {
		if right, ok := recordUnificationView(t2); ok {
			return u.unifyRecord(left, right)
		}
	}

	// Handle type variables
	if tv1, ok := t1.(*TypeVar); ok {
		if tv1 == t2 {
			return make(Substitution)
		}
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

	// Remaining leaf compatibility is unchanged. Record/Unit admission and
	// supported composite child equations have already been checked above.
	if t1.Equals(t2) {
		return make(Substitution)
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
	return walkTypeVariables(t, func(variable *TypeVar) bool { return variable == tv })
}

func (u *Unifier) unifyFunction(fn1, fn2 *FunctionType) Substitution {
	if fn1.Variadic != fn2.Variadic {
		u.errors = append(u.errors, "cannot unify variadic and fixed-arity functions")
		return nil
	}
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
	if !recordUnificationAdmissible(rec1, rec2) {
		u.errors = append(u.errors, fmt.Sprintf("incompatible record boundaries: %s and %s", rec1, rec2))
		return nil
	}
	if rec1.Struct && rec1.Name != "" && rec2.Struct && rec1.Name == rec2.Name {
		return make(Substitution)
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

	// Unification is structural: the alignment fact's direction is
	// assignability's business (ArrayType.alignedInto), never inference's.
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
