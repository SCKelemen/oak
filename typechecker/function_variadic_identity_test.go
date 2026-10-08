package typechecker

import "testing"

// A variadic function and a fixed-arity function differ in calling behavior,
// even when their last parameter has the same slice representation.
func TestFunctionTypeVariadicIdentity(t *testing.T) {
	elt := &PrimitiveType{Name: "u8"}
	view := &ArrayType{ElementType: elt, IsSlice: true}
	fixed := &FunctionType{Parameters: []Type{view}, ReturnType: &UnitType{}}
	variadic := &FunctionType{Parameters: []Type{view}, ReturnType: &UnitType{}, Variadic: true}
	if fixed.Equals(variadic) || variadic.Equals(fixed) {
		t.Fatal("fixed and variadic signatures must not be equal")
	}
	if sub := NewUnifier().Unify(fixed, variadic); sub != nil {
		t.Fatal("fixed and variadic signatures incorrectly unify")
	}
	for _, same := range []*FunctionType{fixed, variadic} {
		if !same.Equals(same) || NewUnifier().Unify(same, same) == nil {
			t.Fatal("identical function signature did not unify")
		}
	}
}
