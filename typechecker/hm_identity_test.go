package typechecker

import "testing"

func TestFreshTypeVarsFromDifferentUnifiersAreDistinct(t *testing.T) {
	left := NewUnifier().FreshTypeVar("T")
	right := NewUnifier().FreshTypeVar("T")
	if left.Equals(right) {
		t.Fatal("unrelated type variables with the same display name must not be equal")
	}
}

func TestSubstitutionIsKeyedByBinderIdentityNotDisplayName(t *testing.T) {
	left := NewUnifier().FreshTypeVar("T")
	right := NewUnifier().FreshTypeVar("T")
	sub := make(Substitution)
	sub[left] = &PrimitiveType{Name: "i32"}
	if got := sub.Apply(left); !got.Equals(&PrimitiveType{Name: "i32"}) {
		t.Fatalf("expected left binder to substitute to i32, got %s", got)
	}
	if got := sub.Apply(right); got != right {
		t.Fatalf("substitution for unrelated T leaked across binder identity: got %s", got)
	}
}

func TestOccursCheckUsesBinderIdentity(t *testing.T) {
	leftUnifier := NewUnifier()
	rightUnifier := NewUnifier()
	left := leftUnifier.FreshTypeVar("T")
	right := rightUnifier.FreshTypeVar("T")
	if leftUnifier.occursIn(left, right) {
		t.Fatal("occurs check confused unrelated binders with the same display name")
	}
	cyclic := &GenericType{Name: "Box", TypeArgs: []Type{left}}
	if !leftUnifier.occursIn(left, cyclic) {
		t.Fatal("occurs check failed to find the same binder through a generic type")
	}
}

func TestInstantiateFreshensSameNamedSchemeOnEveryUse(t *testing.T) {
	binder := NewUnifier().FreshTypeVar("T")
	scheme := &TypeScheme{
		TypeVars: []string{"T"},
		Type:     &FunctionType{Parameters: []Type{binder}, ReturnType: binder},
	}
	first := Instantiate(scheme, NewUnifier()).(*FunctionType)
	second := Instantiate(scheme, NewUnifier()).(*FunctionType)
	firstVar := first.Parameters[0].(*TypeVar)
	secondVar := second.Parameters[0].(*TypeVar)
	if firstVar.Equals(secondVar) {
		t.Fatal("independent instantiations reused one type-variable identity")
	}
	if first.ReturnType != firstVar || second.ReturnType != secondVar {
		t.Fatal("instantiation did not preserve repeated binder identity")
	}
}

func TestNamedLookupRejectsAmbiguousIndependentBinders(t *testing.T) {
	left := NewUnifier().FreshTypeVar("T")
	right := NewUnifier().FreshTypeVar("T")
	sub := make(Substitution)
	sub[left] = &PrimitiveType{Name: "i32"}
	sub[right] = &PrimitiveType{Name: "u32"}
	if _, ok := sub.LookupName("T"); ok {
		t.Fatal("name lookup must fail closed when independent binders share a display name")
	}
}
