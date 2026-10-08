package typechecker

import "testing"

func TestGeneralizeUsesBinderIdentityAcrossSameNames(t *testing.T) {
	env := NewTypeEnvironment()
	outer := &TypeVar{Name: "T"}
	env.SetType("outer", outer)
	local := &TypeVar{Name: "T"}
	scheme := Generalize(&FunctionType{Parameters: []Type{outer, local}, ReturnType: local}, env)
	if len(scheme.QuantifiedBinders) != 1 || scheme.QuantifiedBinders[0] != local {
		t.Fatalf("generalized wrong binder: %#v", scheme.QuantifiedBinders)
	}
	first := Instantiate(scheme, NewUnifier()).(*FunctionType)
	second := Instantiate(scheme, NewUnifier()).(*FunctionType)
	if first.Parameters[0] != outer || second.Parameters[0] != outer {
		t.Fatal("environment free variable was freshened")
	}
	if first.Parameters[1] == local || second.Parameters[1] == local || first.Parameters[1] == second.Parameters[1] {
		t.Fatal("local quantified binder was not freshened independently")
	}
}

func TestGeneralizeDoesNotTreatEnvironmentQuantifierAsFree(t *testing.T) {
	env := NewTypeEnvironment()
	quantified := &TypeVar{Name: "T"}
	env.Set("polymorphic", Generalize(quantified, nil))
	if got := Generalize(quantified, env); len(got.QuantifiedBinders) != 1 || got.QuantifiedBinders[0] != quantified {
		t.Fatal("environment quantified binder incorrectly blocked generalization")
	}
}

func TestGeneralizeDistinctBindersWithSameLabel(t *testing.T) {
	a, b := &TypeVar{Name: "T"}, &TypeVar{Name: "T"}
	scheme := Generalize(&FunctionType{Parameters: []Type{a, b}, ReturnType: a}, nil)
	if len(scheme.QuantifiedBinders) != 2 {
		t.Fatalf("expected two distinct quantified binders: %d", len(scheme.QuantifiedBinders))
	}
	inst := Instantiate(scheme, NewUnifier()).(*FunctionType)
	if inst.Parameters[0] == inst.Parameters[1] || inst.Parameters[0] != inst.ReturnType {
		t.Fatal("independent same-label binders collapsed during instantiation")
	}
}

func TestBlockedGeneralizationSameNamePreservesEnvironmentVariable(t *testing.T) {
	env := NewTypeEnvironment()
	outer, local := &TypeVar{Name: "T"}, &TypeVar{Name: "T"}
	env.SetType("outer", outer)
	scheme := GeneralizeWithFacts(&FunctionType{Parameters: []Type{outer, local}, ReturnType: local}, env, GeneralizationFacts{Barriers: GeneralizationMutableAuthority})
	if scheme.Monomorphic == nil || outer.Monomorphic != nil || local.Monomorphic == nil {
		t.Fatal("blocked generalization incorrectly marked an environment binder")
	}
}
