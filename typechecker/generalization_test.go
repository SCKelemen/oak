package typechecker

import (
	"reflect"
	"testing"
)

func polymorphicIdentityType() Type {
	v := NewUnifier().FreshTypeVar("T")
	return &FunctionType{Parameters: []Type{v}, ReturnType: v}
}

func TestGeneralizeWithFactsGeneralizesSafeBinding(t *testing.T) {
	typ := polymorphicIdentityType()
	scheme := GeneralizeWithFacts(typ, NewTypeEnvironment(), GeneralizationFacts{})

	if len(scheme.TypeVars) != 1 || scheme.TypeVars[0] != "T" {
		t.Fatalf("expected one quantified T, got %#v", scheme.TypeVars)
	}
	if scheme.Type != typ {
		t.Fatal("generalization changed the underlying inferred type")
	}
}

func TestGeneralizeWithFactsKeepsUnsafeBindingsMonomorphic(t *testing.T) {
	barriers := []GeneralizationBarrier{
		GeneralizationMutableAuthority,
		GeneralizationUniqueAuthority,
		GeneralizationRegionBound,
		GeneralizationExternalAuthority,
		GeneralizationEffectfulCapture,
		GeneralizationUnsafeAssumption,
		GeneralizationUnknownAuthority,
	}

	for _, barrier := range barriers {
		t.Run(GeneralizationFacts{Barriers: barrier}.String(), func(t *testing.T) {
			typ := polymorphicIdentityType()
			scheme := GeneralizeWithFacts(typ, NewTypeEnvironment(), GeneralizationFacts{Barriers: barrier})
			if len(scheme.TypeVars) != 0 {
				t.Fatalf("barrier %v unexpectedly generalized to %#v", barrier, scheme.TypeVars)
			}
			if scheme.Type != typ {
				t.Fatal("blocked generalization changed the inferred monotype")
			}
		})
	}
}

func TestGeneralizationFactsComposeMonotonically(t *testing.T) {
	facts := GeneralizationFacts{}.
		With(GeneralizationRegionBound).
		With(GeneralizationUniqueAuthority)

	if facts.Safe() {
		t.Fatal("barriers must not become safe by composition")
	}
	if !facts.Has(GeneralizationRegionBound) || !facts.Has(GeneralizationUniqueAuthority) {
		t.Fatalf("composed facts lost a barrier: %#v", facts)
	}
}

func TestGeneralizationReasonsAreStableAndOrthogonal(t *testing.T) {
	facts := GeneralizationFacts{}.
		With(GeneralizationMutableAuthority).
		With(GeneralizationRegionBound).
		With(GeneralizationUnsafeAssumption)

	want := []string{"mutable authority", "region-bound value", "unsafe assumption"}
	if got := facts.Reasons(); !reflect.DeepEqual(got, want) {
		t.Fatalf("reasons = %#v, want %#v", got, want)
	}
}

func TestBlockedGeneralizationDoesNotAffectTypeInference(t *testing.T) {
	v := NewUnifier().FreshTypeVar("T")
	typ := &GenericType{Name: "Box", TypeArgs: []Type{v}}
	facts := GeneralizationFacts{Barriers: GeneralizationExternalAuthority}

	scheme := GeneralizeWithFacts(typ, NewTypeEnvironment(), facts)
	if scheme.Type != typ {
		t.Fatal("generalization policy must not rewrite the inferred semantic type")
	}
	if len(scheme.TypeVars) != 0 {
		t.Fatalf("unsafe binding must remain monomorphic, got %#v", scheme.TypeVars)
	}
}
