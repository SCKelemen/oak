package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

func TestVariantPatternBinderCarriesInstantiatedPayloadAuthority(t *testing.T) {
	tc := New(object.NewEnvironment())
	tc.adtTypes["Box"] = &object.ADTType{
		Name:       "Box",
		TypeParams: []string{"T"},
		Variants: []*object.ADTVariantDef{{
			Name:          "Hold",
			Payload:       "T",
			ResultName:    "Box",
			ResultIndices: []string{"T"},
		}},
	}
	tc.adtPayloadTypes["Box"] = map[string]Type{
		"Hold": &ADTType{Name: "T"},
	}
	pattern := &ast.VariantPattern{
		Variant: &ast.Identifier{Value: "Hold"},
		Payload: &ast.BindingPattern{Name: &ast.Identifier{Value: "payload"}},
	}
	owned := &ArrayType{
		Length:      2,
		ElementType: &PrimitiveType{Name: "i32"},
	}
	facts := tc.generalizationPatternBindingFacts(pattern, &GenericType{
		Name:     "Box",
		TypeArgs: []Type{owned},
	})["payload"]
	if !facts.Has(GeneralizationMutableAuthority) || !facts.Has(GeneralizationUniqueAuthority) {
		t.Fatalf("payload facts = %v, want mutable and unique authority", facts)
	}
}


func TestWholeADTBindingCarriesReachablePayloadAuthority(t *testing.T) {
	tc := New(object.NewEnvironment())
	tc.adtTypes["Carrier"] = &object.ADTType{
		Name: "Carrier",
		Variants: []*object.ADTVariantDef{{
			Name:       "Owned",
			Payload:    "[2]i32",
			ResultName: "Carrier",
		}},
	}
	tc.adtPayloadTypes["Carrier"] = map[string]Type{
		"Owned": &ArrayType{
			Length:      2,
			ElementType: &PrimitiveType{Name: "i32"},
		},
	}
	pattern := &ast.BindingPattern{Name: &ast.Identifier{Value: "whole"}}
	facts := tc.generalizationPatternBindingFacts(
		pattern,
		&ADTType{Name: "Carrier"},
	)["whole"]
	if !facts.Has(GeneralizationMutableAuthority) || !facts.Has(GeneralizationUniqueAuthority) {
		t.Fatalf("whole ADT facts = %v, want mutable and unique authority", facts)
	}
}


func TestExpandingRecursiveADTAuthorityTraversalTerminates(t *testing.T) {
	tc := New(object.NewEnvironment())
	tc.adtTypes["Nest"] = &object.ADTType{
		Name:       "Nest",
		TypeParams: []string{"T"},
		Variants: []*object.ADTVariantDef{
			{
				Name:          "Next",
				Payload:       "Nest[[]T]",
				ResultName:    "Nest",
				ResultIndices: []string{"T"},
			},
			{
				Name:          "Stop",
				ResultName:    "Nest",
				ResultIndices: []string{"T"},
			},
		},
	}
	tc.adtPayloadTypes["Nest"] = map[string]Type{
		"Next": &GenericType{
			Name: "Nest",
			TypeArgs: []Type{&ArrayType{
				Length: -1, IsSlice: true,
				ElementType: &ADTType{Name: "T"},
			}},
		},
	}
	facts := tc.valueAuthorityFacts(&GenericType{
		Name: "Nest",
		TypeArgs: []Type{&PrimitiveType{Name: "i32"}},
	}, make(map[string]bool))
	if !facts.Has(GeneralizationRegionBound) {
		t.Fatalf("recursive ADT facts = %v, want nested view authority", facts)
	}
}


func TestIndexedStoreCreatesCaptureBarrier(t *testing.T) {
	env := NewTypeEnvironment()
	env.Set("values", &TypeScheme{Type: &ArrayType{
		Length: 2,
		ElementType: &PrimitiveType{Name: "i32"},
	}})
	fn := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "write"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{
			Statements: []ast.Statement{&ast.IndexAssignmentStatement{
				Target: &ast.IndexExpression{
					Left:  &ast.Identifier{Value: "values"},
					Index: &ast.IntegerLiteral{Value: 0},
				},
				Value: &ast.IntegerLiteral{Value: 1},
			}},
		}},
	}
	facts := functionStatementCaptureFacts(fn, env)
	want := GeneralizationMutableAuthority | GeneralizationEffectfulCapture
	if facts.Barriers&want != want {
		t.Fatalf("indexed-store barriers = %v, want mutable and effectful capture", facts.Barriers)
	}
}
