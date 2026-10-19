package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

func TestMatchCatchAllAfterCompleteBoolIsRedundant(t *testing.T) {
	tc := patternAnalysisChecker()
	match := &ast.MatchExpression{Arms: []*ast.MatchArm{
		arm(boolPattern(false)),
		arm(boolPattern(true)),
		arm(wildcardPattern()),
	}}
	result := tc.analyzeMatch(match, &BoolType{})
	if !result.Reliable || len(result.Missing) != 0 {
		t.Fatalf("complete Bool coverage: %#v", result)
	}
	if !result.Arms[2].Redundant || result.Arms[2].Reachable || result.Arms[2].Impossible {
		t.Fatalf("catch-all must be redundant after complete coverage: %#v", result.Arms[2])
	}
}

func TestMatchNestedCatchAllAfterCompletePayloadIsRedundant(t *testing.T) {
	tc := patternAnalysisChecker()
	match := &ast.MatchExpression{Arms: []*ast.MatchArm{
		arm(variantPattern("Some", boolPattern(false))),
		arm(variantPattern("Some", boolPattern(true))),
		arm(variantPattern("Some", wildcardPattern())),
		arm(variantPattern("None", nil)),
	}}
	result := tc.analyzeMatch(match, &ADTType{Name: "OptionBool"})
	if !result.Reliable || len(result.Missing) != 0 {
		t.Fatalf("complete OptionBool coverage: %#v", result)
	}
	if !result.Arms[2].Redundant || result.Arms[2].Reachable {
		t.Fatalf("nested catch-all adds no semantic case: %#v", result.Arms[2])
	}
}

func TestMatchCatchAllOverEmptyADTIsImpossible(t *testing.T) {
	tc := patternAnalysisChecker()
	match := &ast.MatchExpression{Arms: []*ast.MatchArm{arm(wildcardPattern())}}
	result := tc.analyzeMatch(match, &ADTType{Name: "Void"})
	if !result.Reliable || len(result.Missing) != 0 {
		t.Fatalf("empty ADT is vacuously complete: %#v", result)
	}
	if !result.Arms[0].Impossible || result.Arms[0].Reachable || result.Arms[0].Redundant {
		t.Fatalf("catch-all cannot run on an uninhabited type: %#v", result.Arms[0])
	}
}

func TestMatchConstructorWithEmptyPayloadIsImpossible(t *testing.T) {
	tc := patternAnalysisChecker()
	tc.adtTypes["OnlyVoid"] = &object.ADTType{
		Name: "OnlyVoid",
		Variants: []*object.ADTVariantDef{{Name: "Wrap", Payload: "Void"}},
	}
	match := &ast.MatchExpression{Arms: []*ast.MatchArm{
		arm(variantPattern("Wrap", wildcardPattern())),
	}}
	result := tc.analyzeMatch(match, &ADTType{Name: "OnlyVoid"})
	if !result.Reliable || len(result.Missing) != 0 {
		t.Fatalf("uninhabited payload must not generate counterexamples: %#v", result)
	}
	if !result.Arms[0].Impossible || result.Arms[0].Reachable {
		t.Fatalf("constructor with impossible payload must be unreachable: %#v", result.Arms[0])
	}
}

func TestMatchOpenScalarStillNeedsCatchAll(t *testing.T) {
	tc := patternAnalysisChecker()
	match := &ast.MatchExpression{Arms: []*ast.MatchArm{
		arm(&ast.LiteralPattern{Value: &ast.IntegerLiteral{Value: 1}}),
		arm(wildcardPattern()),
	}}
	result := tc.analyzeMatch(match, &PrimitiveType{Name: "i32"})
	if !result.Reliable || len(result.Missing) != 0 || !result.Arms[1].Reachable {
		t.Fatalf("integer domain must remain open: %#v", result)
	}
}
