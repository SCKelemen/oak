package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/object"
)

func patternAnalysisChecker() *TypeChecker {
	env := object.NewEnvironment()
	env.SetADTType("OptionBool", &object.ADTType{
		Name: "OptionBool",
		Variants: []*object.ADTVariantDef{
			{Name: "Some", Payload: "Bool"},
			{Name: "None"},
		},
	})
	env.SetADTType("Inner", &object.ADTType{
		Name: "Inner",
		Variants: []*object.ADTVariantDef{
			{Name: "A"},
			{Name: "B"},
		},
	})
	env.SetADTType("Outer", &object.ADTType{
		Name: "Outer",
		Variants: []*object.ADTVariantDef{
			{Name: "Wrap", Payload: "Inner"},
			{Name: "Empty"},
		},
	})
	return New(env)
}

func variantPattern(name string, payload ast.Pattern) *ast.VariantPattern {
	return &ast.VariantPattern{
		Variant: &ast.Identifier{Value: name},
		Payload: payload,
	}
}

func boolPattern(value bool) *ast.LiteralPattern {
	return &ast.LiteralPattern{Value: &ast.Boolean{Value: value}}
}

func wildcardPattern() *ast.WildcardPattern { return &ast.WildcardPattern{} }

func arm(pattern ast.Pattern) *ast.MatchArm {
	return &ast.MatchArm{Pattern: pattern, Body: &ast.IntegerLiteral{Value: 0}}
}

func TestPatternAnalysisProducesNestedCounterexample(t *testing.T) {
	tc := patternAnalysisChecker()
	expr := &ast.MatchExpression{
		Scrutinee: &ast.Identifier{Value: "x"},
		Arms: []*ast.MatchArm{
			arm(variantPattern("Some", boolPattern(true))),
			arm(variantPattern("None", nil)),
		},
	}

	analysis := tc.analyzeMatch(expr, &ADTType{Name: "OptionBool"})
	if len(analysis.Missing) != 1 || analysis.Missing[0] != ".Some(false)" {
		t.Fatalf("missing = %#v, want [.Some(false)]", analysis.Missing)
	}
	if got := analysis.Arms[0].Refinements; len(got) != 1 || got[0].Subject != "x" || got[0].Constructor != "Some" {
		t.Fatalf("refinements = %#v", got)
	}
}

func TestPatternAnalysisNestedADTCanBecomeExhaustive(t *testing.T) {
	tc := patternAnalysisChecker()
	expr := &ast.MatchExpression{Arms: []*ast.MatchArm{
		arm(variantPattern("Wrap", variantPattern("A", nil))),
		arm(variantPattern("Wrap", variantPattern("B", nil))),
		arm(variantPattern("Empty", nil)),
	}}

	analysis := tc.analyzeMatch(expr, &ADTType{Name: "Outer"})
	if len(analysis.Missing) != 0 {
		t.Fatalf("unexpected missing cases: %#v", analysis.Missing)
	}
	for i, state := range analysis.Arms {
		if !state.Reachable {
			t.Fatalf("arm %d unexpectedly unreachable: %#v", i, state)
		}
	}
}

func TestPatternAnalysisDetectsRedundantArm(t *testing.T) {
	tc := patternAnalysisChecker()
	expr := &ast.MatchExpression{Arms: []*ast.MatchArm{
		arm(variantPattern("Some", wildcardPattern())),
		arm(variantPattern("Some", boolPattern(true))),
		arm(variantPattern("None", nil)),
	}}

	analysis := tc.analyzeMatch(expr, &ADTType{Name: "OptionBool"})
	if !analysis.Arms[1].Redundant || analysis.Arms[1].Reachable {
		t.Fatalf("second arm should be redundant: %#v", analysis.Arms[1])
	}
	if len(analysis.Missing) != 0 {
		t.Fatalf("unexpected missing cases: %#v", analysis.Missing)
	}
}

func TestPatternAnalysisUsesRefinedConstructorUniverse(t *testing.T) {
	tc := patternAnalysisChecker()
	expr := &ast.MatchExpression{Arms: []*ast.MatchArm{
		arm(variantPattern("None", nil)),
		arm(variantPattern("Some", wildcardPattern())),
	}}

	analysis := tc.analyzeMatch(expr, &NarrowedADTVariantType{ADTName: "OptionBool", VariantName: "Some"})
	if !analysis.Arms[0].Impossible || analysis.Arms[0].Reachable {
		t.Fatalf("None arm should be impossible after Some refinement: %#v", analysis.Arms[0])
	}
	if !analysis.Arms[1].Reachable {
		t.Fatalf("Some arm should remain reachable: %#v", analysis.Arms[1])
	}
	if len(analysis.Missing) != 0 {
		t.Fatalf("unexpected missing cases: %#v", analysis.Missing)
	}
}

func TestPatternDiagnosticsCarryCounterexamplesAndUnnecessaryTags(t *testing.T) {
	tc := patternAnalysisChecker()
	expr := &ast.MatchExpression{Arms: []*ast.MatchArm{
		arm(variantPattern("Some", wildcardPattern())),
		arm(variantPattern("Some", boolPattern(true))),
	}}
	analysis := tc.analyzeMatch(expr, &ADTType{Name: "OptionBool"})
	tc.emitMatchAnalysisDiagnostics(expr, analysis)

	var sawMissing, sawRedundant bool
	for _, d := range tc.Diagnostics() {
		switch d.Code {
		case CodeMatchNonExhaustive:
			sawMissing = true
			data, ok := d.Data.(map[string]interface{})
			if !ok {
				t.Fatalf("counterexample data missing: %#v", d.Data)
			}
			cases, ok := data["counterexamples"].([]string)
			if !ok || len(cases) != 1 || cases[0] != ".None" {
				t.Fatalf("counterexamples = %#v", data["counterexamples"])
			}
		case CodeMatchRedundantArm:
			sawRedundant = true
			if d.Severity != diagnostic.SeverityWarning {
				t.Fatalf("redundant arm severity = %v", d.Severity)
			}
			if len(d.Tags) != 1 || d.Tags[0] != diagnostic.TagUnnecessary {
				t.Fatalf("redundant tags = %#v", d.Tags)
			}
		}
	}
	if !sawMissing || !sawRedundant {
		t.Fatalf("diagnostics = %#v", tc.Diagnostics())
	}
}
