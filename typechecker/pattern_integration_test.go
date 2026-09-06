package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func TestMatchCheckerSkipsRedundantArmBodyFromResultJoin(t *testing.T) {
	tc := patternAnalysisChecker()
	tc.env.SetType("x", &ADTType{Name: "OptionBool"})

	expr := &ast.MatchExpression{
		Scrutinee: &ast.Identifier{Value: "x"},
		Arms: []*ast.MatchArm{
			{Pattern: variantPattern("Some", wildcardPattern()), Body: &ast.IntegerLiteral{Value: 1}},
			// This arm is redundant. Its string result must not widen the match.
			{Pattern: variantPattern("Some", boolPattern(true)), Body: &ast.StringLiteral{Value: "unreachable"}},
			{Pattern: variantPattern("None", nil), Body: &ast.IntegerLiteral{Value: 0}},
		},
	}

	got := tc.checkMatchExpression(expr)
	if got == nil || !got.Equals(&PrimitiveType{Name: "i32"}) {
		t.Fatalf("match type = %v, want i32", got)
	}

	var redundant bool
	for _, d := range tc.Diagnostics() {
		if d.Code == CodeMatchRedundantArm {
			redundant = true
		}
		if d.Code == string("OAK-T0000") && d.Message == "match expression has branches with incompatible types. Use explicit 'any' return type if intentional." {
			t.Fatalf("redundant arm widened the result: %#v", d)
		}
	}
	if !redundant {
		t.Fatalf("expected redundant-arm diagnostic, got %#v", tc.Diagnostics())
	}
}

func TestMatchCheckerEmitsNestedCounterexample(t *testing.T) {
	tc := patternAnalysisChecker()
	tc.env.SetType("x", &ADTType{Name: "OptionBool"})

	expr := &ast.MatchExpression{
		Scrutinee: &ast.Identifier{Value: "x"},
		Arms: []*ast.MatchArm{
			{Pattern: variantPattern("Some", boolPattern(true)), Body: &ast.IntegerLiteral{Value: 1}},
			{Pattern: variantPattern("None", nil), Body: &ast.IntegerLiteral{Value: 0}},
		},
	}

	_ = tc.checkMatchExpression(expr)
	for _, d := range tc.Diagnostics() {
		if d.Code != CodeMatchNonExhaustive {
			continue
		}
		data, ok := d.Data.(map[string]interface{})
		if !ok {
			t.Fatalf("counterexample data missing: %#v", d.Data)
		}
		cases, ok := data["counterexamples"].([]string)
		if !ok || len(cases) != 1 || cases[0] != ".Some(false)" {
			t.Fatalf("counterexamples = %#v", data["counterexamples"])
		}
		return
	}
	t.Fatalf("expected %s, got %#v", CodeMatchNonExhaustive, tc.Diagnostics())
}
