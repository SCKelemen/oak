package typechecker

import (
	"fmt"
	"strings"
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
		Name:     "OnlyVoid",
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

func TestMatchStructuredGenericPayloadInhabitation(t *testing.T) {
	tc := patternAnalysisChecker()
	for _, decl := range []*ast.ADTType{
		{Name: &ast.Identifier{Value: "Box"}, TypeParams: []*ast.TypeParameter{{Name: &ast.Identifier{Value: "T"}}},
			Variants: []*ast.ADTVariant{{Name: &ast.Identifier{Value: "Put"}, Payload: &ast.Identifier{Value: "T"}}}},
		{Name: &ast.Identifier{Value: "Envelope"}, TypeParams: []*ast.TypeParameter{{Name: &ast.Identifier{Value: "T"}}},
			Variants: []*ast.ADTVariant{{Name: &ast.Identifier{Value: "Wrap"}, Payload: indexedType("Box", "T")}}},
	} {
		tc.checkADTType(decl)
	}
	if errors := tc.Errors(); len(errors) != 0 {
		t.Fatalf("declaration errors: %v", errors)
	}
	for _, test := range []struct {
		name      string
		arg       Type
		inhabited bool
	}{
		{"empty", &ADTType{Name: "Void"}, false},
		{"inhabited", &BoolType{}, true},
		{"nested_empty", &GenericType{Name: "Box", TypeArgs: []Type{&ADTType{Name: "Void"}}}, false},
		{"unknown", &ADTType{Name: "Unknown"}, true},
	} {
		t.Run(test.name, func(t *testing.T) {
			typ := &GenericType{Name: "Envelope", TypeArgs: []Type{test.arg}}
			assertMatchInhabitation(t, tc, typ, variantPattern("Wrap", wildcardPattern()), test.inhabited)
		})
	}
	// The same structured payload must be used for nested constructor coverage,
	// not only for the emptiness precheck.
	typ := &GenericType{Name: "Envelope", TypeArgs: []Type{&BoolType{}}}
	result := tc.analyzeMatch(&ast.MatchExpression{Arms: []*ast.MatchArm{
		arm(variantPattern("Wrap", variantPattern("Put", boolPattern(true)))),
	}}, typ)
	if !result.Reliable || len(result.Missing) != 1 || result.Missing[0] != ".Wrap(.Put(false))" {
		t.Fatalf("structured nested witness: %#v", result)
	}
}

func assertMatchInhabitation(t *testing.T, tc *TypeChecker, typ Type, pattern ast.Pattern, inhabited bool) {
	t.Helper()
	if got := tc.coverageHasValues(typ); got != inhabited {
		t.Errorf("coverageHasValues = %v, want %v", got, inhabited)
	}
	empty := tc.analyzeMatch(&ast.MatchExpression{}, typ)
	if !empty.Reliable || (len(empty.Missing) != 0) != inhabited {
		t.Errorf("empty match must have a witness exactly when inhabited: %#v", empty)
	}
	for _, p := range []ast.Pattern{pattern, wildcardPattern()} {
		result := tc.analyzeMatch(&ast.MatchExpression{Arms: []*ast.MatchArm{arm(p)}}, typ)
		if !result.Reliable || len(result.Missing) != 0 || result.Arms[0].Reachable != inhabited || result.Arms[0].Impossible == inhabited || result.Arms[0].Redundant {
			t.Errorf("arm inhabitation = %#v, want reachable %v", result, inhabited)
		}
	}
}

func TestMatchProductPayloadInhabitation(t *testing.T) {
	void := &ADTType{Name: "Void"}
	for _, test := range []struct {
		name      string
		payload   Type
		inhabited bool
	}{
		{"record", &RecordType{Fields: map[string]Type{"empty": void}}, false},
		{"open_record", &RecordType{Fields: map[string]Type{"empty": void}, Open: true}, false},
		{"struct", &RecordType{Name: "ImpossibleStruct", Struct: true, Fields: map[string]Type{"empty": void}}, false},
		{"fixed_array", &ArrayType{ElementType: void, Length: 1}, false},
		{"nested_product", &RecordType{Fields: map[string]Type{"items": &ArrayType{ElementType: void, Length: 2}}}, false},
		{"never_field", &RecordType{Fields: map[string]Type{"empty": &NeverType{}}}, false},
		{"empty_record", &RecordType{Fields: map[string]Type{}}, true},
		{"bool_record", &RecordType{Fields: map[string]Type{"ok": &BoolType{}}}, true},
		{"zero_array", &ArrayType{ElementType: void, Length: 0}, true},
		{"slice", &ArrayType{ElementType: void, Length: -1, IsSlice: true}, true},
		{"span", &ArrayType{ElementType: void, Length: -1, IsSpan: true}, true},
		{"unknown_length", &ArrayType{ElementType: void, Length: -1}, true},
		{"unknown_field", &RecordType{Fields: map[string]Type{"open": &ADTType{Name: "Unknown"}}}, true},
	} {
		t.Run(test.name, func(t *testing.T) {
			tc := patternAnalysisChecker()
			tc.adtTypes["Product"] = &object.ADTType{Name: "Product", Variants: []*object.ADTVariantDef{{Name: "Wrap", Payload: "payload"}}}
			tc.adtPayloadTypes["Product"] = map[string]Type{"Wrap": test.payload}
			assertMatchInhabitation(t, tc, &ADTType{Name: "Product"}, variantPattern("Wrap", wildcardPattern()), test.inhabited)
			assertMatchInhabitation(t, tc, test.payload, wildcardPattern(), test.inhabited)
			// An impossible product constructor must not erase a live sibling.
			tc.adtTypes["Product"].Variants = append(tc.adtTypes["Product"].Variants, &object.ADTVariantDef{Name: "Unit"})
			result := tc.analyzeMatch(&ast.MatchExpression{Arms: []*ast.MatchArm{arm(variantPattern("Unit", nil))}}, &ADTType{Name: "Product"})
			if !result.Reliable || !result.Arms[0].Reachable || (len(result.Missing) != 0) != test.inhabited {
				t.Fatalf("live sibling coverage: %#v", result)
			}
		})
	}
}

func TestMatchRecursivePayloadRemainsConservative(t *testing.T) {
	for _, shape := range []string{"direct", "record", "array", "growing", "duplicating"} {
		t.Run(shape, func(t *testing.T) {
			tc := patternAnalysisChecker()
			tc.adtTypes["Loop"] = &object.ADTType{Name: "Loop", TypeParams: []string{"T"}, Variants: []*object.ADTVariantDef{{Name: "Next", Payload: "recursive"}}}
			var arg Type = &ADTType{Name: "T"}
			if shape == "growing" {
				arg = &GenericType{Name: "Box", TypeArgs: []Type{arg}}
			}
			if shape == "duplicating" {
				arg = &GenericType{Name: "Pair", TypeArgs: []Type{arg, arg}}
			}
			var payload Type = &GenericType{Name: "Loop", TypeArgs: []Type{arg}}
			if shape == "record" {
				payload = &RecordType{Fields: map[string]Type{"next": payload}}
			}
			if shape == "array" {
				payload = &ArrayType{ElementType: payload, Length: 1}
			}
			tc.adtPayloadTypes["Loop"] = map[string]Type{"Next": payload}
			typ := &GenericType{Name: "Loop", TypeArgs: []Type{&BoolType{}}}
			assertMatchInhabitation(t, tc, typ, variantPattern("Next", wildcardPattern()), true)
		})
	}
}

func expandingPatternChecker() (*TypeChecker, Type) {
	tc := patternAnalysisChecker()
	tc.adtTypes["Loop"] = &object.ADTType{Name: "Loop", TypeParams: []string{"T"}, Variants: []*object.ADTVariantDef{{Name: "Next", Payload: "Loop[Pair[T,T]]"}}}
	parameter := &ADTType{Name: "T"}
	tc.adtPayloadTypes["Loop"] = map[string]Type{"Next": &GenericType{Name: "Loop", TypeArgs: []Type{
		&GenericType{Name: "Pair", TypeArgs: []Type{parameter, parameter}},
	}}}
	return tc, &GenericType{Name: "Loop", TypeArgs: []Type{&BoolType{}}}
}

func nestedNextPattern(depth int) ast.Pattern {
	var pattern ast.Pattern = wildcardPattern()
	for i := 0; i < depth; i++ {
		pattern = variantPattern("Next", pattern)
	}
	return pattern
}

func TestMatchExpansionBudget(t *testing.T) {
	for _, depth := range []int{12, 64} {
		t.Run(fmt.Sprintf("depth_%d", depth), func(t *testing.T) {
			tc, typ := expandingPatternChecker()
			deep := arm(nestedNextPattern(depth))
			match := &ast.MatchExpression{Scrutinee: &ast.Identifier{Value: "x"}, Arms: []*ast.MatchArm{deep}}
			result := tc.analyzeMatch(match, typ)
			if !result.Reliable || !result.Arms[0].Reachable || result.Arms[0].Impossible || result.Arms[0].Redundant || len(result.Missing) == 0 {
				t.Fatalf("budget exhaustion must remain potentially useful and non-exhaustive: %#v", result)
			}
			match.Arms = append(match.Arms, arm(wildcardPattern()))
			result = tc.analyzeMatch(match, typ)
			if !result.Reliable || !result.Arms[1].Reachable || len(result.Missing) != 0 {
				t.Fatalf("wildcard must cover the unknown remainder: %#v", result)
			}
			match.Arms = []*ast.MatchArm{arm(wildcardPattern()), deep}
			result = tc.analyzeMatch(match, typ)
			if !result.Reliable || !result.Arms[1].Redundant || result.Arms[1].Reachable || result.Arms[1].Impossible || len(result.Missing) != 0 {
				t.Fatalf("deep arm after wildcard must remain redundant: %#v", result)
			}
		})
	}
}

func TestMatchExpansionBudgetFullTypecheck(t *testing.T) {
	for _, depth := range []int{3, 12, 64} {
		t.Run(fmt.Sprintf("depth_%d", depth), func(t *testing.T) {
			tc, typ := expandingPatternChecker()
			tc.env.SetType("x", typ)
			tc.CheckExpression(&ast.MatchExpression{Scrutinee: &ast.Identifier{Value: "x"}, Arms: []*ast.MatchArm{
				arm(nestedNextPattern(depth)), arm(wildcardPattern()),
			}})
			errors := strings.Join(tc.Errors(), "\n")
			if depth == 3 {
				if errors != "" {
					t.Fatalf("ordinary finite pattern rejected: %s", errors)
				}
			} else if !strings.Contains(errors, "constructor pattern type expansion exceeds") {
				t.Fatalf("expanded constructor pattern must fail closed with a complexity diagnostic: %s", errors)
			}
		})
	}
	// A wildcard requires no constructor expansion and remains accepted.
	tc, typ := expandingPatternChecker()
	tc.env.SetType("x", typ)
	tc.CheckExpression(&ast.MatchExpression{Scrutinee: &ast.Identifier{Value: "x"}, Arms: []*ast.MatchArm{arm(wildcardPattern())}})
	if errors := tc.Errors(); len(errors) != 0 {
		t.Fatalf("wildcard rejected: %v", errors)
	}
}

func TestMatchOversizedSharedTypeRemainsUnknown(t *testing.T) {
	tc, _ := expandingPatternChecker()
	var argument Type = &BoolType{}
	for i := 0; i < 20; i++ {
		// A small DAG whose unfolded form has more than a million nodes.
		argument = &GenericType{Name: "Pair", TypeArgs: []Type{argument, argument}}
	}
	typ := &GenericType{Name: "Loop", TypeArgs: []Type{argument}}
	if _, bounded := coverageTypeSize(typ); bounded {
		t.Fatal("shared tree should exceed the unfolded budget")
	}
	if !tc.coverageHasValues(typ) {
		t.Fatal("exhaustion is not proof of emptiness")
	}
	empty := tc.analyzeMatch(&ast.MatchExpression{}, typ)
	if !empty.Reliable || len(empty.Missing) != 1 || empty.Missing[0] != "_" {
		t.Fatalf("unknown empty-match witness: %#v", empty)
	}
	match := &ast.MatchExpression{Scrutinee: &ast.Identifier{Value: "x"}, Arms: []*ast.MatchArm{arm(variantPattern("Next", wildcardPattern()))}}
	result := tc.analyzeMatch(match, typ)
	if !result.Reliable || !result.Arms[0].Reachable || len(result.Missing) == 0 || len(result.Arms[0].Refinements) != 1 || len(result.Arms[0].Refinements[0].Equalities) != 0 {
		t.Fatalf("unknown variant must preserve arity and omit unproved index equalities: %#v", result)
	}
	match.Arms = append(match.Arms, arm(wildcardPattern()))
	result = tc.analyzeMatch(match, typ)
	if !result.Reliable || !result.Arms[1].Reachable || len(result.Missing) != 0 {
		t.Fatalf("unknown wildcard coverage: %#v", result)
	}
	match.Arms = []*ast.MatchArm{arm(variantPattern("Next", nil))}
	if result = tc.analyzeMatch(match, typ); result.Reliable {
		t.Fatalf("budget must not erase mandatory payload arity: %#v", result)
	}
}
