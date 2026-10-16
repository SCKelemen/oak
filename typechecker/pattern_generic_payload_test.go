package typechecker

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func checkPatternPayloadSource(t *testing.T, input string) *TypeChecker {
	t.Helper()
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		t.Fatalf("parse errors: %v", errors)
	}
	tc := setupTypeChecker(input)
	tc.CheckProgram(program)
	return tc
}

func TestPatternAnalysisNestedGenericPayloadSource(t *testing.T) {
	const option = "Option[T]: type = Some: T | None\n"
	const concreteOuter = "Outer: type = Wrap: Option[Bool] | Empty"
	const genericOuter = "Outer[T]: type = Wrap: Option[T] | Empty"
	for _, test := range []struct {
		name         string
		declarations string
		scrutinee    string
		arms         string
		missing      []string
		warnings     []string
	}{
		{
			name: "concrete payload", declarations: option + concreteOuter, scrutinee: "Outer",
			arms:    ".Wrap(.Some(true)) => 1 | .Empty => 0",
			missing: []string{".Wrap(.Some(false))", ".Wrap(.None)"},
		},
		{
			name: "substituted payload", declarations: option + genericOuter, scrutinee: "Outer[Bool]",
			arms:    ".Wrap(.Some(true)) => 1 | .Empty => 0",
			missing: []string{".Wrap(.Some(false))", ".Wrap(.None)"},
		},
		{
			name: "nested type argument", declarations: option + "Outer[T]: type = Wrap: Option[Option[T]] | Empty", scrutinee: "Outer[Bool]",
			arms:    ".Wrap(.Some(.Some(true))) => 1 | .Empty => 0",
			missing: []string{".Wrap(.Some(.Some(false)))", ".Wrap(.Some(.None))", ".Wrap(.None)"},
		},
		{
			name: "multiple type arguments", declarations: "Either[T, U]: type = Left: T | Right: U\nOuter[T]: type = Wrap: Either[T, Bool] | Empty", scrutinee: "Outer[Bool]",
			arms:    ".Wrap(.Left(true)) => 1 | .Wrap(.Right(false)) => 2 | .Empty => 0",
			missing: []string{".Wrap(.Left(false))", ".Wrap(.Right(true))"},
		},
		{
			name: "exhaustive", declarations: option + genericOuter, scrutinee: "Outer[Bool]",
			arms: ".Wrap(.Some(true)) => 1 | .Wrap(.Some(false)) => 2 | .Wrap(.None) => 3 | .Empty => 0",
		},
		{
			name: "catch all", declarations: option + genericOuter, scrutinee: "Outer[Bool]",
			arms: ".Wrap(.Some(true)) => 1 | _ => 0",
		},
		{
			name: "redundant nested pattern", declarations: option + genericOuter, scrutinee: "Outer[Bool]",
			arms:     ".Wrap(.Some(true)) => 1 | .Wrap(.Some(true)) => \"unreachable\" | .Wrap(.Some(false)) => 2 | .Wrap(.None) => 3 | .Empty => 0",
			warnings: []string{CodeMatchRedundantArm},
		},
		{
			name: "nested indexed payload", declarations: "Expr[T]: type = Flag: Bool => Expr[Bool] | Int: i64 => Expr[i64]\nOuter[T]: type = Wrap: Expr[T] | Empty", scrutinee: "Outer[Bool]",
			arms:    ".Wrap(.Flag(true)) => 1 | .Wrap(.Int(_)) => \"impossible\" | .Empty => 0",
			missing: []string{".Wrap(.Flag(false))"}, warnings: []string{CodeMatchImpossibleArm},
		},
	} {
		for _, prefix := range []string{"", "type "} {
			style := "canonical"
			if prefix != "" {
				style = "legacy declaration"
			}
			t.Run(test.name+"/"+style, func(t *testing.T) {
				declarations := prefix + strings.ReplaceAll(test.declarations, "\n", "\n"+prefix)
				if prefix != "" {
					declarations = strings.ReplaceAll(declarations, "type = ", "type = | ")
				}
				tc := checkPatternPayloadSource(t, declarations+"\nf: (x: "+test.scrutinee+"): u8 = x ? { | "+test.arms+" }")
				var missing, warnings []string
				for _, d := range tc.Diagnostics() {
					switch d.Code {
					case CodeMatchNonExhaustive:
						data, ok := d.Data.(map[string]interface{})
						if !ok {
							t.Fatalf("missing counterexample data: %#v", d)
						}
						cases, ok := data["counterexamples"].([]string)
						if !ok {
							t.Fatalf("invalid counterexamples: %#v", data)
						}
						missing = append(missing, cases...)
					case CodeMatchRedundantArm, CodeMatchImpossibleArm:
						warnings = append(warnings, d.Code)
					default:
						t.Fatalf("unexpected diagnostic: %#v", d)
					}
				}
				if !reflect.DeepEqual(missing, test.missing) {
					t.Errorf("missing = %#v, want %#v", missing, test.missing)
				}
				if !reflect.DeepEqual(warnings, test.warnings) {
					t.Errorf("warnings = %#v, want %#v", warnings, test.warnings)
				}
			})
		}
	}
}

func TestPatternAnalysisInvalidNestedGenericPayloadSuppressesExhaustiveness(t *testing.T) {
	tc := checkPatternPayloadSource(t, `Option[T]: type = Some: T | None
Outer[T]: type = Wrap: Option[T] | Empty
f: (x: Outer[Bool]): u8 = x ? { | .Wrap(.Some("wrong")) => 1 }`)
	if errors := tc.Errors(); len(errors) != 1 || !strings.Contains(errors[0], "pattern literal type string does not match expected type Bool") {
		t.Fatalf("expected only the root payload type error, got %v", errors)
	}
	for _, d := range tc.Diagnostics() {
		if d.Code == CodeMatchNonExhaustive {
			t.Fatalf("invalid payload caused derivative exhaustiveness diagnostic: %#v", d)
		}
	}
}

func TestPatternAnalysisOuterGADTRefinesNestedPayload(t *testing.T) {
	tc := checkPatternPayloadSource(t, `Option[T]: type = Some: T | None
Outer[T]: type = Wrap: Option[T] => Outer[Bool] | Empty => Outer[T]`)
	if errors := tc.Errors(); len(errors) != 0 {
		t.Fatalf("declaration errors: %v", errors)
	}
	scrutinee := &GenericType{Name: "Outer", TypeArgs: []Type{NewUnifier().FreshTypeVar("X")}}
	expr := &ast.MatchExpression{
		Scrutinee: &ast.Identifier{Value: "x"},
		Arms: []*ast.MatchArm{
			arm(variantPattern("Wrap", variantPattern("Some", boolPattern(true)))),
			arm(variantPattern("Empty", nil)),
		},
	}
	analysis := tc.analyzeMatch(expr, scrutinee)
	want := []string{".Wrap(.Some(false))", ".Wrap(.None)"}
	if !analysis.Reliable || !reflect.DeepEqual(analysis.Missing, want) {
		t.Fatalf("analysis = %#v, want reliable coverage missing %#v", analysis, want)
	}
	equalities := analysis.Arms[0].Refinements[0].Equalities
	if !reflect.DeepEqual(equalities, []TypeIndexEquality{{Parameter: "T", Type: "Bool"}}) {
		t.Fatalf("fixed constructor equalities = %#v", equalities)
	}
	pattern := variantPattern("Wrap", variantPattern("Some", &ast.BindingPattern{Name: &ast.Identifier{Value: "payload"}}))
	if tc.checkPattern(pattern, scrutinee) == nil {
		t.Fatalf("refined nested pattern rejected: %v", tc.Errors())
	}
	if got, ok := tc.env.GetType("payload"); !ok || !reflect.DeepEqual(got, &BoolType{}) {
		t.Fatalf("refined nested payload = %#v, want Bool", got)
	}
}

func TestPatternAnalysisReusesGenericPayloadAcrossInstantiations(t *testing.T) {
	tc := checkPatternPayloadSource(t, `Option[T]: type = Some: T | None
Outer[T]: type = Wrap: Option[T] | Empty`)
	if errors := tc.Errors(); len(errors) != 0 {
		t.Fatalf("declaration errors: %v", errors)
	}
	for _, test := range []struct {
		argument Type
		literal  ast.Pattern
		missing  string
	}{
		{&BoolType{}, boolPattern(true), ".Wrap(.Some(false))"},
		{&PrimitiveType{Name: "u8"}, &ast.LiteralPattern{Value: &ast.IntegerLiteral{Value: 0}}, ".Wrap(.Some(_))"},
		{&BoolType{}, boolPattern(false), ".Wrap(.Some(true))"},
	} {
		scrutinee := &GenericType{Name: "Outer", TypeArgs: []Type{test.argument}}
		expr := &ast.MatchExpression{Arms: []*ast.MatchArm{
			arm(variantPattern("Wrap", variantPattern("Some", test.literal))),
			arm(variantPattern("Empty", nil)),
		}}
		analysis := tc.analyzeMatch(expr, scrutinee)
		want := []string{test.missing, ".Wrap(.None)"}
		if !analysis.Reliable || !reflect.DeepEqual(analysis.Missing, want) {
			t.Fatalf("%s analysis = %#v, want reliable coverage missing %#v", scrutinee, analysis, want)
		}
		if tc.checkPattern(expr.Arms[0].Pattern, scrutinee) == nil {
			t.Fatalf("%s pattern rejected: %v", scrutinee, tc.Errors())
		}
	}
	open := &GenericType{Name: "Option", TypeArgs: []Type{&ADTType{Name: "T"}}}
	if got := tc.adtPayloadTypes["Outer"]["Wrap"]; !reflect.DeepEqual(got, open) {
		t.Fatalf("cached generic payload changed: %#v, want %#v", got, open)
	}
}

func TestVariantPayloadInstantiationPreservesArrayShape(t *testing.T) {
	for _, test := range []struct {
		source string
		want   *ArrayType
	}{
		{"[4]T", &ArrayType{Length: 4}},
		{"[]T", &ArrayType{Length: -1, IsSlice: true}},
		{"[align 16]T", &ArrayType{Length: -1, IsSlice: true, Align: 16}},
		{"[*]T", &ArrayType{Length: -1, IsSpan: true}},
		{"[* align 64]T", &ArrayType{Length: -1, IsSpan: true, Align: 64}},
	} {
		t.Run(test.source, func(t *testing.T) {
			tc := checkPatternPayloadSource(t, "Box[T]: type = Hold: "+test.source+" | Empty")
			if errors := tc.Errors(); len(errors) != 0 {
				t.Fatalf("declaration errors: %v", errors)
			}
			variant, ok := tc.findADTVariant("Box", "Hold")
			if !ok {
				t.Fatal("missing Hold variant")
			}
			want := *test.want
			want.ElementType = &BoolType{}
			parent := &GenericType{Name: "Box", TypeArgs: []Type{&BoolType{}}}
			for name, got := range map[string]Type{
				"coverage": tc.variantPayloadType(parent, variant),
				"pattern":  tc.instantiatedVariantPayload("Box", variant, map[string]Type{"T": &BoolType{}}),
			} {
				if !reflect.DeepEqual(got, &want) {
					t.Errorf("%s payload = %#v, want %#v", name, got, &want)
				}
			}
			// Neither substitution path may mutate the declaration's open payload.
			original := *test.want
			original.ElementType = &ADTType{Name: "T"}
			if got := tc.adtPayloadTypes["Box"]["Hold"]; !reflect.DeepEqual(got, &original) {
				t.Fatalf("cached payload changed: %#v, want %#v", got, &original)
			}
			pattern := variantPattern("Hold", &ast.BindingPattern{Name: &ast.Identifier{Value: "payload"}})
			if tc.checkPattern(pattern, parent) == nil {
				t.Fatalf("pattern rejected: %v", tc.Errors())
			}
			if got, ok := tc.env.GetType("payload"); !ok || !reflect.DeepEqual(got, &want) {
				t.Fatalf("bound payload = %#v, want %#v", got, &want)
			}
		})
	}
}
