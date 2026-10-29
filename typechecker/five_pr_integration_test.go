package typechecker

import (
	"fmt"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// These integration controls deliberately pass a parsed open-row type through
// the GADT solver used by pattern coverage, rather than testing Unify alone.
func fivePRIndexed(name string, arguments ...string) ast.Expression {
	var result ast.Expression = &ast.Identifier{Value: name}
	for _, argument := range arguments {
		result = &ast.IndexExpression{Left: result, Index: &ast.Identifier{Value: argument}}
	}
	return result
}

func fivePRGADTChecker(t *testing.T) *TypeChecker {
	t.Helper()
	tc := patternAnalysisChecker()
	tc.checkADTType(&ast.ADTType{
		Name:       &ast.Identifier{Value: "IntegrationBox"},
		TypeParams: []*ast.TypeParameter{{Name: &ast.Identifier{Value: "T"}}},
		Variants:   []*ast.ADTVariant{{Name: &ast.Identifier{Value: "Put"}, Payload: &ast.Identifier{Value: "T"}}},
	})
	tc.checkADTType(&ast.ADTType{
		Name: &ast.Identifier{Value: "IntegrationGate"},
		TypeParams: []*ast.TypeParameter{
			{Name: &ast.Identifier{Value: "A"}},
			{Name: &ast.Identifier{Value: "B"}},
			{Name: &ast.Identifier{Value: "P"}},
		},
		Variants: []*ast.ADTVariant{{
			Name:    &ast.Identifier{Value: "Same"},
			Payload: fivePRIndexed("IntegrationBox", "P"),
			Result:  fivePRIndexed("IntegrationGate", "A", "A", "P"),
		}},
	})
	if errors := tc.Errors(); len(errors) != 0 {
		t.Fatalf("checked integration declarations: %v", errors)
	}
	return tc
}

func TestFivePRGADTRecordBoundaryFeedsCoverage(t *testing.T) {
	open := parsedEmptyOpenRow(t)
	cases := []struct {
		name        string
		left, right Type
		admitted    bool
	}{
		{"parsed_open_unit", open, &UnitType{}, false},
		{"closed_unit", &RecordType{}, &UnitType{}, true},
		{"nominal_unit", &RecordType{Name: "Token", Struct: true}, &UnitType{}, false},
		{"same_nominal", &RecordType{Name: "Token", Struct: true}, &RecordType{Name: "Token", Struct: true}, true},
		{"distinct_nominal", &RecordType{Name: "Left", Struct: true}, &RecordType{Name: "Right", Struct: true}, false},
		{"both_open", open, &RecordType{Open: true, Row: "different_diagnostic_row"}, true},
	}
	wrappers := []struct {
		name string
		wrap func(Type) Type
	}{
		{"direct", func(x Type) Type { return x }},
		{"array", func(x Type) Type { return &ArrayType{Length: 2, ElementType: x} }},
		{"function", func(x Type) Type { return &FunctionType{Parameters: []Type{x}, ReturnType: x} }},
		{"generic", func(x Type) Type { return &GenericType{Name: "IndexBox", TypeArgs: []Type{x}} }},
		{"record", func(x Type) Type { return &RecordType{Fields: map[string]Type{"index": x}} }},
	}
	payloads := []struct {
		name      string
		typ       Type
		inhabited bool
	}{
		{"bool", &BoolType{}, true},
		{"void", &ADTType{Name: "Void"}, false},
		{"unknown", &ADTType{Name: "Unknown"}, true},
	}
	for _, c := range cases {
		for _, w := range wrappers {
			for direction, pair := range [][2]Type{{c.left, c.right}, {c.right, c.left}} {
				for _, payload := range payloads {
					t.Run(fmt.Sprintf("%s/%s/order%d/%s", c.name, w.name, direction, payload.name), func(t *testing.T) {
						tc := fivePRGADTChecker(t)
						adt := tc.adtTypes["IntegrationGate"]
						actual := []Type{w.wrap(pair[0]), w.wrap(pair[1]), payload.typ}
						bindings, substitution, admitted := tc.variantIndexBindings(adt, adt.Variants[0], actual)
						if admitted != c.admitted {
							t.Fatalf("repeated GADT index admission = %v, want %v", admitted, c.admitted)
						}
						if !admitted && (bindings != nil || substitution != nil) {
							t.Fatal("failed GADT equations leaked partial solutions")
						}
						typ := &GenericType{Name: "IntegrationGate", TypeArgs: actual}
						// This executes #745's structured generic-payload path only
						// after #796's repeated-index admission has succeeded.
						assertMatchInhabitation(t, tc, typ, variantPattern("Same", wildcardPattern()), c.admitted && payload.inhabited)
					})
				}
			}
		}
	}
}

func TestFivePRGADTSubstitutionTransactionRollback(t *testing.T) {
	open := parsedEmptyOpenRow(t)
	for direction, pair := range [][2]Type{{open, &UnitType{}}, {&UnitType{}, open}} {
		t.Run(fmt.Sprintf("order%d", direction), func(t *testing.T) {
			tc := fivePRGADTChecker(t)
			adt := &object.ADTType{Name: "Repeated", TypeParams: []string{"A", "B", "C"}}
			variant := &object.ADTVariantDef{Name: "Same", ResultName: "Repeated", ResultIndices: []string{"A", "A", "A"}}
			v := NewUnifier().FreshTypeVar("X")
			v.Monomorphic = make(Substitution)
			v.monomorphicGroup = &monomorphicGroup{}
			bindings, substitution, admitted := tc.variantIndexBindings(adt, variant, []Type{v, pair[0], pair[1]})
			if admitted || bindings != nil || substitution != nil || len(v.Monomorphic) != 0 {
				t.Fatal("failed later GADT equation retained an earlier solution")
			}
			// Two individually valid GADT solutions conflict only when they
			// reach the persistent transaction merger from #796.
			tc.beginMonomorphicTransaction()
			for _, solution := range pair {
				_, sub, ok := tc.variantIndexBindings(adt, variant, []Type{v, solution, solution})
				if !ok || sub == nil {
					t.Fatal("positive individual GADT solution refused")
				}
				tc.stageMonomorphicBindings(sub)
			}
			tc.finishMonomorphicTransaction(true)
			if len(tc.Errors()) == 0 || len(v.Monomorphic) != 0 || len(tc.monomorphicTransactions) != 0 {
				t.Fatal("conflicting GADT solutions escaped transactional rollback")
			}
			// Rollback must not poison the next successful use. Unit/closed
			// admission remains compatible, with Unit retained as the solution.
			errors := len(tc.Errors())
			_, sub, ok := tc.variantIndexBindings(adt, variant, []Type{v, &UnitType{}, &RecordType{}})
			if !ok || sub == nil {
				t.Fatal("compatible GADT control refused after rollback")
			}
			tc.beginMonomorphicTransaction()
			tc.stageMonomorphicBindings(sub)
			tc.finishMonomorphicTransaction(true)
			if len(tc.Errors()) != errors || len(tc.monomorphicTransactions) != 0 {
				t.Fatal("successful transaction inherited a prior failure")
			}
			if _, ok := v.Monomorphic.Apply(v).(*UnitType); !ok {
				t.Fatalf("successful Unit solution was erased: %T", v.Monomorphic.Apply(v))
			}
		})
	}
}
