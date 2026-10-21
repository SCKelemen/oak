package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func parsedEmptyOpenRow(t *testing.T) *RecordType {
	t.Helper()
	p := parser.New(scanner.New("value: { r | }"))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parse open-row annotation: %v", errs)
	}
	if len(program.Statements) != 1 {
		t.Fatalf("got %d statements, want one declaration", len(program.Statements))
	}
	decl, ok := program.Statements[0].(*ast.VariableDeclaration)
	if !ok {
		t.Fatalf("annotation produced %T", program.Statements[0])
	}
	tc := setupTypeChecker("")
	row, ok := tc.parseTypeExpression(decl.Type).(*RecordType)
	if !ok || !row.Open || len(row.Fields) != 0 {
		t.Fatalf("annotation did not produce an empty open row: %#v", row)
	}
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("check open-row annotation: %v", errs)
	}
	return row
}

func TestUnificationParsedOpenRowUnitBoundary(t *testing.T) {
	open := parsedEmptyOpenRow(t)
	wrappers := []struct {
		name string
		wrap func(Type) Type
	}{
		{"direct", func(x Type) Type { return x }},
		{"function parameter", func(x Type) Type { return &FunctionType{Parameters: []Type{x}, ReturnType: &UnitType{}} }},
		{"function result", func(x Type) Type { return &FunctionType{ReturnType: x} }},
		{"array", func(x Type) Type { return &ArrayType{Length: 2, ElementType: x} }},
		{"slice", func(x Type) Type { return &ArrayType{IsSlice: true, ElementType: x} }},
		{"span", func(x Type) Type { return &ArrayType{IsSpan: true, ElementType: x} }},
		{"generic", func(x Type) Type { return &GenericType{Name: "Box", TypeArgs: []Type{x}} }},
		{"record", func(x Type) Type { return &RecordType{Fields: map[string]Type{"value": x}} }},
	}
	cases := []struct {
		name        string
		left, right Type
		want        bool
	}{
		{"open versus unit", open, &UnitType{}, false},
		{"open versus closed", open, &RecordType{}, false},
		{"closed versus unit", &RecordType{}, &UnitType{}, true},
		{"nominal versus unit", &RecordType{Name: "Token", Struct: true}, &UnitType{}, false},
		{"nonempty versus unit", &RecordType{Fields: map[string]Type{"x": &BoolType{}}}, &UnitType{}, false},
		{"unit versus unit", &UnitType{}, &UnitType{}, true},
	}
	for _, c := range cases {
		for _, w := range wrappers {
			t.Run(c.name+"/"+w.name, func(t *testing.T) {
				for _, pair := range [][2]Type{{c.left, c.right}, {c.right, c.left}} {
					u := NewUnifier()
					if got := u.Unify(w.wrap(pair[0]), w.wrap(pair[1])) != nil; got != c.want {
						t.Errorf("Unify(%T, %T) = %v, want %v; errors %v", pair[0], pair[1], got, c.want, u.Errors())
					}
				}
			})
		}
	}
}

func TestUnificationOpenRowUnitRepeatedBinder(t *testing.T) {
	open := parsedEmptyOpenRow(t)
	unit := &UnitType{}
	closed := &RecordType{}
	cases := []struct {
		name string
		args []Type
		want bool
	}{
		{"open first", []Type{open, unit}, false},
		{"unit first", []Type{unit, open}, false},
		{"unit closed open bridge", []Type{unit, closed, open}, false},
		{"unit open closed bridge", []Type{unit, open, closed}, false},
		{"closed unit open bridge", []Type{closed, unit, open}, false},
		{"closed open unit bridge", []Type{closed, open, unit}, false},
		{"open unit closed bridge", []Type{open, unit, closed}, false},
		{"open closed unit bridge", []Type{open, closed, unit}, false},
		{"unit closed unit", []Type{unit, closed, unit}, true},
		{"closed unit closed", []Type{closed, unit, closed}, true},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			v := NewUnifier().FreshTypeVar("T")
			v.Monomorphic = make(Substitution)
			params := make([]Type, len(c.args))
			for i := range params {
				params[i] = v
			}
			left := &FunctionType{Parameters: params, ReturnType: &UnitType{}}
			right := &FunctionType{Parameters: c.args, ReturnType: &UnitType{}}
			sub := NewUnifier().Unify(left, right)
			if got := sub != nil; got != c.want {
				t.Errorf("unified = %v, want %v", got, c.want)
			}
			if len(v.Monomorphic) != 0 {
				t.Fatal("unification mutated persistent binder state")
			}
			if sub != nil {
				// Admission normalization must not change the binder's solution.
				switch c.args[0].(type) {
				case *UnitType:
					if _, ok := sub.Apply(v).(*UnitType); !ok {
						t.Fatalf("Unit solution normalized outside admission: %T", sub.Apply(v))
					}
				case *RecordType:
					if _, ok := sub.Apply(v).(*RecordType); !ok {
						t.Fatalf("record solution changed: %T", sub.Apply(v))
					}
				}
			}
		})
	}
}

func TestUnificationOpenRowUnitTransactionRollback(t *testing.T) {
	open := parsedEmptyOpenRow(t)
	for _, pair := range [][2]Type{{open, &UnitType{}}, {&UnitType{}, open}} {
		tc := setupTypeChecker("")
		v := NewUnifier().FreshTypeVar("T")
		v.Monomorphic = make(Substitution)
		v.monomorphicGroup = &monomorphicGroup{}
		tc.beginMonomorphicTransaction()
		tc.stageMonomorphicBindings(Substitution{v: pair[0]})
		tc.stageMonomorphicBindings(Substitution{v: pair[1]})
		tc.finishMonomorphicTransaction(true)
		if len(tc.Errors()) == 0 {
			t.Error("conflicting open-row/Unit staged bindings were committed")
		}
		if len(v.Monomorphic) != 0 || len(tc.monomorphicTransactions) != 0 {
			t.Fatal("conflicting transaction left persistent or staged bindings")
		}
	}
}

func TestUnificationOpenRowAdmissionDoesNotChangeAssignability(t *testing.T) {
	open := parsedEmptyOpenRow(t)
	tc := setupTypeChecker("")
	concrete := &RecordType{Name: "Stored", Struct: true, Fields: map[string]Type{"x": &BoolType{}}}
	if !tc.isAssignable(concrete, open) {
		t.Fatal("a concrete record must still satisfy an empty open-row constraint")
	}
	if NewUnifier().Unify(concrete, open) != nil {
		t.Fatal("constraint satisfaction must not become exact record unification")
	}
}
