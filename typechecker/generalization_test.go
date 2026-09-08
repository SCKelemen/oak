package typechecker

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/token"
)

func nilObjectEnvironment() *object.Environment { return object.NewEnvironment() }

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

func TestFactsFromTypeClassifiesBorrowedAndOwnedAuthority(t *testing.T) {
	element := NewUnifier().FreshTypeVar("T")
	view := factsFromType(&ArrayType{ElementType: element, Length: -1, IsSlice: true})
	if !view.Has(GeneralizationRegionBound) || view.Has(GeneralizationUniqueAuthority) {
		t.Fatalf("view facts = %v", view)
	}
	span := factsFromType(&ArrayType{ElementType: element, Length: -1, IsSpan: true})
	for _, barrier := range []GeneralizationBarrier{
		GeneralizationMutableAuthority, GeneralizationUniqueAuthority, GeneralizationRegionBound,
	} {
		if !span.Has(barrier) {
			t.Fatalf("span facts %v missing %v", span, barrier)
		}
	}
	raw := factsFromType(&PrimitiveType{Name: "ptr"})
	if !raw.Has(GeneralizationExternalAuthority) || !raw.Has(GeneralizationUnknownAuthority) {
		t.Fatalf("raw pointer facts = %v", raw)
	}
}

func TestVariableGeneralizationUsesClosureCaptureFacts(t *testing.T) {
	tc := New(nilObjectEnvironment())
	element := NewUnifier().FreshTypeVar("T")
	tc.env.SetType("borrowed", &ArrayType{ElementType: element, Length: -1, IsSlice: true})
	stmt := &ast.VariableDeclaration{
		Name: &ast.Identifier{Value: "capture"},
		Value: &ast.FunctionLiteral{
			Arguments: nil,
			Body: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "borrowed"}},
			}},
		},
	}
	tc.checkVariableDeclaration(stmt)
	scheme, ok := tc.env.Get("capture")
	if !ok || scheme == nil {
		t.Fatal("capturing closure was not bound")
	}
	if len(scheme.TypeVars) != 0 {
		t.Fatalf("captured region authority generalized to %#v", scheme.TypeVars)
	}
}

func TestClosedFunctionLiteralAddsNoAuthorityBarrier(t *testing.T) {
	tc := New(nilObjectEnvironment())
	literal := &ast.FunctionLiteral{
		Arguments: []*ast.Identifier{{Value: "x"}},
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "x"}},
		}},
	}
	typ := tc.checkExpression(literal)
	facts := deriveGeneralizationFacts(typ, literal, tc.env)
	if !facts.Safe() {
		t.Fatalf("closed function facts = %v", facts)
	}
}

func TestNestedNamedClosureContributesOuterCaptureFacts(t *testing.T) {
	tc := New(nilObjectEnvironment())
	element := NewUnifier().FreshTypeVar("T")
	tc.env.SetType("borrowed", &ArrayType{ElementType: element, Length: -1, IsSlice: true})
	inner := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "inner"},
		Body: &ast.Identifier{Value: "borrowed"},
	}
	outer := &ast.FunctionLiteral{Body: &ast.BlockStatement{Statements: []ast.Statement{
		inner,
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "inner"}},
	}}}
	facts := functionCaptureFacts(outer, tc.env)
	if !facts.Has(GeneralizationMutableAuthority) || !facts.Has(GeneralizationRegionBound) {
		t.Fatalf("nested closure facts = %v", facts)
	}
}

func TestBlockInitializerVisitsAllExecutedStatements(t *testing.T) {
	tc := New(nilObjectEnvironment())
	block := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.VariableDeclaration{
			Name:  &ast.Identifier{Value: "value"},
			Value: &ast.InvocationExpression{Function: &ast.Identifier{Value: "unknown"}},
		},
		&ast.WhileStatement{
			Condition: &ast.InvocationExpression{Function: &ast.Identifier{Value: "condition"}},
			Body: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.AssignmentStatement{
					Name:  &ast.Identifier{Value: "value"},
					Value: &ast.InvocationExpression{Function: &ast.Identifier{Value: "step"}},
				},
			}},
		},
	}}}
	facts := deriveGeneralizationFacts(polymorphicIdentityType(), block, tc.env)
	if !facts.Has(GeneralizationEffectfulCapture) || !facts.Has(GeneralizationUnknownAuthority) {
		t.Fatalf("executed block facts = %v", facts)
	}
}

func TestNamedGenericFunctionUnsafeBodyRemainsMonomorphic(t *testing.T) {
	tc := New(nilObjectEnvironment())
	fn := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "unsafeIdentity"},
		TypeParams: []*ast.TypeParameter{{
			Name: &ast.Identifier{Value: "T"},
		}},
		Parameters: []*ast.FunctionParameter{{
			Name: &ast.Identifier{Value: "x"},
			Type: &ast.Identifier{Value: "T"},
		}},
		ReturnType: &ast.Identifier{Value: "T"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.UnsafeBlock{Body: &ast.BlockStatement{}},
			&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "x"}},
		}}},
	}
	tc.checkFunctionStatement(fn)
	scheme, ok := tc.env.Get("unsafeIdentity")
	if !ok || scheme == nil {
		t.Fatal("named function was not bound")
	}
	if len(scheme.TypeVars) != 0 {
		t.Fatalf("unsafe named closure generalized to %#v", scheme.TypeVars)
	}
}

func TestStatelessBuiltinDoesNotBecomeForwardCapture(t *testing.T) {
	tc := New(nilObjectEnvironment())
	fn := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "helper"},
		Body: &ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "i64"},
			Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
		},
	}
	if facts := functionStatementCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("stateless builtin was treated as captured authority: %v", facts)
	}
}

func TestForwardCalleeAuthorityBlocksEarlierGenericCaller(t *testing.T) {
	tc := New(nilObjectEnvironment())
	caller := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "caller"},
		TypeParams: []*ast.TypeParameter{{
			Name: &ast.Identifier{Value: "T"},
		}},
		Parameters: []*ast.FunctionParameter{{
			Name: &ast.Identifier{Value: "x"},
			Type: &ast.Identifier{Value: "T"},
		}},
		ReturnType: &ast.Identifier{Value: "T"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.InvocationExpression{
				Function: &ast.Identifier{Value: "helper"},
			}},
			&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "x"}},
		}}},
	}
	helper := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "helper"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.UnsafeBlock{Body: &ast.BlockStatement{}},
		}}},
	}

	tc.CheckProgram(&ast.Program{Statements: []ast.Statement{caller, helper}})
	if len(tc.Errors()) != 0 {
		t.Fatalf("program failed to type-check: %v", tc.Errors())
	}
	scheme, ok := tc.env.Get("caller")
	if !ok || scheme == nil {
		t.Fatal("caller was not bound")
	}
	if len(scheme.TypeVars) != 0 {
		t.Fatalf("caller through unresolved forward callee generalized to %#v", scheme.TypeVars)
	}
	if scheme.GeneralizationBarriers&GeneralizationUnsafeAssumption == 0 {
		t.Fatalf("caller lost the forward-callee authority barrier: %v", scheme.GeneralizationBarriers)
	}
}

func TestSafeForwardCalleePreservesEarlierGenericCaller(t *testing.T) {
	tc := New(nilObjectEnvironment())
	caller := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "caller"},
		TypeParams: []*ast.TypeParameter{{
			Name: &ast.Identifier{Value: "T"},
		}},
		Parameters: []*ast.FunctionParameter{{
			Name: &ast.Identifier{Value: "x"},
			Type: &ast.Identifier{Value: "T"},
		}},
		ReturnType: &ast.Identifier{Value: "T"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.InvocationExpression{
				Function: &ast.Identifier{Value: "helper"},
			}},
			&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "x"}},
		}}},
	}
	helper := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "helper"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{}},
	}

	tc.CheckProgram(&ast.Program{Statements: []ast.Statement{caller, helper}})
	if len(tc.Errors()) != 0 {
		t.Fatalf("program failed to type-check: %v", tc.Errors())
	}
	scheme, ok := tc.env.Get("caller")
	if !ok || scheme == nil {
		t.Fatal("caller was not bound")
	}
	if len(scheme.TypeVars) != 1 {
		t.Fatalf("safe forward callee blocked caller quantification: %#v", scheme.TypeVars)
	}

	before := len(tc.Errors())
	for _, argument := range []ast.Expression{
		&ast.IntegerLiteral{Value: 1},
		&ast.StringLiteral{Value: "ok"},
	} {
		if result := tc.checkInvocationExpression(&ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "caller"},
			Arguments: []ast.Expression{argument},
		}); result == nil {
			t.Fatal("safe generic caller invocation failed")
		}
	}
	if len(tc.Errors()) != before {
		t.Fatalf("safe generic caller was not reusable: %v", tc.Errors()[before:])
	}
}

func TestGenericCalleeParticipatesInForwardBarrierFixedPoint(t *testing.T) {
	tc := New(nilObjectEnvironment())
	helper := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "genericHelper"},
		TypeParams: []*ast.TypeParameter{{
			Name: &ast.Identifier{Value: "U"},
		}},
		Parameters: []*ast.FunctionParameter{{
			Name: &ast.Identifier{Value: "value"},
			Type: &ast.Identifier{Value: "U"},
		}},
		ReturnType: &ast.Identifier{Value: "U"},
		Body:       &ast.Identifier{Value: "value"},
	}
	caller := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "caller"},
		TypeParams: []*ast.TypeParameter{{
			Name: &ast.Identifier{Value: "T"},
		}},
		Parameters: []*ast.FunctionParameter{{
			Name: &ast.Identifier{Value: "x"},
			Type: &ast.Identifier{Value: "T"},
		}},
		ReturnType: &ast.Identifier{Value: "T"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.InvocationExpression{
				Function: &ast.Identifier{Value: "bridge"},
			}},
			&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "x"}},
		}}},
	}
	bridge := &ast.FunctionStatement{
		Name:       &ast.Identifier{Value: "bridge"},
		ReturnType: &ast.Identifier{Value: "int"},
		Body: &ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "genericHelper"},
			Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
		},
	}

	tc.CheckProgram(&ast.Program{Statements: []ast.Statement{helper, caller, bridge}})
	if len(tc.Errors()) != 0 {
		t.Fatalf("program failed to type-check: %v", tc.Errors())
	}
	scheme, ok := tc.env.Get("caller")
	if !ok || scheme == nil || len(scheme.TypeVars) != 1 {
		t.Fatalf("generic callee made safe forward chain monomorphic: %#v", scheme)
	}

	before := len(tc.Errors())
	for _, argument := range []ast.Expression{
		&ast.IntegerLiteral{Value: 1},
		&ast.StringLiteral{Value: "ok"},
	} {
		if result := tc.checkInvocationExpression(&ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "caller"},
			Arguments: []ast.Expression{argument},
		}); result == nil {
			t.Fatal("safe generic caller invocation failed")
		}
	}
	if len(tc.Errors()) != before {
		t.Fatalf("safe generic forward chain was not reusable: %v", tc.Errors()[before:])
	}
}

func TestBlockedSchemePersistsFirstCallSubstitution(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	scheme := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", scheme)

	first := &ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "blocked"},
		Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
	}
	if got := tc.checkInvocationExpression(first); got == nil || !got.Equals(&PrimitiveType{Name: "int"}) {
		t.Fatalf("first call type = %v, want int", got)
	}
	if got := scheme.Monomorphic.Apply(v); !got.Equals(&PrimitiveType{Name: "int"}) {
		t.Fatalf("persistent solution = %v, want int", got)
	}

	before := len(tc.Errors())
	second := &ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "blocked"},
		Arguments: []ast.Expression{&ast.StringLiteral{Value: "different"}},
	}
	tc.checkInvocationExpression(second)
	if len(tc.Errors()) == before {
		t.Fatal("second call with a different type reused blocked binding polymorphically")
	}
}

func TestBlockedSchemePersistsThroughHigherOrderArguments(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	blocked := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", blocked)
	tc.env.SetType("takesInt", &FunctionType{
		Parameters: []Type{&FunctionType{
			Parameters: []Type{&PrimitiveType{Name: "int"}},
			ReturnType: &PrimitiveType{Name: "int"},
		}},
		ReturnType: &UnitType{},
	})
	tc.env.SetType("takesString", &FunctionType{
		Parameters: []Type{&FunctionType{
			Parameters: []Type{&StringType{}},
			ReturnType: &StringType{},
		}},
		ReturnType: &UnitType{},
	})

	first := &ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "takesInt"},
		Arguments: []ast.Expression{&ast.Identifier{Value: "blocked"}},
	}
	tc.checkInvocationExpression(first)
	if got := blocked.Monomorphic.Apply(v); !got.Equals(&PrimitiveType{Name: "int"}) {
		t.Fatalf("higher-order persistent solution = %v, want int", got)
	}

	before := len(tc.Errors())
	second := &ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "takesString"},
		Arguments: []ast.Expression{&ast.Identifier{Value: "blocked"}},
	}
	tc.checkInvocationExpression(second)
	if len(tc.Errors()) == before {
		t.Fatal("indirect uses specialized one blocked binding at incompatible types")
	}
}

func TestBlockedSchemeCannotBeRegeneralizedByAlias(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	blocked := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", blocked)
	tc.checkVariableDeclaration(&ast.VariableDeclaration{
		Name:  &ast.Identifier{Value: "alias"},
		Value: &ast.Identifier{Value: "blocked"},
	})
	alias, ok := tc.env.Get("alias")
	if !ok || alias == nil || len(alias.TypeVars) != 0 {
		t.Fatal("alias reintroduced quantification for the blocked scheme")
	}

	tc.checkInvocationExpression(&ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "alias"},
		Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
	})
	before := len(tc.Errors())
	tc.checkInvocationExpression(&ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "blocked"},
		Arguments: []ast.Expression{&ast.StringLiteral{Value: "different"}},
	})
	if len(tc.Errors()) == before {
		t.Fatal("alias re-generalized a blocked binding")
	}
}

func TestBlockedConstrainedSchemeReusesPersistentBinding(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	scheme := makeMonomorphicScheme(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		[]Constraint{{Var: "T"}},
	)
	tc.env.Set("blockedConstrained", scheme)
	call := func() {
		tc.checkInvocationExpression(&ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "blockedConstrained"},
			Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
		})
	}
	call()
	before := len(tc.Errors())
	call()
	if len(tc.Errors()) != before {
		t.Fatalf("second constrained use rejected stored T = int: %v", tc.Errors()[before:])
	}
}

func TestBlockedSpanInstantiationPreservesSpanIdentity(t *testing.T) {
	element := NewUnifier().FreshTypeVar("T")
	span := &ArrayType{ElementType: element, Length: -1, IsSpan: true}
	scheme := GeneralizeWithFacts(
		span,
		NewTypeEnvironment(),
		GeneralizationFacts{Barriers: GeneralizationRegionBound},
	)
	got, ok := Instantiate(scheme, NewUnifier()).(*ArrayType)
	if !ok || !got.IsSpan || got.IsSlice || got.Length != -1 {
		t.Fatalf("blocked span instantiated as %#v", got)
	}
}

func TestMatchArmBindingIsNotAnOuterCapture(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.SetType("item", &ArrayType{
		ElementType: &PrimitiveType{Name: "u8"},
		Length:      -1,
		IsSpan:      true,
	})
	fn := &ast.FunctionLiteral{
		Arguments: []*ast.Identifier{{Value: "value"}},
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.MatchExpression{
				Scrutinee: &ast.Identifier{Value: "value"},
				Arms: []*ast.MatchArm{{
					Pattern: &ast.BindingPattern{Name: &ast.Identifier{Value: "item"}},
					Body:    &ast.Identifier{Value: "item"},
				}},
			}},
		}},
	}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("match-local binder was classified as outer capture: %v", facts)
	}
}

func TestSelectorNameIsNotAnOuterCapture(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.SetType("field", &ArrayType{
		ElementType: &PrimitiveType{Name: "u8"},
		Length:      -1,
		IsSpan:      true,
	})
	fn := &ast.FunctionLiteral{
		Arguments: []*ast.Identifier{{Value: "record"}},
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.IndexExpression{
				Token: token.Token{Literal: "."},
				Left:  &ast.Identifier{Value: "record"},
				Index: &ast.Identifier{Value: "field"},
			}},
		}},
	}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("selector name was classified as outer capture: %v", facts)
	}
}

func TestSelectorNameDoesNotPropagateInitializerBarrier(t *testing.T) {
	tc := New(nilObjectEnvironment())
	selectorBinding := GeneralizeWithFacts(
		polymorphicIdentityType(),
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationMutableAuthority},
	)
	tc.env.Set("field", selectorBinding)
	projection := &ast.IndexExpression{
		Token: token.Token{Literal: "."},
		Left:  &ast.Identifier{Value: "record"},
		Index: &ast.Identifier{Value: "field"},
	}
	if facts := deriveGeneralizationFacts(polymorphicIdentityType(), projection, tc.env); !facts.Safe() {
		t.Fatalf("selector name propagated an unrelated binding barrier: %v", facts)
	}
}

func TestInitializerLocalBindingsDoNotResolveOuterBarriers(t *testing.T) {
	tc := New(nilObjectEnvironment())
	for _, name := range []string{"localValue", "localFunction"} {
		tc.env.Set(name, GeneralizeWithFacts(
			polymorphicIdentityType(),
			tc.env,
			GeneralizationFacts{Barriers: GeneralizationMutableAuthority},
		))
	}
	block := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.VariableDeclaration{
			Name:  &ast.Identifier{Value: "localValue"},
			Value: &ast.IntegerLiteral{Value: 1},
		},
		&ast.FunctionStatement{
			Name: &ast.Identifier{Value: "localFunction"},
			Body: &ast.IntegerLiteral{Value: 1},
		},
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "localValue"}},
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "localFunction"}},
	}}}
	if facts := deriveGeneralizationFacts(polymorphicIdentityType(), block, tc.env); !facts.Safe() {
		t.Fatalf("initializer-local binding resolved an outer barrier: %v", facts)
	}
}

func TestInitializerLocalAuthorityPropagatesThroughNamedCapture(t *testing.T) {
	tc := New(nilObjectEnvironment())
	block := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.VariableDeclaration{
			Name: &ast.Identifier{Value: "local"},
			Value: &ast.ArrayLiteral{Elements: []ast.Expression{
				&ast.IntegerLiteral{Value: 1},
			}},
		},
		&ast.FunctionStatement{
			Name: &ast.Identifier{Value: "inner"},
			Body: &ast.Identifier{Value: "local"},
		},
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "inner"}},
	}}}
	facts := deriveGeneralizationFacts(polymorphicIdentityType(), block, tc.env)
	if !facts.Has(GeneralizationMutableAuthority) {
		t.Fatalf("initializer-local authority was lost through named capture: %v", facts)
	}
}

func TestCompositeLocalAuthorityPropagatesThroughCapture(t *testing.T) {
	array := func() ast.Expression {
		return &ast.ArrayLiteral{Elements: []ast.Expression{
			&ast.IntegerLiteral{Value: 1},
		}}
	}
	cases := map[string]ast.Expression{
		"block": &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: array()},
		}}},
		"match": &ast.MatchExpression{
			Scrutinee: &ast.Boolean{Value: true},
			Arms: []*ast.MatchArm{{
				Pattern: &ast.BindingPattern{Name: &ast.Identifier{Value: "value"}},
				Body:    array(),
			}},
		},
		"variant": &ast.VariantExpression{Payload: array()},
	}
	for name, value := range cases {
		t.Run(name, func(t *testing.T) {
			tc := New(nilObjectEnvironment())
			block := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.VariableDeclaration{
					Name:  &ast.Identifier{Value: "local"},
					Value: value,
				},
				&ast.FunctionStatement{
					Name: &ast.Identifier{Value: "inner"},
					Body: &ast.Identifier{Value: "local"},
				},
				&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "inner"}},
			}}}
			facts := deriveGeneralizationFacts(polymorphicIdentityType(), block, tc.env)
			if !facts.Has(GeneralizationMutableAuthority) {
				t.Fatalf("composite local authority was lost through capture: %v", facts)
			}
		})
	}
}

func TestMatchBinderShadowsOuterBarrierThroughLocalAlias(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.Set("item", GeneralizeWithFacts(
		polymorphicIdentityType(),
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationMutableAuthority},
	))
	match := &ast.MatchExpression{
		Scrutinee: &ast.Boolean{Value: true},
		Arms: []*ast.MatchArm{{
			Pattern: &ast.BindingPattern{Name: &ast.Identifier{Value: "item"}},
			Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.VariableDeclaration{
					Name:  &ast.Identifier{Value: "alias"},
					Value: &ast.Identifier{Value: "item"},
				},
				&ast.FunctionStatement{
					Name: &ast.Identifier{Value: "inner"},
					Body: &ast.Identifier{Value: "alias"},
				},
				&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "inner"}},
			}}},
		}},
	}
	if facts := deriveGeneralizationFacts(polymorphicIdentityType(), match, tc.env); !facts.Safe() {
		t.Fatalf("match binder alias resolved an unrelated outer barrier: %v", facts)
	}
}

func TestAssignedLocalAuthorityPropagatesThroughCapture(t *testing.T) {
	tc := New(nilObjectEnvironment())
	block := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.VariableDeclaration{Name: &ast.Identifier{Value: "local"}},
		&ast.AssignmentStatement{
			Name: &ast.Identifier{Value: "local"},
			Value: &ast.ArrayLiteral{Elements: []ast.Expression{
				&ast.IntegerLiteral{Value: 1},
			}},
		},
		&ast.FunctionStatement{
			Name: &ast.Identifier{Value: "inner"},
			Body: &ast.Identifier{Value: "local"},
		},
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "inner"}},
	}}}
	facts := deriveGeneralizationFacts(polymorphicIdentityType(), block, tc.env)
	if !facts.Has(GeneralizationMutableAuthority) {
		t.Fatalf("assigned local authority was lost through capture: %v", facts)
	}
}

func TestNestedAssignmentUpdatesInheritedLocalAuthority(t *testing.T) {
	assignment := func() *ast.AssignmentStatement {
		return &ast.AssignmentStatement{
			Name: &ast.Identifier{Value: "local"},
			Value: &ast.ArrayLiteral{Elements: []ast.Expression{
				&ast.IntegerLiteral{Value: 1},
			}},
		}
	}
	cases := map[string]ast.Statement{
		"block": &ast.BlockStatement{Statements: []ast.Statement{assignment()}},
		"while": &ast.WhileStatement{
			Condition: &ast.Boolean{Value: true},
			Body:      &ast.BlockStatement{Statements: []ast.Statement{assignment()}},
		},
	}
	for name, nested := range cases {
		t.Run(name, func(t *testing.T) {
			tc := New(nilObjectEnvironment())
			block := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.VariableDeclaration{Name: &ast.Identifier{Value: "local"}},
				nested,
				&ast.FunctionStatement{
					Name: &ast.Identifier{Value: "inner"},
					Body: &ast.Identifier{Value: "local"},
				},
				&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "inner"}},
			}}}
			facts := deriveGeneralizationFacts(polymorphicIdentityType(), block, tc.env)
			if !facts.Has(GeneralizationMutableAuthority) {
				t.Fatalf("nested assignment update was lost at scope exit: %v", facts)
			}
		})
	}
}

func TestOuterAssignmentBlocksGeneralization(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.Set("outer", &TypeScheme{Type: &PrimitiveType{Name: "int"}})
	block := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.AssignmentStatement{
			Name:  &ast.Identifier{Value: "outer"},
			Value: &ast.IntegerLiteral{Value: 1},
		},
	}}}
	facts := deriveGeneralizationFacts(polymorphicIdentityType(), block, tc.env)
	if !facts.Has(GeneralizationMutableAuthority) || !facts.Has(GeneralizationEffectfulCapture) {
		t.Fatalf("outer assignment did not block generalization: %v", facts)
	}
}

func TestNestedBlockBindingsDoNotLeakIntoCaptureScope(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.Set("item", GeneralizeWithFacts(
		polymorphicIdentityType(),
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationMutableAuthority},
	))
	fn := &ast.FunctionLiteral{Body: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.BlockStatement{Statements: []ast.Statement{
			&ast.VariableDeclaration{
				Name:  &ast.Identifier{Value: "item"},
				Value: &ast.IntegerLiteral{Value: 1},
			},
		}},
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "item"}},
	}}}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Has(GeneralizationMutableAuthority) {
		t.Fatalf("nested block binding leaked and hid an outer capture: %v", facts)
	}
}

func TestMethodSelectorPropagatesResolvedSchemeBarriers(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.SetType("receiver", &ADTType{Name: "Box"})
	tc.env.Set("Box::touch", &TypeScheme{
		Type:                   &FunctionType{ReturnType: &UnitType{}},
		GeneralizationBarriers: GeneralizationUnsafeAssumption,
	})
	call := &ast.InvocationExpression{
		Function: &ast.IndexExpression{
			Token: token.Token{Literal: "."},
			Left:  &ast.Identifier{Value: "receiver"},
			Index: &ast.Identifier{Value: "touch"},
		},
	}
	fn := &ast.FunctionLiteral{
		Arguments: []*ast.Identifier{{Value: "receiver"}},
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: call},
		}},
	}
	facts := functionCaptureFacts(fn, tc.env)
	if !facts.Has(GeneralizationUnsafeAssumption) {
		t.Fatalf("resolved method barrier did not propagate: %v", facts)
	}
	if facts.Has(GeneralizationUnknownAuthority) {
		t.Fatalf("resolved method was treated as unknown: %v", facts)
	}
}

func TestSafeResolvedMethodSelectorDoesNotBlockGeneralization(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.SetType("receiver", &ADTType{Name: "Box"})
	tc.env.Set("Box::inspect", &TypeScheme{
		Type: &FunctionType{ReturnType: &UnitType{}},
	})
	fn := &ast.FunctionLiteral{
		Arguments: []*ast.Identifier{{Value: "receiver"}},
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.InvocationExpression{
				Function: &ast.IndexExpression{
					Token: token.Token{Literal: "."},
					Left:  &ast.Identifier{Value: "receiver"},
					Index: &ast.Identifier{Value: "inspect"},
				},
			}},
		}},
	}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("safe resolved method blocked generalization: %v", facts)
	}
}

func TestNestedClosureInheritsMatchArmBindingScope(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.SetType("item", &ArrayType{
		ElementType: &PrimitiveType{Name: "u8"},
		Length:      -1,
		IsSpan:      true,
	})
	nested := &ast.FunctionLiteral{Body: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "item"}},
	}}}
	fn := &ast.FunctionLiteral{
		Arguments: []*ast.Identifier{{Value: "value"}},
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.MatchExpression{
				Scrutinee: &ast.Identifier{Value: "value"},
				Arms: []*ast.MatchArm{{
					Pattern: &ast.BindingPattern{Name: &ast.Identifier{Value: "item"}},
					Body:    nested,
				}},
			}},
		}},
	}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("nested closure lost match-arm binder scope: %v", facts)
	}
}

func TestRejectedCallDoesNotCommitPartialMonomorphicBindings(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	scheme := GeneralizeWithFacts(
		&FunctionType{
			Parameters: []Type{v, &BoolType{}},
			ReturnType: v,
		},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blockedPair", scheme)

	tc.checkInvocationExpression(&ast.InvocationExpression{
		Function: &ast.Identifier{Value: "blockedPair"},
		Arguments: []ast.Expression{
			&ast.IntegerLiteral{Value: 1},
			&ast.StringLiteral{Value: "not bool"},
		},
	})
	if _, fixed := scheme.Monomorphic[v]; fixed {
		t.Fatal("rejected call committed a partial monomorphic solution")
	}

	before := len(tc.Errors())
	result := tc.checkInvocationExpression(&ast.InvocationExpression{
		Function: &ast.Identifier{Value: "blockedPair"},
		Arguments: []ast.Expression{
			&ast.StringLiteral{Value: "valid"},
			&ast.Boolean{Value: true},
		},
	})
	if result == nil || !result.Equals(&StringType{}) {
		t.Fatalf("valid later call type = %v, want string", result)
	}
	if len(tc.Errors()) != before {
		t.Fatalf("valid later call cascaded after rejected call: %v", tc.Errors()[before:])
	}
}

func TestDirectFunctionReferenceAddsNoCaptureBarrier(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.SetType("helper", &FunctionType{
		Parameters: []Type{&PrimitiveType{Name: "int"}},
		ReturnType: &PrimitiveType{Name: "int"},
	})
	fn := &ast.FunctionLiteral{Body: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.ExpressionStatement{Expression: &ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "helper"},
			Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
		}},
	}}}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("direct function reference was classified as capture: %v", facts)
	}
}

func TestArgumentDiagnosticPreventsMonomorphicCommit(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	scheme := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", scheme)
	badArray := &ast.ArrayLiteral{
		Type: &ast.IndexExpression{
			Left:  &ast.Identifier{Value: "int"},
			Index: &ast.IntegerLiteral{Value: 1},
		},
		Elements: []ast.Expression{&ast.StringLiteral{Value: "bad element"}},
	}
	tc.checkInvocationExpression(&ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "blocked"},
		Arguments: []ast.Expression{badArray},
	})
	if _, fixed := scheme.Monomorphic[v]; fixed {
		t.Fatal("argument diagnostic still committed a monomorphic solution")
	}

	before := len(tc.Errors())
	result := tc.checkInvocationExpression(&ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "blocked"},
		Arguments: []ast.Expression{&ast.StringLiteral{Value: "valid"}},
	})
	if result == nil || !result.Equals(&StringType{}) {
		t.Fatalf("later valid call type = %v, want string", result)
	}
	if len(tc.Errors()) != before {
		t.Fatalf("later valid call cascaded: %v", tc.Errors()[before:])
	}
}

func TestNestedNamedFunctionInheritsMatchArmBindingScope(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.SetType("item", &ArrayType{
		ElementType: &PrimitiveType{Name: "u8"},
		Length:      -1,
		IsSpan:      true,
	})
	inner := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "inner"},
		Body: &ast.Identifier{Value: "item"},
	}
	armBody := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		inner,
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "inner"}},
	}}}
	fn := &ast.FunctionLiteral{
		Arguments: []*ast.Identifier{{Value: "value"}},
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.MatchExpression{
				Scrutinee: &ast.Identifier{Value: "value"},
				Arms: []*ast.MatchArm{{
					Pattern: &ast.BindingPattern{Name: &ast.Identifier{Value: "item"}},
					Body:    armBody,
				}},
			}},
		}},
	}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("nested named function lost match-arm binder scope: %v", facts)
	}
}

func TestAnnotatedAliasCommitsBlockedSpecialization(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	blocked := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", blocked)
	tc.env.SetType("IntFn", &FunctionType{
		Parameters: []Type{&PrimitiveType{Name: "int"}},
		ReturnType: &PrimitiveType{Name: "int"},
	})
	tc.env.SetType("StringFn", &FunctionType{
		Parameters: []Type{&StringType{}},
		ReturnType: &StringType{},
	})

	tc.checkVariableDeclaration(&ast.VariableDeclaration{
		Name:  &ast.Identifier{Value: "intAlias"},
		Type:  &ast.Identifier{Value: "IntFn"},
		Value: &ast.Identifier{Value: "blocked"},
	})
	if got := blocked.Monomorphic.Apply(v); !got.Equals(&PrimitiveType{Name: "int"}) {
		t.Fatalf("annotated alias solution = %v, want int", got)
	}
	before := len(tc.Errors())
	tc.checkVariableDeclaration(&ast.VariableDeclaration{
		Name:  &ast.Identifier{Value: "stringAlias"},
		Type:  &ast.Identifier{Value: "StringFn"},
		Value: &ast.Identifier{Value: "blocked"},
	})
	if len(tc.Errors()) == before {
		t.Fatal("conflicting annotated alias reused blocked binding polymorphically")
	}
}

func TestIndependentBlockedSchemesDoNotPolluteConstraints(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v1 := NewUnifier().FreshTypeVar("T")
	v2 := NewUnifier().FreshTypeVar("T")
	first := makeMonomorphicScheme(
		&FunctionType{Parameters: []Type{v1}, ReturnType: v1},
		[]Constraint{{Var: "T"}},
	)
	second := makeMonomorphicScheme(
		&FunctionType{Parameters: []Type{v2}, ReturnType: v2},
		[]Constraint{{Var: "T"}},
	)
	tc.env.Set("first", first)
	tc.env.Set("second", second)
	intFn := &FunctionType{
		Parameters: []Type{&PrimitiveType{Name: "int"}},
		ReturnType: &PrimitiveType{Name: "int"},
	}
	tc.env.SetType("takesBoth", &FunctionType{
		Parameters: []Type{intFn, intFn},
		ReturnType: &UnitType{},
	})
	tc.checkInvocationExpression(&ast.InvocationExpression{
		Function: &ast.Identifier{Value: "takesBoth"},
		Arguments: []ast.Expression{
			&ast.Identifier{Value: "first"},
			&ast.Identifier{Value: "second"},
		},
	})
	before := len(tc.Errors())
	for _, name := range []string{"first", "second"} {
		tc.checkInvocationExpression(&ast.InvocationExpression{
			Function:  &ast.Identifier{Value: name},
			Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
		})
	}
	if len(tc.Errors()) != before {
		t.Fatalf("independent same-named binders polluted constraints: %v", tc.Errors()[before:])
	}
}

func TestBlockedLocalDoesNotCaptureEnclosingTypeBinder(t *testing.T) {
	env := NewTypeEnvironment()
	enclosing := NewUnifier().FreshTypeVar("T")
	env.SetType("T", enclosing)
	localType := &ArrayType{
		ElementType: enclosing,
		Length:      1,
	}
	scheme := GeneralizeWithFacts(
		localType,
		env,
		GeneralizationFacts{Barriers: GeneralizationMutableAuthority},
	)
	if enclosing.Monomorphic != nil {
		t.Fatal("blocked local tagged an enclosing generic binder")
	}
	if scheme.Monomorphic != nil {
		t.Fatal("scheme gained persistent state without a local free variable")
	}

	functionType := &FunctionType{
		Parameters: []Type{enclosing},
		ReturnType: enclosing,
	}
	generalized := Generalize(functionType, NewTypeEnvironment())
	if len(generalized.TypeVars) != 1 || generalized.Monomorphic != nil {
		t.Fatalf("enclosing function binder was not reusable: %#v", generalized)
	}
}

func TestCaptureMetadataSurvivesWithoutLocalFreeBinders(t *testing.T) {
	env := NewTypeEnvironment()
	enclosing := NewUnifier().FreshTypeVar("T")
	env.SetType("T", enclosing)
	authorityFunction := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{enclosing}, ReturnType: enclosing},
		env,
		GeneralizationFacts{Barriers: GeneralizationMutableAuthority | GeneralizationRegionBound},
	)
	if authorityFunction.Monomorphic != nil {
		t.Fatal("enclosing binder incorrectly gained persistent state")
	}
	if authorityFunction.GeneralizationBarriers == 0 {
		t.Fatal("authority metadata was discarded with empty local free-variable set")
	}
	env.Set("authorityFunction", authorityFunction)

	fn := &ast.FunctionLiteral{Body: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "authorityFunction"}},
	}}}
	facts := functionCaptureFacts(fn, env)
	if !facts.Has(GeneralizationMutableAuthority) || !facts.Has(GeneralizationRegionBound) {
		t.Fatalf("transitive function capture lost authority metadata: %v", facts)
	}
}

func TestMatchInitializerDoesNotPropagateShadowedBarrierMetadata(t *testing.T) {
	tc := New(nilObjectEnvironment())
	outer := GeneralizeWithFacts(
		polymorphicIdentityType(),
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationMutableAuthority},
	)
	tc.env.Set("item", outer)
	match := &ast.MatchExpression{
		Scrutinee: &ast.Boolean{Value: true},
		Arms: []*ast.MatchArm{{
			Pattern: &ast.BindingPattern{Name: &ast.Identifier{Value: "item"}},
			Body:    &ast.Identifier{Value: "item"},
		}},
	}
	if facts := deriveGeneralizationFacts(polymorphicIdentityType(), match, tc.env); !facts.Safe() {
		t.Fatalf("match-local identifier propagated outer barrier metadata: %v", facts)
	}
}

func TestMatchInitializerPassesBinderScopeIntoNestedFunctions(t *testing.T) {
	tc := New(nilObjectEnvironment())
	outer := GeneralizeWithFacts(
		polymorphicIdentityType(),
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationMutableAuthority},
	)
	tc.env.Set("item", outer)

	namedBody := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.FunctionStatement{
			Name: &ast.Identifier{Value: "inner"},
			Body: &ast.Identifier{Value: "item"},
		},
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "inner"}},
	}}}
	literalBody := &ast.FunctionLiteral{Body: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "item"}},
	}}}

	for name, body := range map[string]ast.Expression{
		"named":   namedBody,
		"literal": literalBody,
	} {
		t.Run(name, func(t *testing.T) {
			match := &ast.MatchExpression{
				Scrutinee: &ast.Boolean{Value: true},
				Arms: []*ast.MatchArm{{
					Pattern: &ast.BindingPattern{Name: &ast.Identifier{Value: "item"}},
					Body:    body,
				}},
			}
			if facts := deriveGeneralizationFacts(polymorphicIdentityType(), match, tc.env); !facts.Safe() {
				t.Fatalf("nested function lost match-arm binder scope: %v", facts)
			}
		})
	}
}

func TestFailedAnnotatedDeclarationRollsBackNestedCall(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	blocked := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", blocked)
	tc.checkVariableDeclaration(&ast.VariableDeclaration{
		Name: &ast.Identifier{Value: "bad"},
		Type: &ast.Identifier{Value: "string"},
		Value: &ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "blocked"},
			Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
		},
	})
	if _, fixed := blocked.Monomorphic[v]; fixed {
		t.Fatal("failed enclosing declaration committed nested specialization")
	}
	before := len(tc.Errors())
	result := tc.checkInvocationExpression(&ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "blocked"},
		Arguments: []ast.Expression{&ast.StringLiteral{Value: "valid"}},
	})
	if result == nil || !result.Equals(&StringType{}) {
		t.Fatalf("later valid call type = %v, want string", result)
	}
	if len(tc.Errors()) != before {
		t.Fatalf("later valid call cascaded: %v", tc.Errors()[before:])
	}
}

func TestSiblingUsesSharePendingMonomorphicSpecialization(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	blocked := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", blocked)
	tc.env.SetType("consume", &FunctionType{
		Parameters: []Type{
			&PrimitiveType{Name: "int"},
			&StringType{},
		},
		ReturnType: &UnitType{},
	})
	callBlocked := func(argument ast.Expression) ast.Expression {
		return &ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "blocked"},
			Arguments: []ast.Expression{argument},
		}
	}
	before := len(tc.Errors())
	tc.checkInvocationExpression(&ast.InvocationExpression{
		Function: &ast.Identifier{Value: "consume"},
		Arguments: []ast.Expression{
			callBlocked(&ast.IntegerLiteral{Value: 1}),
			callBlocked(&ast.StringLiteral{Value: "conflict"}),
		},
	})
	if len(tc.Errors()) == before {
		t.Fatal("sibling uses specialized one blocked binding incompatibly")
	}
	if _, fixed := blocked.Monomorphic[v]; fixed {
		t.Fatal("failed sibling transaction committed a specialization")
	}
}

func TestAssertFailureRollsBackNestedSpecialization(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	blocked := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", blocked)
	tc.checkInvocationExpression(&ast.InvocationExpression{
		Function: &ast.Identifier{Value: "assert"},
		Arguments: []ast.Expression{
			&ast.InvocationExpression{
				Function:  &ast.Identifier{Value: "blocked"},
				Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
			},
		},
	})
	if _, fixed := blocked.Monomorphic[v]; fixed {
		t.Fatal("failed assert committed nested specialization")
	}
	before := len(tc.Errors())
	result := tc.checkInvocationExpression(&ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "blocked"},
		Arguments: []ast.Expression{&ast.StringLiteral{Value: "valid"}},
	})
	if result == nil || !result.Equals(&StringType{}) {
		t.Fatalf("later valid call type = %v, want string", result)
	}
	if len(tc.Errors()) != before {
		t.Fatalf("later valid call cascaded: %v", tc.Errors()[before:])
	}
}

func TestRepeatedBlockedArgumentsReconcileWithinCall(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	blocked := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", blocked)
	tc.env.SetType("consumeFunctions", &FunctionType{
		Parameters: []Type{
			&FunctionType{
				Parameters: []Type{&PrimitiveType{Name: "int"}},
				ReturnType: &PrimitiveType{Name: "int"},
			},
			&FunctionType{
				Parameters: []Type{&StringType{}},
				ReturnType: &StringType{},
			},
		},
		ReturnType: &UnitType{},
	})
	before := len(tc.Errors())
	tc.checkInvocationExpression(&ast.InvocationExpression{
		Function: &ast.Identifier{Value: "consumeFunctions"},
		Arguments: []ast.Expression{
			&ast.Identifier{Value: "blocked"},
			&ast.Identifier{Value: "blocked"},
		},
	})
	if len(tc.Errors()) == before {
		t.Fatal("repeated blocked arguments accepted incompatible specializations")
	}
	if _, fixed := blocked.Monomorphic[v]; fixed {
		t.Fatal("failed repeated-argument call committed specialization")
	}
}

func TestFailedAssignmentRollsBackNestedSpecialization(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.SetType("target", &StringType{})
	v := NewUnifier().FreshTypeVar("T")
	blocked := GeneralizeWithFacts(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		tc.env,
		GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption},
	)
	tc.env.Set("blocked", blocked)
	tc.checkAssignmentStatement(&ast.AssignmentStatement{
		Name: &ast.Identifier{Value: "target"},
		Value: &ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "blocked"},
			Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
		},
	})
	if _, fixed := blocked.Monomorphic[v]; fixed {
		t.Fatal("failed assignment committed nested specialization")
	}
	before := len(tc.Errors())
	result := tc.checkInvocationExpression(&ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "blocked"},
		Arguments: []ast.Expression{&ast.StringLiteral{Value: "valid"}},
	})
	if result == nil || !result.Equals(&StringType{}) {
		t.Fatalf("later valid call type = %v, want string", result)
	}
	if len(tc.Errors()) != before {
		t.Fatalf("later valid call cascaded: %v", tc.Errors()[before:])
	}
}

func TestSiblingConstrainedUsesSeePendingMonomorphicSpecialization(t *testing.T) {
	tc := New(nilObjectEnvironment())
	v := NewUnifier().FreshTypeVar("T")
	blocked := makeMonomorphicScheme(
		&FunctionType{Parameters: []Type{v}, ReturnType: v},
		[]Constraint{{Var: "T"}},
	)
	tc.env.Set("blocked", blocked)
	tc.env.SetType("consume", &FunctionType{
		Parameters: []Type{
			&PrimitiveType{Name: "int"},
			&PrimitiveType{Name: "int"},
		},
		ReturnType: &UnitType{},
	})
	callBlocked := func(value int64) ast.Expression {
		return &ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "blocked"},
			Arguments: []ast.Expression{&ast.IntegerLiteral{Value: value}},
		}
	}

	before := len(tc.Errors())
	result := tc.checkInvocationExpression(&ast.InvocationExpression{
		Function: &ast.Identifier{Value: "consume"},
		Arguments: []ast.Expression{
			callBlocked(1),
			callBlocked(2),
		},
	})
	if result == nil || !result.Equals(&UnitType{}) {
		t.Fatalf("sibling constrained call type = %v, want unit", result)
	}
	if len(tc.Errors()) != before {
		t.Fatalf("compatible sibling constrained calls failed: %v", tc.Errors()[before:])
	}
	if got := blocked.Monomorphic.Apply(v); !got.Equals(&PrimitiveType{Name: "int"}) {
		t.Fatalf("committed constrained specialization = %v, want int", got)
	}
}

func TestEscapedTypeVariableJoinsBlockedMonomorphicGroup(t *testing.T) {
	tc := New(nilObjectEnvironment())
	blockedVar := NewUnifier().FreshTypeVar("T")
	blocked := makeMonomorphicScheme(
		&FunctionType{Parameters: []Type{blockedVar}, ReturnType: blockedVar},
		nil,
	)
	tc.env.Set("blocked", blocked)

	polyVar := NewUnifier().FreshTypeVar("P")
	tc.env.Set("poly", Generalize(
		&FunctionType{Parameters: []Type{polyVar}, ReturnType: polyVar},
		tc.env,
	))
	intFn := &FunctionType{
		Parameters: []Type{&PrimitiveType{Name: "int"}},
		ReturnType: &PrimitiveType{Name: "int"},
	}
	stringFn := &FunctionType{
		Parameters: []Type{&StringType{}},
		ReturnType: &StringType{},
	}
	tc.env.Set("intIdentity", &TypeScheme{Type: intFn})
	tc.env.Set("stringIdentity", &TypeScheme{Type: stringFn})
	callBlocked := func(name string) Type {
		return tc.checkInvocationExpression(&ast.InvocationExpression{
			Function:  &ast.Identifier{Value: "blocked"},
			Arguments: []ast.Expression{&ast.Identifier{Value: name}},
		})
	}

	before := len(tc.Errors())
	if result := callBlocked("poly"); result == nil {
		t.Fatal("blocked binding rejected the initial polymorphic value")
	}
	if len(tc.Errors()) != before {
		t.Fatalf("initial polymorphic escape failed: %v", tc.Errors()[before:])
	}

	if result := callBlocked("intIdentity"); result == nil || !result.Equals(intFn) {
		t.Fatalf("escaped variable did not specialize to int identity: %v", result)
	}
	if len(tc.Errors()) != before {
		t.Fatalf("int specialization failed: %v", tc.Errors()[before:])
	}

	callBlocked("stringIdentity")
	if len(tc.Errors()) == before {
		t.Fatal("escaped variable reopened blocked binding at string identity")
	}
}

func TestBarredPredeclaredGenericIsPersistent(t *testing.T) {
	tc := New(object.NewEnvironment())
	fn := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "unsafeIdentity"},
		TypeParams: []*ast.TypeParameter{{
			Name: &ast.Identifier{Value: "T"},
		}},
		Parameters: []*ast.FunctionParameter{{
			Name: &ast.Identifier{Value: "value"},
			Type: &ast.Identifier{Value: "T"},
		}},
		ReturnType: &ast.Identifier{Value: "T"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{
			Statements: []ast.Statement{
				&ast.UnsafeBlock{Body: &ast.BlockStatement{}},
				&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "value"}},
			},
		}},
	}
	program := &ast.Program{Statements: []ast.Statement{fn}}
	tc.predeclareFunctionSignature(fn)
	tc.resolvePredeclaredFunctionBarriers(program)

	scheme, ok := tc.env.Get("unsafeIdentity")
	if !ok || scheme == nil {
		t.Fatal("barred generic was not predeclared")
	}
	if len(scheme.TypeVars) != 0 || scheme.Monomorphic == nil {
		t.Fatalf("barred predeclared scheme remained polymorphic: %#v", scheme)
	}

	first := Instantiate(scheme, NewUnifier()).(*FunctionType)
	binding := NewUnifier().Unify(first.Parameters[0], &PrimitiveType{Name: "i32"})
	if binding == nil {
		t.Fatal("first monomorphic use did not unify")
	}
	commitMonomorphicBindings(binding)

	tc.checkFunctionStatement(fn)
	finalized, ok := tc.env.Get("unsafeIdentity")
	if !ok || finalized != scheme {
		t.Fatal("function finalization replaced the persistent predeclared scheme")
	}

	second := Instantiate(finalized, NewUnifier()).(*FunctionType)
	if got := NewUnifier().Unify(second.Parameters[0], &StringType{}); got != nil {
		t.Fatalf("second incompatible use reopened barred generic: %v", got)
	}
}

func TestPredeclaredMethodCallDoesNotMonomorphizeSafeGeneric(t *testing.T) {
	box := &ast.ADTType{
		Name: &ast.Identifier{Value: "Box"},
		Variants: []*ast.ADTVariant{{
			Name: &ast.Identifier{Value: "Box"},
		}},
	}
	method := &ast.FunctionStatement{
		Receiver: &ast.FunctionParameter{
			Name: &ast.Identifier{Value: "self"},
			Type: &ast.Identifier{Value: "Box"},
		},
		Name:       &ast.Identifier{Value: "read"},
		ReturnType: &ast.Identifier{Value: "i32"},
		Body:       &ast.IntegerLiteral{Value: 0},
	}
	generic := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "keep"},
		TypeParams: []*ast.TypeParameter{{
			Name: &ast.Identifier{Value: "T"},
		}},
		Parameters: []*ast.FunctionParameter{
			{Name: &ast.Identifier{Value: "value"}, Type: &ast.Identifier{Value: "T"}},
			{Name: &ast.Identifier{Value: "box"}, Type: &ast.Identifier{Value: "Box"}},
		},
		ReturnType: &ast.Identifier{Value: "T"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.InvocationExpression{
				Function: &ast.IndexExpression{
					Token: token.Token{Literal: "."},
					Left:  &ast.Identifier{Value: "box"},
					Index: &ast.Identifier{Value: "read"},
				},
			}},
			&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "value"}},
		}}},
	}
	tc := New(nilObjectEnvironment())
	tc.CheckProgram(&ast.Program{Statements: []ast.Statement{box, method, generic}})
	scheme, ok := tc.env.Get("keep")
	if !ok || scheme == nil {
		t.Fatal("safe generic method caller was not registered")
	}
	if scheme.GeneralizationBarriers != 0 || len(scheme.TypeVars) != 1 {
		t.Fatalf("safe generic method caller became monomorphic: %#v", scheme)
	}
}

func TestCompilerLibraryCallDoesNotCreateCaptureBarrier(t *testing.T) {
	tc := New(nilObjectEnvironment())
	fn := &ast.FunctionLiteral{
		Arguments: []*ast.Identifier{{Value: "value"}},
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.InvocationExpression{
				Function: &ast.IndexExpression{
					Token: token.Token{Literal: "."},
					Left:  &ast.Identifier{Value: "arm64"},
					Index: &ast.Identifier{Value: "clz64"},
				},
				Arguments: []ast.Expression{&ast.Identifier{Value: "value"}},
			}},
		}},
	}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("compiler library namespace blocked generalization: %v", facts)
	}
}

func TestPredeclaredMethodParametersResolveMethodAuthority(t *testing.T) {
	box := &ast.ADTType{
		Name:     &ast.Identifier{Value: "Box"},
		Variants: []*ast.ADTVariant{{Name: &ast.Identifier{Value: "Box"}}},
	}
	read := &ast.FunctionStatement{
		Receiver: &ast.FunctionParameter{
			Name: &ast.Identifier{Value: "self"}, Type: &ast.Identifier{Value: "Box"},
		},
		Name:       &ast.Identifier{Value: "read"},
		ReturnType: &ast.Identifier{Value: "i32"},
		Body:       &ast.IntegerLiteral{Value: 0},
	}
	forward := &ast.FunctionStatement{
		Receiver: &ast.FunctionParameter{
			Name: &ast.Identifier{Value: "self"}, Type: &ast.Identifier{Value: "Box"},
		},
		Name: &ast.Identifier{Value: "forward"},
		Parameters: []*ast.FunctionParameter{{
			Name: &ast.Identifier{Value: "other"}, Type: &ast.Identifier{Value: "Box"},
		}},
		ReturnType: &ast.Identifier{Value: "i32"},
		Body: &ast.InvocationExpression{
			Function: &ast.IndexExpression{
				Token: token.Token{Literal: "."},
				Left:  &ast.Identifier{Value: "other"},
				Index: &ast.Identifier{Value: "read"},
			},
		},
	}
	tc := New(nilObjectEnvironment())
	program := &ast.Program{Statements: []ast.Statement{box, read, forward}}
	tc.CheckProgram(program)
	scheme, ok := tc.env.Get("Box::forward")
	if !ok || scheme == nil {
		t.Fatal("forwarding method was not registered")
	}
	if scheme.GeneralizationBarriers != 0 {
		t.Fatalf("typed method parameter retained unknown authority: %v", scheme.GeneralizationBarriers)
	}
}

func TestDeclaredLocalTypeResolvesMethodAuthority(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.Set("Box::read", &TypeScheme{
		Type: &FunctionType{ReturnType: &PrimitiveType{Name: "i32"}},
	})
	fn := &ast.FunctionLiteral{
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.VariableDeclaration{
				Name: &ast.Identifier{Value: "box"},
				Type: &ast.Identifier{Value: "Box"},
				Value: &ast.VariantExpression{
					TypeName: &ast.Identifier{Value: "Box"},
					Variant:  &ast.Identifier{Value: "Box"},
				},
			},
			&ast.ExpressionStatement{Expression: &ast.InvocationExpression{
				Function: &ast.IndexExpression{
					Token: token.Token{Literal: "."},
					Left:  &ast.Identifier{Value: "box"},
					Index: &ast.Identifier{Value: "read"},
				},
			}},
		}},
	}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("declared local method receiver blocked generalization: %v", facts)
	}
}

func TestExpressionReceiverResolvesMethodAuthority(t *testing.T) {
	tc := New(nilObjectEnvironment())
	tc.env.Set("makeBox", &TypeScheme{Type: &FunctionType{ReturnType: &ADTType{Name: "Box"}}})
	tc.env.Set("Box::read", &TypeScheme{Type: &FunctionType{ReturnType: &PrimitiveType{Name: "i32"}}})
	fn := &ast.FunctionLiteral{Body: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.ExpressionStatement{Expression: &ast.InvocationExpression{
			Function: &ast.IndexExpression{
				Token: token.Token{Literal: "."},
				Left:  &ast.InvocationExpression{Function: &ast.Identifier{Value: "makeBox"}},
				Index: &ast.Identifier{Value: "read"},
			},
		}},
	}}}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("expression receiver blocked generalization: %v", facts)
	}
}

func TestTemplateAuthorityCannotBeReopenedBySpecialization(t *testing.T) {
	tc := New(nilObjectEnvironment())
	fn := &ast.FunctionStatement{
		Name:       &ast.Identifier{Value: "restricted"},
		TypeParams: []*ast.TypeParameter{{Name: &ast.Identifier{Value: "T"}}},
		Parameters: []*ast.FunctionParameter{{
			Name: &ast.Identifier{Value: "value"},
			Type: &ast.Identifier{Value: "T"},
		}},
		ReturnType: &ast.Identifier{Value: "T"},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.UnsafeBlock{Body: &ast.BlockStatement{}},
			&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "value"}},
		}}},
	}
	tc.CheckProgram(&ast.Program{Statements: []ast.Statement{fn}})
	first := tc.CheckExpression(&ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "restricted"},
		Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1}},
	})
	if first == nil || len(tc.Errors()) != 0 {
		t.Fatalf("first specialization failed: %v", tc.Errors())
	}
	before := len(tc.Errors())
	second := tc.CheckExpression(&ast.InvocationExpression{
		Function:  &ast.Identifier{Value: "restricted"},
		Arguments: []ast.Expression{&ast.StringLiteral{Value: "different"}},
	})
	if second != nil || len(tc.Errors()) == before {
		t.Fatal("template specialization reopened restricted authority")
	}
}

func TestConditionalUnsafeBodyContributesGeneralizationBarrier(t *testing.T) {
	tc := New(nilObjectEnvironment())
	body := &ast.BlockStatement{Statements: []ast.Statement{
		&ast.IfStatement{
			Condition: &ast.Boolean{Value: true},
			Consequence: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.UnsafeBlock{Body: &ast.BlockStatement{}},
			}},
		},
	}}
	capture := functionCaptureFacts(&ast.FunctionLiteral{Body: body}, tc.env)
	initializer := deriveGeneralizationFacts(polymorphicIdentityType(), &ast.BlockExpression{Block: body}, tc.env)
	if !capture.Has(GeneralizationUnsafeAssumption) || !initializer.Has(GeneralizationUnsafeAssumption) {
		t.Fatalf("conditional hid unsafe evidence: capture=%v initializer=%v", capture, initializer)
	}
}

func TestWritesThroughParametersDoNotCaptureAuthority(t *testing.T) {
	tc := New(nilObjectEnvironment())
	fn := &ast.FunctionLiteral{
		Arguments: []*ast.Identifier{{Value: "buffer"}},
		Body: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.IndexAssignmentStatement{
				Target: &ast.IndexExpression{
					Left:  &ast.Identifier{Value: "buffer"},
					Index: &ast.IntegerLiteral{Value: 0},
				},
				Value: &ast.IntegerLiteral{Value: 1},
			},
		}},
	}
	if facts := functionCaptureFacts(fn, tc.env); !facts.Safe() {
		t.Fatalf("parameter write treated as captured authority: %v", facts)
	}
	fn.Arguments = nil
	tc.env.SetType("buffer", &ArrayType{Length: -1, IsSpan: true, ElementType: &PrimitiveType{Name: "i32"}})
	facts := functionCaptureFacts(fn, tc.env)
	if !facts.Has(GeneralizationMutableAuthority) || !facts.Has(GeneralizationRegionBound) {
		t.Fatalf("outer buffer write lost capture authority: %v", facts)
	}
}
