package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/resourceflow"
)

func callableResourceAnalysis() (*TypeChecker, *typedResourceAnalysis) {
	tc := setupTypeChecker("")
	tc.globalEnv = tc.env
	model := NewResourceModel()
	model.MarkResourceType("Handle")
	analysis := &typedResourceAnalysis{
		tc:       tc,
		model:    model,
		flow:     resourceflow.New(),
		reported: make(map[string]bool),
	}
	analysis.pushScope()
	return tc, analysis
}

func TestResolveResourceDeclarationsAcceptsSemanticMethodIdentity(t *testing.T) {
	tc := setupTypeChecker("")
	tc.env.SetType("Handle", &ADTType{Name: "Handle"})
	tc.env.SetType("Handle::transfer", &FunctionType{
		Parameters: []Type{&ADTType{Name: "Handle"}},
		ReturnType: &UnitType{},
	})

	resolved, err := tc.ResolveResourceDeclarations([]ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open"},
		Initial:       "Open",
		Transitions: []ResourceTransitionDeclaration{{
			Name:             "transfer-transition",
			Callable:         "Handle::transfer",
			From:             "Open",
			To:               "Open",
			Consumes:         []int{0},
			ConsumesReceiver: true,
		}},
	}})
	if err != nil {
		t.Fatalf("semantic method callable failed resource resolution: %v", err)
	}
	transition := resolved.Protocols[0].Transitions[0]
	if transition.Callable != "Handle::transfer" || !transition.ConsumesReceiver || len(transition.Consumes) != 1 || transition.Consumes[0] != 0 {
		t.Fatalf("unexpected resolved method transition: %#v", transition)
	}
}

func TestResolveResourceDeclarationsRejectsReceiverConsumeOnFreeFunction(t *testing.T) {
	tc := setupTypeChecker("")
	tc.env.SetType("Handle", &ADTType{Name: "Handle"})
	tc.env.SetType("close", &FunctionType{ReturnType: &UnitType{}})

	_, err := tc.ResolveResourceDeclarations([]ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open"},
		Initial:       "Open",
		Transitions: []ResourceTransitionDeclaration{{
			Name:             "close-transition",
			Callable:         "close",
			From:             "Open",
			To:               "Open",
			ConsumesReceiver: true,
		}},
	}})
	if err == nil || !strings.Contains(err.Error(), "no resolved nominal receiver identity") {
		t.Fatalf("expected free-function receiver-consume rejection, got %v", err)
	}
}

func TestResolveResourceDeclarationsRejectsNonResourceReceiverConsume(t *testing.T) {
	tc := setupTypeChecker("")
	tc.env.SetType("Handle", &ADTType{Name: "Handle"})
	tc.env.SetType("Other", &ADTType{Name: "Other"})
	tc.env.SetType("Other::close", &FunctionType{ReturnType: &UnitType{}})

	_, err := tc.ResolveResourceDeclarations([]ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open"},
		Initial:       "Open",
		Transitions: []ResourceTransitionDeclaration{{
			Name:             "close-transition",
			Callable:         "Other::close",
			From:             "Open",
			To:               "Open",
			ConsumesReceiver: true,
		}},
	}})
	if err == nil || !strings.Contains(err.Error(), "non-resource type") {
		t.Fatalf("expected non-resource receiver-consume rejection, got %v", err)
	}
}

func TestResourceCallableIdentityRejectsLexicallyShadowedGlobal(t *testing.T) {
	tc, analysis := callableResourceAnalysis()
	tc.globalEnv.SetType("close", &FunctionType{
		Parameters: []Type{&ADTType{Name: "Handle"}},
		ReturnType: &UnitType{},
	})
	analysis.model.MarkOperation("close", ResourceOperation{Consumes: []int{0}})

	call := &ast.InvocationExpression{Function: &ast.Identifier{Value: "close"}}
	if identity, ok := analysis.callableIdentity(call); !ok || identity != "close" {
		t.Fatalf("global callable identity = (%q, %v), want (close, true)", identity, ok)
	}

	analysis.bind("close")
	if identity, ok := analysis.callableIdentity(call); ok {
		t.Fatalf("lexically shadowed global resolved as resource callable %q", identity)
	}
}

func TestResourceCallableIdentityUsesCheckedReceiverType(t *testing.T) {
	tc, analysis := callableResourceAnalysis()
	tc.globalEnv.SetType("Handle::transfer", &FunctionType{
		Parameters: []Type{&ADTType{Name: "Handle"}},
		ReturnType: &UnitType{},
	})
	analysis.model.MarkOperation("Handle::transfer", ResourceOperation{Consumes: []int{0}})

	receiver := &ast.Identifier{Value: "self"}
	argument := &ast.Identifier{Value: "other"}
	method := &ast.Identifier{Value: "transfer"}
	call := &ast.InvocationExpression{
		Function: &ast.IndexExpression{Dot: true, Left: receiver, Index: method},
		Arguments: []ast.Expression{argument},
	}
	tc.env.borrowMetadata().expressions[receiver] = &ADTType{Name: "Handle"}

	identity, ok := analysis.callableIdentity(call)
	if !ok || identity != "Handle::transfer" {
		t.Fatalf("method callable identity = (%q, %v), want (Handle::transfer, true)", identity, ok)
	}

	analysis.bind("self")
	analysis.bind("other")
	analysis.flow.Register("self", receiver)
	analysis.flow.Register("other", argument)
	analysis.invocation(call)

	if !analysis.flow.CanUse("self") {
		t.Fatal("explicit argument consumption unexpectedly consumed method receiver")
	}
	if analysis.flow.CanUse("other") {
		t.Fatal("receiver-qualified consuming method did not consume its explicit resource argument")
	}
}

func TestResourceReceiverConsumptionInvalidatesAliasClass(t *testing.T) {
	tc, analysis := callableResourceAnalysis()
	tc.globalEnv.SetType("Handle::close", &FunctionType{ReturnType: &UnitType{}})
	analysis.model.MarkOperation("Handle::close", ResourceOperation{ConsumesReceiver: true})

	root := &ast.Identifier{Value: "self"}
	receiver := &ast.Identifier{Value: "alias"}
	call := &ast.InvocationExpression{
		Function: &ast.IndexExpression{
			Dot:   true,
			Left:  receiver,
			Index: &ast.Identifier{Value: "close"},
		},
	}
	tc.env.borrowMetadata().expressions[receiver] = &ADTType{Name: "Handle"}
	analysis.bind("self")
	analysis.bind("alias")
	analysis.flow.Register("self", root)
	analysis.flow.Alias("alias", "self", receiver)
	analysis.invocation(call)

	if analysis.flow.CanUse("alias") || analysis.flow.CanUse("self") {
		t.Fatal("consuming receiver did not invalidate its complete authority alias class")
	}
}

func TestResourceCallableIdentityDoesNotMatchMethodSpellingAcrossReceivers(t *testing.T) {
	tc, analysis := callableResourceAnalysis()
	tc.globalEnv.SetType("Handle::transfer", &FunctionType{ReturnType: &UnitType{}})
	tc.globalEnv.SetType("Other::transfer", &FunctionType{ReturnType: &UnitType{}})
	analysis.model.MarkOperation("Handle::transfer", ResourceOperation{})

	receiver := &ast.Identifier{Value: "other"}
	call := &ast.InvocationExpression{
		Function: &ast.IndexExpression{
			Dot:   true,
			Left:  receiver,
			Index: &ast.Identifier{Value: "transfer"},
		},
	}
	tc.env.borrowMetadata().expressions[receiver] = &ADTType{Name: "Other"}

	identity, ok := analysis.callableIdentity(call)
	if !ok || identity != "Other::transfer" {
		t.Fatalf("method callable identity = (%q, %v), want (Other::transfer, true)", identity, ok)
	}
	if _, resource := analysis.operation(call); resource {
		t.Fatal("resource semantics leaked across receivers that share a method spelling")
	}
}

func TestFreshMethodResultUsesResolvedCallableIdentity(t *testing.T) {
	tc, analysis := callableResourceAnalysis()
	tc.globalEnv.SetType("Handle::renew", &FunctionType{
		ReturnType: &ADTType{Name: "Handle"},
	})
	analysis.model.MarkOperation("Handle::renew", ResourceOperation{
		ConsumesReceiver: true,
		ReturnsFresh:     true,
	})

	receiver := &ast.Identifier{Value: "self"}
	call := &ast.InvocationExpression{
		Function: &ast.IndexExpression{
			Dot:   true,
			Left:  receiver,
			Index: &ast.Identifier{Value: "renew"},
		},
	}
	tc.env.borrowMetadata().expressions[receiver] = &ADTType{Name: "Handle"}
	analysis.bind("self")
	analysis.flow.Register("self", receiver)

	analysis.variable(&ast.VariableDeclaration{
		Name:  &ast.Identifier{Value: "next"},
		Value: call,
	})
	if !analysis.flow.Registered("next") || !analysis.flow.CanUse("next") {
		t.Fatal("fresh method result was not registered as a new live authority class")
	}
	if analysis.flow.CanUse("self") {
		t.Fatal("consuming fresh-return method left old receiver authority live")
	}
}
