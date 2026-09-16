package typechecker

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/token"
)

func TestExpressionTypeProofIdentityAndDefensiveCopies(t *testing.T) {
	firstToken := token.Token{SemanticContext: "pkg.specialized", Literal: "+", Line: 4, Column: 9}
	secondToken := token.Token{SemanticContext: "pkg.specialized", Literal: "+", Line: 5, Column: 9}
	tc := &TypeChecker{expressionTypes: map[tokenKey]Type{
		positionKey(firstToken):  &PrimitiveType{Name: "u32"},
		positionKey(secondToken): &PrimitiveType{Name: "u32"},
	}}

	first, ok := tc.ExpressionTypeProof(firstToken)
	if !ok || first.ID == "" || first.Proposition != "checked.type" || first.Type != "u32" ||
		first.Provenance != "checked" || first.Witness != "u32" || first.Scope != "pkg.specialized:4:9" {
		t.Fatalf("expression type proof = %+v, ok=%v", first, ok)
	}
	again, ok := tc.ExpressionTypeProof(firstToken)
	if !ok || !reflect.DeepEqual(again, first) {
		t.Fatalf("expression type proof is not deterministic: first=%+v again=%+v", first, again)
	}
	second, ok := tc.ExpressionTypeProof(secondToken)
	if !ok || second.ID == first.ID {
		t.Fatalf("source-sensitive proof IDs = %q and %q", first.ID, second.ID)
	}

	authority := tc.ExpressionTypeProofs()
	authority[first.ID] = ExpressionTypeProof{}
	delete(authority, second.ID)
	after, ok := tc.ExpressionTypeProof(firstToken)
	if !ok || !reflect.DeepEqual(after, first) {
		t.Fatalf("mutating returned authority changed the checker proof: %+v", after)
	}

	tc.expressionTypes[positionKey(firstToken)] = &PrimitiveType{Name: "u64"}
	changed, ok := tc.ExpressionTypeProof(firstToken)
	if !ok || changed.ID == first.ID || changed.Type != "u64" {
		t.Fatalf("type-sensitive proof identity = %+v", changed)
	}
	if _, ok := (*TypeChecker)(nil).ExpressionTypeProof(firstToken); ok {
		t.Fatal("nil typechecker returned expression authority")
	}
}
