package nativegen

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

func TestVerificationGlobalsRetainsSourceClosureWithoutUnrelatedCells(t *testing.T) {
	call := func(name string) ast.Statement {
		return &ast.ExpressionStatement{Expression: &ast.InvocationExpression{Function: &ast.Identifier{Value: name}}}
	}
	root := &ast.FunctionStatement{Name: &ast.Identifier{Value: "root"}, Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.AssignmentStatement{Name: &ast.Identifier{Value: "direct"}, Value: &ast.Identifier{Value: "read"}}, call("child"),
	}}}}
	child := &ast.FunctionStatement{Name: &ast.Identifier{Value: "child"}, Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.AssignmentStatement{Name: &ast.Identifier{Value: "transitive"}, Value: &ast.Identifier{Value: "read"}}, call("root"), call("absent"),
	}}}}
	globals := map[string]asm.Global{
		"direct": {Type: "u32", Bits: 32}, "read": {Type: "u32", Bits: 32},
		"transitive": {Type: "u64", Bits: 64}, "unrelated": {Type: "u8", Bits: 8},
	}
	addressed := map[string]asm.Global{"addressed": {Type: "u16", Bits: 16}}
	got := verificationGlobals(root, map[string]*ast.FunctionStatement{"root": root, "child": child, "absent": nil}, globals, addressed)
	want := map[string]asm.Global{
		"direct": globals["direct"], "read": globals["read"], "transitive": globals["transitive"], "addressed": addressed["addressed"],
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("source closure = %+v, want %+v", got, want)
	}
	delete(got, "direct")
	delete(got, "addressed")
	if len(globals) != 4 || len(addressed) != 1 {
		t.Fatal("verification footprint mutated its inputs")
	}
	if verificationGlobals(nil, nil, globals, nil) != nil {
		t.Fatal("empty source retained unrelated globals")
	}
}
