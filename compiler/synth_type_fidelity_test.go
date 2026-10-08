package compiler

import (
	"github.com/SCKelemen/oak/ast"
	"testing"
)

func TestSyntheticTypeConstructorsPreserveSource(t *testing.T) {
	s := newSynth("type-fidelity")
	for want, expr := range map[string]ast.Expression{
		"[]u32":           s.view(s.id("u32")),
		"[*]u32":          s.span(s.id("u32")),
		"[4]u32":          s.array(4, s.id("u32")),
		"Pair[u32, []u8]": s.app("Pair", s.id("u32"), s.view(s.id("u8"))),
	} {
		if expr.String() != want {
			t.Fatalf("synthesized %s, want %s", expr, want)
		}
		tree, err := New().WithSource("type.oak", "f: (x: "+expr.String()+"): () = {}").Parse().Get()
		if err != nil {
			t.Fatal(err)
		}
		original := tree.Root.Statements[0].(*ast.FunctionStatement).Parameters[0].Type
		rebuilt, ok := s.rebuildType(original)
		if !ok || rebuilt.String() != want {
			t.Fatalf("rebuilt %s, want %s", rebuilt, want)
		}
	}
	tree, err := New().WithSource("align.oak", "f: (x: [* align 16]u32): () = {}").Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	rebuilt, ok := s.rebuildType(tree.Root.Statements[0].(*ast.FunctionStatement).Parameters[0].Type)
	if !ok || rebuilt.String() != "[* align 16]u32" {
		t.Fatalf("lost alignment: %s", rebuilt)
	}
}
