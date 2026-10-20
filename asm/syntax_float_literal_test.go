package asm

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func TestSyntaxFloatLiteralRounding(t *testing.T) {
	for _, tc := range []struct {
		text   string
		bits32 uint32
		bits64 uint64
	}{
		{"1.00000005960464477550", 0x3f800001, 0x3ff0000010000000},
		{"1.00000017881393432617", 0x3f800001, 0x3ff0000030000000},
		{"1.000000059604644775390625", 0x3f800000, 0x3ff0000010000000},
		{"0x1.fffffeffffffffffffffp127", 0x7f7fffff, 0x47effffff0000000},
		{"0.0", 0, 0},
		{"-0.0", 0x80000000, 0x8000000000000000},
		{"0x1p-149", 1, 0x36a0000000000000},
		// The untyped syntax node stores both widths. A valid f64 literal
		// may overflow its dormant f32 slot; exporting it must still work.
		{"1e39", 0x7f800000, 0x48078287f49c4a1d},
	} {
		t.Run(tc.text, func(t *testing.T) {
			w := &syntaxWriter{}
			// Deliberately omit the optional f64 cache: Text is authoritative.
			id, reason, ok := w.expr(nil, &ast.FloatLiteral{Text: tc.text})
			if !ok {
				t.Fatalf("not serialized: %s", reason)
			}
			if id != 0 || len(w.nodes) != 8 || w.nodes[0] != synFloatLit {
				t.Fatalf("unexpected syntax node %d: %v", id, w.nodes)
			}
			got32 := w.nodes[1]
			got64 := uint64(w.nodes[5]) | uint64(w.nodes[6])<<32
			if got32 != tc.bits32 || got64 != tc.bits64 {
				t.Fatalf("got f32=0x%x f64=0x%x, want f32=0x%x f64=0x%x", got32, got64, tc.bits32, tc.bits64)
			}
		})
	}
}

func TestSyntaxFloatLiteralInvalidFailsClosed(t *testing.T) {
	for _, text := range []string{"", "not-a-number", "1e400"} {
		t.Run(text, func(t *testing.T) {
			w := &syntaxWriter{}
			if _, reason, ok := w.expr(nil, &ast.FloatLiteral{Text: text, Value: 1.5}); ok || reason == "" || len(w.nodes) != 0 {
				t.Fatalf("invalid literal serialized: nodes=%v reason=%q ok=%t", w.nodes, reason, ok)
			}
		})
	}
}

func TestExportSyntaxFloatLiteralRounding(t *testing.T) {
	spec, err := parseSignatureWithBody("f: (a: f32) -> f32 = 1.00000005960464477550")
	if err != nil {
		t.Fatal(err)
	}
	words, _, reason, ok := ExportSyntax(spec, nil, Declarations{})
	if !ok {
		t.Fatalf("not exported: %s", reason)
	}
	// Header and tables precede the eight-word nodes (syntax.go).
	params := uint32(0)
	for i := uint32(0); i < words[0]; i++ {
		params += words[16+8*i+1]
	}
	nodesAt := 16 + 8*words[0] + 4*params + 8*words[6] + 2*words[7] + 2*words[8] + 3*words[10] + words[9]
	body := words[16+3]
	node := words[nodesAt+8*body : nodesAt+8*body+8]
	if node[0] != synFloatLit || node[1] != 0x3f800001 || node[5] != 0x10000000 || node[6] != 0x3ff00000 {
		t.Fatalf("incorrect public syntax payload: %v", node)
	}
}
