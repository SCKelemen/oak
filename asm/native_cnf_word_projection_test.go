package asm

import (
	"strings"
	"testing"
)

func TestNativeCNFReplayWordProjectionRefusesMalformedInputs(t *testing.T) {
	tests := []struct {
		name   string
		mutate func(*blaster, *term)
		want   string
	}{
		{"zero width", func(_ *blaster, root *term) { root.width = 0 }, "outside 1..64"},
		{"wide term", func(_ *blaster, root *term) { root.width = 65 }, "outside 1..64"},
		{"negative width", func(_ *blaster, root *term) { root.width = -1 }, "outside 1..64"},
		{"unknown operation", func(_ *blaster, root *term) { root.op = "add" }, "outside the word projection"},
		{"unknown kind", func(_ *blaster, root *term) { root.kind = termIte }, "term kind"},
		{"binary condition", func(_ *blaster, root *term) { root.cond = root.left }, "binary term is malformed"},
		{"missing child", func(_ *blaster, root *term) { root.left = nil }, "binary term is malformed"},
		{"constant high bits", func(_ *blaster, root *term) { root.right.value |= 1 << 8 }, "constant term is malformed"},
		{"constant child", func(_ *blaster, root *term) { root.right.left = root.left }, "constant term is malformed"},
		{"unknown parameter", func(_ *blaster, root *term) { root.left.name = "missing" }, "parameter is absent"},
		{"parameter width mismatch", func(_ *blaster, root *term) { root.left.declared = 16 }, "mismatched declared width"},
		{"negative declared width", func(_ *blaster, root *term) { root.left.declared = -1 }, "parameter term is malformed"},
		{"parameter value", func(_ *blaster, root *term) { root.left.value = 1 }, "parameter term is malformed"},
		{"mismatched index", func(bl *blaster, _ *term) { bl.index["a"] = 1 }, "invalid ordered parameter"},
		{"missing index zero", func(bl *blaster, _ *term) {
			delete(bl.index, "a")
			bl.index["missing"] = 0
		}, "invalid ordered parameter"},
		{"duplicate names", func(bl *blaster, _ *term) { bl.params[1] = "a" }, "invalid ordered parameter"},
		{"extra declaration", func(bl *blaster, _ *term) { bl.widths["extra"] = 8 }, "tables disagree"},
		{"invalid declaration", func(bl *blaster, _ *term) { bl.widths["a"] = 65 }, "invalid ordered parameter"},
		{"grouped", func(bl *blaster, _ *term) { bl.grouped = true }, "ordering or abstraction"},
		{"assumed", func(bl *blaster, _ *term) { bl.assumed = true }, "ordering or abstraction"},
		{"select", func(bl *blaster, _ *term) { bl.selects = []selectAbstraction{{}} }, "ordering or abstraction"},
		{"zero allocation", func(bl *blaster, _ *term) { bl.cnf.inputs[0] = 0 }, "input allocation"},
		{"negative allocation", func(bl *blaster, _ *term) { bl.cnf.inputs[0] = -1 }, "input allocation"},
		{"out of range allocation", func(bl *blaster, _ *term) { bl.cnf.inputs[0] = bl.cnf.variables + 1 }, "input allocation"},
		{"aliased inputs", func(bl *blaster, _ *term) { bl.cnf.inputs[0] = bl.cnf.inputs[1] }, "input allocation"},
		{"missing high input bit", func(bl *blaster, _ *term) {
			// Retain a valid dense allocation while moving a required source
			// bit to an unused source. Only the name/bit projection catches it.
			bl.cnf.inputs[999] = bl.cnf.inputs[70]
			delete(bl.cnf.inputs, 70)
		}, "bit 7 has no valid allocated input output"},
		{"truncated invalid child", func(_ *blaster, root *term) {
			root.width = 1
			root.right.width = 65
		}, "outside 1..64"},
		{"cycle", func(_ *blaster, root *term) { root.left = root }, "cyclic"},
		{"deep tree", func(_ *blaster, root *term) {
			for i := 0; i < 66; i++ {
				root.left = &term{kind: termBinary, width: 8, op: "or", left: root.left, right: constTerm(0, 8)}
			}
		}, "depth bound"},
		{"deep reuse of shared subtree", func(_ *blaster, root *term) {
			for i := 0; i < 40; i++ {
				root.left = &term{kind: termBinary, width: 8, op: "or", left: root.left, right: constTerm(0, 8)}
			}
			root.right = root.left
			for i := 0; i < 25; i++ {
				root.right = &term{kind: termBinary, width: 8, op: "or", left: root.right, right: constTerm(0, 8)}
			}
		}, "depth bound"},
		{"expanding shared DAG", func(_ *blaster, root *term) {
			for i := 0; i < 20; i++ {
				root.left = &term{kind: termBinary, width: 8, op: "and", left: root.left, right: root.left}
			}
		}, "text budget"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			bl := newCNFBlaster([]string{"a", "b"}, map[string]int{"a": 8, "b": 8})
			root := &term{kind: termBinary, width: 8, op: "xor", left: paramTerm("a", 8), right: constTerm(0x5a, 8)}
			bl.blast(root)
			bl.blast(paramTerm("b", 8))
			if _, err := renderNativeCNFReplayWord(bl, root); err != nil {
				t.Fatalf("valid fixture refused: %v", err)
			}
			test.mutate(bl, root)
			if _, err := renderNativeCNFReplayWord(bl, root); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want %q", err, test.want)
			}
		})
	}

	bl := newCNFBlaster(nil, nil)
	for _, missing := range []*blaster{nil, {}} {
		if _, err := renderNativeCNFReplayWord(missing, constTerm(0, 8)); err == nil {
			t.Fatal("missing CNF builder entered the projection")
		}
	}
	for _, test := range []struct{ left, right *term }{
		{nil, constTerm(0, 8)}, {constTerm(0, 8), nil},
		{constTerm(0, 8), constTerm(0, 16)}, {constTerm(0, 0), constTerm(0, 0)},
	} {
		if _, err := renderNativeCNFReplayPairs(bl, test.left, test.right); err == nil {
			t.Fatal("missing, unequal, or empty result widths entered the pair projection")
		}
	}
}
