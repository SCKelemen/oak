package asm

import (
	"fmt"
	goast "go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestPair64WriteLogMatchesLean(t *testing.T) {
	prefix := appendWrite(nil, "s", constTerm(2, 32), constTerm(3, 64), nil)
	prefixSlice := prefix["s"]
	prefixEntry := prefixSlice[0]
	log := appendPair64Writes(prefix, "s", constTerm(7, 32), constTerm(11, 64), constTerm(13, 64))
	if len(prefixSlice) != 1 || prefixSlice[0] != prefixEntry {
		t.Fatal("appending a pair mutated an aliased write-log prefix")
	}
	writes := log["s"]
	if len(writes) != 3 {
		t.Fatalf("pair log length = %d, want prefix plus two", len(writes))
	}
	assertWordWrite(t, writes[1], 7, 11)
	assertWordWrite(t, writes[2], 8, 13)
	wrapped := appendPair64Writes(nil, "s", constTerm(0xffffffff, 32), constTerm(11, 64), constTerm(13, 64))
	assertWordWrite(t, wrapped["s"][0], 0xffffffff, 11)
	assertWordWrite(t, wrapped["s"][1], 0, 13)

	block := appendPair64Writes(nil, "s", constTerm(7, 32), constTerm(0, 64), constTerm(0, 64))
	block = appendPair64Writes(block, "s", constTerm(9, 32), constTerm(0, 64), constTerm(0, 64))
	for i, write := range block["s"] {
		assertWordWrite(t, write, uint64(7+i), 0)
	}

	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "PairStoreEffects.lean"))
	if err != nil {
		t.Fatal(err)
	}
	want := []string{
		"example : pair64Writes 7 11 13 = " + renderWordWrites(writes[1:]) + " := by decide",
		"example : pair64Writes 4294967295 11 13 = " + renderWordWrites(wrapped["s"]) + " := by decide",
		"example : block4Writes 7 0 = " + renderWordWrites(block["s"]) + " := by decide",
	}
	for _, line := range want {
		if !strings.Contains(string(lean), line) {
			t.Fatalf("Go pair-write expansion is not synchronized with Lean:\n%s", line)
		}
	}
}

func assertWordWrite(t *testing.T, write *spanWrite, index, value uint64) {
	t.Helper()
	if write == nil || write.memory != "" || write.guard != nil ||
		write.index.kind != termConst || write.index.width != 32 || write.index.value != index ||
		write.value.kind != termConst || write.value.width != 64 || write.value.value != value {
		t.Fatalf("write = %+v, want unconditional (%d, %d)", write, index, value)
	}
}

func renderWordWrites(writes []*spanWrite) string {
	parts := make([]string, len(writes))
	for i, write := range writes {
		parts[i] = fmt.Sprintf("⟨%d, %d⟩", write.index.value, write.value.value)
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

// The helper is proof staging, not instruction authority. This gate makes any
// production use deliberate: it must arrive together with the separately
// checked private-memory certificate and replacement verifier tests.
func TestPair64WriteLogRemainsUnreachableFromInstructions(t *testing.T) {
	entries, err := os.ReadDir(".")
	if err != nil {
		t.Fatal(err)
	}
	references := 0
	files := token.NewFileSet()
	for _, entry := range entries {
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".go") || strings.HasSuffix(entry.Name(), "_test.go") {
			continue
		}
		file, err := parser.ParseFile(files, entry.Name(), nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		goast.Inspect(file, func(node goast.Node) bool {
			if ident, ok := node.(*goast.Ident); ok && ident.Name == "appendPair64Writes" {
				references++
			}
			return true
		})
	}
	if references != 1 {
		t.Fatalf("appendPair64Writes has %d production references, want only its staged declaration", references)
	}
}

// A pair store through a record span writes the leaves its two registers
// cover; through a span of scalars it is still refused, since a span's
// element memory is one element per index and a pair writes two.
func TestPairStorePaths(t *testing.T) {
	generic := verifyCase(t,
		"zero2: (v: [*]u64) -> ()",
		"{\n  len(v) >= u32(2) ? {\n    v[u32(0)] = u64(0)\n    v[u32(1)] = u64(0)\n  } | { }\n}",
		"  bind x0, w1 = v\n  clobber w9, w10, x11\n  cmp w1, #2\n  b.lo done\n  mov w9, wzr\n  sub w10, w1, #2\n  cmp w9, w10\n  b.hi done\n  add x11, x0, w9, uxtw #3\n  stp xzr, xzr, [x11]\ndone:\n  ret")
	if generic.Kind != VerdictTrusted || !strings.Contains(generic.Message, "a pair store to a span") {
		t.Fatalf("generic span STP must remain refused, got %s: %s", generic.Kind, generic.Message)
	}

	decl := "zero_node: (pool: [*]Node, i: u32) -> ()"
	unit, errs := ParseUnit("pair_record.oakasm", decl+" = {\n  bind x0, w1 = pool\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  b.hs done\n  add x9, x0, w2, uxtw #4\n  stp xzr, xzr, [x9]\ndone:\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	unit.Functions[0].Composites = map[string]Composite{"Node": {
		Size: 16,
		Fields: []CompositeField{
			{Name: "first", Offset: 0, Size: 8, Scalar: "u64"},
			{Name: "second", Offset: 8, Size: 8, Scalar: "u64"},
		},
	}}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("record pair must reach the verifier after byte checking: %v", findings)
	}
	spec, err := parseSignatureWithBody(decl + " = {\n  i < len(pool) ? {\n    pool[i].first = u64(0)\n    pool[i].second = u64(0)\n  } | { }\n}")
	if err != nil {
		t.Fatal(err)
	}
	record := Verify(unit.Functions[0], sig, spec.Body)
	if record.Kind != VerdictProven || !strings.Contains(record.Message, "the span memory it writes (pool.first, pool.second)") {
		t.Fatalf("record-span STP must be proven in the leaves it writes, got %s: %s", record.Kind, record.Message)
	}
}
