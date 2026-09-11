package compiler

import (
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/stdlib"
)

// leanStdlibPackages lists the standard-library packages whose Lean
// extraction is committed under spec/lean/Oak/Stdlib (docs/spec/95-extraction.md
// section 5). Each package's program is the core prelude plus the flattened
// texts of its dependencies and itself; the roots are the package's own
// declarations (plus a driver instantiating generic templates, which the
// checker materializes under mangled names), and the extraction closes over
// their callees.
var leanStdlibPackages = []struct {
	name      string
	file      string
	namespace string
	deps      []string
	driver    string
}{
	{name: "varint", file: "VarintExtracted.lean", namespace: "Oak.Stdlib.Varint"},
	{name: "encoding", file: "EncodingExtracted.lean", namespace: "Oak.Stdlib.Encoding"},
	{name: "hash", file: "HashExtracted.lean", namespace: "Oak.Stdlib.Hash"},
	{name: "random", file: "RandomExtracted.lean", namespace: "Oak.Stdlib.Random", driver: `
drive_shuffle_u32: (state: [*]Xoshiro, items: [*]u32): () { random_shuffle[u32](state, items) }
`},
	{name: "uuid", file: "UuidExtracted.lean", namespace: "Oak.Stdlib.Uuid", deps: []string{"random", "encoding"}},
	{name: "sort", file: "SortU32Extracted.lean", namespace: "Oak.Stdlib.SortU32", driver: `
sort_u32_is_sorted: (items: []u32): Bool = sort_is_sorted[u32](items)
sort_u32_insertion: (items: [*]u32): () { sort_insertion[u32](items) }
sort_u32_heap: (items: [*]u32): () { sort_heap[u32](items) }
sort_u32_span: (items: [*]u32): () { sort_span[u32](items) }
sort_u32_search: (items: []u32, key: u32): Option[u32] = sort_search[u32](items, key)
sort_u32_lower_bound: (items: []u32, key: u32): u32 = sort_lower_bound[u32](items, key)
sort_u32_dedup: (items: [*]u32): u32 = sort_dedup[u32](items)
sort_u32_reverse: (items: [*]u32): () { sort_reverse[u32](items) }
`},
}

// leanStdlibProgram assembles a package's extraction program and its roots.
func leanStdlibProgram(t *testing.T, name string, deps []string, driver string) (string, []string) {
	t.Helper()
	var source strings.Builder
	source.WriteString(stdlib.Prelude)
	source.WriteString("\n")
	for _, dep := range deps {
		text, ok := stdlib.Packages[dep]
		if !ok {
			t.Fatalf("no standard library package %q", dep)
		}
		source.WriteString(stdlib.Flatten(text))
		source.WriteString("\n")
	}
	text, ok := stdlib.Packages[name]
	if !ok {
		t.Fatalf("no standard library package %q", name)
	}
	packageText := stdlib.Flatten(text)
	source.WriteString(packageText)
	source.WriteString("\n")
	source.WriteString(driver)
	roots := topLevelNames(t, packageText)
	roots = append(roots, topLevelNames(t, driver)...)
	sort.Strings(roots)
	return source.String(), roots
}

// topLevelNames lists the functions and types a source text declares.
func topLevelNames(t *testing.T, text string) []string {
	t.Helper()
	if strings.TrimSpace(text) == "" {
		return nil
	}
	p := parser.New(scanner.New(text))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("parse: %v", p.Errors())
	}
	var names []string
	for _, stmt := range program.Statements {
		switch s := stmt.(type) {
		case *ast.FunctionStatement:
			if s.Name != nil {
				names = append(names, s.Name.Value)
			}
		case *ast.ADTType:
			if s.Name != nil {
				names = append(names, s.Name.Value)
			}
		}
	}
	return names
}

// The committed extractions are regenerated from the library sources and
// compared byte for byte; OAK_LEAN_EXTRACT_UPDATE=1 rewrites them.
func TestLeanStdlibExtract(t *testing.T) {
	for _, pkg := range leanStdlibPackages {
		t.Run(pkg.name, func(t *testing.T) {
			source, roots := leanStdlibProgram(t, pkg.name, pkg.deps, pkg.driver)
			extracted, err := New().WithSource("stdlib_"+pkg.name+".oak", source).EmitLeanRoots(pkg.namespace, roots).Get()
			if err != nil {
				t.Fatalf("extraction failed: %v", err)
			}
			if strings.Contains(extracted, "sorry") {
				t.Fatalf("extraction contains sorry")
			}
			target := filepath.Join("..", "spec", "lean", "Oak", "Stdlib", pkg.file)
			if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
				if err := os.MkdirAll(filepath.Dir(target), 0o755); err != nil {
					t.Fatal(err)
				}
				if err := os.WriteFile(target, []byte(extracted), 0o644); err != nil {
					t.Fatal(err)
				}
			}
			committed, err := os.ReadFile(target)
			if err != nil {
				t.Fatalf("read committed extraction: %v (run with OAK_LEAN_EXTRACT_UPDATE=1 to create it)", err)
			}
			if string(committed) != extracted {
				t.Fatalf("%s is out of date with the library sources; rerun with OAK_LEAN_EXTRACT_UPDATE=1", target)
			}
		})
	}
}
