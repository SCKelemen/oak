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
	// source, when set, is the program itself (over the core prelude and
	// deps) instead of a library package: a committed extraction of a
	// program shape rather than of a package.
	source string
}{
	{name: "varint", file: "VarintExtracted.lean", namespace: "Oak.Stdlib.Varint"},
	{name: "encoding", file: "EncodingExtracted.lean", namespace: "Oak.Stdlib.Encoding"},
	{name: "hash", file: "HashExtracted.lean", namespace: "Oak.Stdlib.Hash"},
	{name: "random", file: "RandomExtracted.lean", namespace: "Oak.Stdlib.Random", driver: `
drive_shuffle_u32: (state: [*]Xoshiro, items: [*]u32): () { random_shuffle[u32](state, items) }
`},
	{name: "uuid", file: "UuidExtracted.lean", namespace: "Oak.Stdlib.Uuid", deps: []string{"random", "encoding"}},
	{name: "float", file: "FloatExtracted.lean", namespace: "Oak.Stdlib.Float"},
	// The ml shape (docs/notes/ml-feedback-2026-09.md, roadmap E4): fixed
	// reductions over f32 and f64 in the stated sequential order, an axpy
	// into a span, and the f32/f64 rows of 20-types.md section 11.3.4.
	{name: "floatkernels", file: "FloatKernelsExtracted.lean", namespace: "Oak.Stdlib.FloatKernels", source: `
// dot_f32 combines products left to right (docs/spec/20-types.md section 11.3.3).
pub dot_f32: (a: []f32, b: []f32): f32 {
  acc: f32 = 0.0
  i: u32 = 0
  while i < len(a) && i < len(b) {
    acc = acc + a[i] * b[i]
    i = i + u32(1)
  }
  acc
}
pub sum_f32: (xs: []f32): f32 {
  acc: f32 = 0.0
  i: u32 = 0
  while i < len(xs) {
    acc = acc + xs[i]
    i = i + u32(1)
  }
  acc
}
pub sum_f64: (xs: []f64): f64 {
  acc: f64 = 0.0
  i: u32 = 0
  while i < len(xs) {
    acc = acc + xs[i]
    i = i + u32(1)
  }
  acc
}
// axpy writes y[i] = a * x[i] + y[i] with two roundings, never contracted.
pub axpy_f32: (a: f32, x: []f32, y: [*]f32): () {
  i: u32 = 0
  while i < len(x) && i < len(y) {
    y[i] = a * x[i] + y[i]
    i = i + u32(1)
  }
}
pub max_abs_f32: (xs: []f32): f32 {
  best: f32 = 0.0
  i: u32 = 0
  while i < len(xs) {
    m: f32 = abs(xs[i])
    m > best ? { best = m }
    i = i + u32(1)
  }
  best
}
pub widen_mean: (xs: []f32): f64 {
  total: f64 = 0.0
  i: u32 = 0
  while i < len(xs) {
    total = total + f64(xs[i])
    i = i + u32(1)
  }
  len(xs) == u32(0) ? 0.0 | total / f64_round_u32(len(xs))
}
pub quantize_u8: (x: f32, scale: f32): u8 = u8_saturating_f32(round(x / scale))
pub bits_roundtrip: (x: f64): Bool = f64_bits_u64(u64_bits_f64(x)) == x || is_nan(x)
`},
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
func leanStdlibProgram(t *testing.T, name string, deps []string, driver, source_ string) (string, []string) {
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
	packageText := source_
	if packageText == "" {
		text, ok := stdlib.Packages[name]
		if !ok {
			t.Fatalf("no standard library package %q", name)
		}
		packageText = stdlib.Flatten(text)
	}
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
			source, roots := leanStdlibProgram(t, pkg.name, pkg.deps, pkg.driver, pkg.source)
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
