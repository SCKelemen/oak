package compiler

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// An `export("symbol")` marker gives a pub function of any package a stable
// C ABI symbol (docs/spec/92-ffi.md section 2.9): the header names it with
// the right prototype and its package, the generated C defines it, and a C
// consumer that only includes the header calls it. The root's implicit
// `oak_<name>` exports are unchanged; a dependency's plain pub functions no
// longer leak into the header under the elaborator's internal names.
func TestE2EExportsFromAnyPackage(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/ml\noak 0.1.0\n",
		"ops/ops.oak": `package ops

export("oak_ml_add") pub add: (a: i32, b: i32): i32 = a + b
export("oak_ml_bump") pub bump: (p: [*]i32): () { p[0] = p[0] + i32(1) }
export("oak_ml_pair") pub pair: (lo: u32, hi: u32): u64 = (u64(lo) << u64(32)) | u64(hi)
pub scale: (a: i32): i32 = a * i32(2)
helper: (a: i32): i32 = a
`,
		"main.oak": `import("example.com/ml/ops")

Pair: type = struct { lo: i32, hi: i32 }
export("oak_ml_total") pub total: (p: Pair): i32 = p.lo + p.hi
pub root_visible: (): i32 = i32(7)
probe: (): c.Int32 = c.extern("probe_exports")
main: (): i32 {
  assert(ops.add(1, 2) == i32(3))
  assert(i32(probe()) == 42)
  42
}
`,
	})
	comp := New().WithPackageDir(root)
	header, err := comp.EmitHeader().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"typedef struct oak_Pair {",
		"i32 oak_root_visible( void );",
		"/* explicit C ABI exports (export(\"symbol\") markers) */",
		"/* example.com/ml/ops: add */",
		"i32 oak_ml_add( i32 a, i32 b );",
		"/* example.com/ml/ops: pair */",
		"u64 oak_ml_pair( u32 lo, u32 hi );",
		"void oak_ml_bump( oak_span_i32 p );",
		"/* the root package: total */",
		"i32 oak_ml_total( oak_Pair p );",
	} {
		if !strings.Contains(header, want) {
			t.Fatalf("header lacks %q:\n%s", want, header)
		}
	}
	// Exports are listed sorted by symbol after the implicit root exports.
	if strings.Index(header, "oak_ml_add(") > strings.Index(header, "oak_ml_bump(") || strings.Index(header, "oak_ml_bump(") > strings.Index(header, "oak_ml_pair(") || strings.Index(header, "oak_ml_pair(") > strings.Index(header, "oak_ml_total(") {
		t.Fatalf("explicit exports are not sorted by symbol:\n%s", header)
	}
	// An explicit marker in the root replaces the implicit oak_<name> in the
	// header; the Oak definition keeps its internal name for Oak callers.
	for _, private := range []string{"__add", "__scale", "__helper", "oak_main", "probe_exports", "helper(", "oak_total("} {
		if strings.Contains(header, private) {
			t.Fatalf("header exposes %q:\n%s", private, header)
		}
	}
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "ml.h"), []byte(header), 0o644); err != nil {
		t.Fatal(err)
	}
	consumer := `
#include "ml.h"
int32_t probe_exports(void) {
  i32 cells[1] = { 4 };
  oak_span_i32 span = { cells, 1 };
  oak_ml_bump(span);
  if (oak_ml_pair(1u, 2u) != (((uint64_t)1 << 32) | 2u)) { return 0; }
  oak_Pair p = { oak_ml_add(10, 5), cells[0] };
  if (oak_root_visible() != 7) { return 0; }
  return oak_ml_total(p) + 22; /* 15 + 5 + 22 */
}
`
	consumerPath := filepath.Join(dir, "consumer.c")
	if err := os.WriteFile(consumerPath, []byte(consumer), 0o644); err != nil {
		t.Fatal(err)
	}
	_, code, abnormal := buildAndRunFrom(t, "ml_exports", comp, "-I"+dir, consumerPath)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Two exports may not share a symbol, whether both are explicit or one is
// the root's implicit `oak_<name>` (OAK-F0108); the diagnostic names both
// packages.
func TestExportSymbolCollisions(t *testing.T) {
	cases := []struct {
		name  string
		files map[string]string
		want  []string
	}{
		{
			name: "two packages",
			files: map[string]string{
				"oak.mod":  "module example.com/ml\noak 0.1.0\n",
				"a/a.oak":  "package a\nexport(\"oak_ml_op\") pub first: (x: i32): i32 = x\n",
				"b/b.oak":  "package b\nexport(\"oak_ml_op\") pub second: (x: i32): i32 = x\n",
				"main.oak": "import(\"example.com/ml/a\")\nimport(\"example.com/ml/b\")\nmain: (): i32 { a.first(1) + b.second(2) }\n",
			},
			want: []string{"OAK-F0108", `export symbol "oak_ml_op" is already used by`, "example.com/ml/"},
		},
		{
			name: "implicit root export",
			files: map[string]string{
				"oak.mod":  "module example.com/ml\noak 0.1.0\n",
				"a/a.oak":  "package a\nexport(\"oak_step\") pub first: (x: i32): i32 = x\n",
				"main.oak": "import(\"example.com/ml/a\")\npub step: (x: i32): i32 = a.first(x)\nmain: (): i32 { step(1) }\n",
			},
			want: []string{"OAK-F0108", `export symbol "oak_step" is already used by step in the root package`, "exported implicitly"},
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			root := writeModule(t, tc.files)
			_, err := New().WithPackageDir(root).EmitC().Get()
			if err == nil {
				t.Fatal("expected the export collision to be rejected")
			}
			for _, want := range tc.want {
				if !strings.Contains(err.Error(), want) {
					t.Fatalf("error lacks %q:\n%v", want, err)
				}
			}
		})
	}
}

// An export must name a C identifier and mark a pub, non-generic free
// function (OAK-F0109); the parser refuses the marker before anything but
// a pub function declaration.
func TestExportMarkerRejections(t *testing.T) {
	cases := []struct {
		name string
		src  string
		want string
	}{
		{"not a C identifier", "export(\"oak-ml.add\") pub add: (a: i32): i32 = a\nmain: (): i32 { add(1) }\n", "OAK-F0109"},
		{"generic template", "export(\"oak_ml_id\") pub id[T]: (a: T): T = a\nmain: (): i32 { id[i32](1) }\n", "OAK-F0109"},
		{"not pub", "export(\"oak_ml_add\") add: (a: i32): i32 = a\nmain: (): i32 { add(1) }\n", "must be followed by a pub function declaration"},
		{"not a function", "export(\"oak_ml_k\") pub K: u32 = 3\nmain: (): i32 { i32(0) }\n", "must be followed by a pub function declaration"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			_, err := New().WithSource("main.oak", tc.src).EmitC().Get()
			if err == nil {
				t.Fatal("expected the export to be rejected")
			}
			if !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("error lacks %q:\n%v", tc.want, err)
			}
		})
	}
}

// A dependency's plain pub functions are not part of the C surface: only
// explicit exports and the root's pub functions reach the header.
func TestHeaderOmitsDependencyInternalNames(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":     "module example.com/ml\noak 0.1.0\n",
		"ops/ops.oak": "package ops\npub add: (a: i32, b: i32): i32 = a + b\n",
		"main.oak":    "import(\"example.com/ml/ops\")\nmain: (): i32 { ops.add(1, 2) }\n",
	})
	header, err := New().WithPackageDir(root).EmitHeader().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(header, "__add") || strings.Contains(header, "oak_example") {
		t.Fatalf("header leaks the dependency's internal name:\n%s", header)
	}
}
