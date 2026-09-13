package compiler

import (
	"strings"
	"testing"
)

// Measured constants (docs/spec/60-effects-allocation.md section 10b; the
// ml pilot's ask 5.21): `TILE: u32 (measured: 2, 8) = 4` runs with the
// value the load supplies within the range — OAK_MEASURED_TILE in the
// environment for the interpreter and the compiled program alike — and
// with the pinned value otherwise; a value outside the range stops the
// program before main.
const measuredProgram = `package main

TILE: u32 (measured: 2, 8) = 4
DEPTH: i32 (measured: -4, 4) = -1

tiles: (n: u32): u32 = (n + TILE - 1) / TILE

main: (): i32 = {
  i32_bits_u32(tiles(16)) * 10 + DEPTH + 1
}
`

func TestE2EMeasuredConstants(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": measuredProgram})
	// Pinned: 16 / 4 = 4 tiles, DEPTH -1.
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 40 {
		t.Fatalf("pinned: exit=(%d,%v)", code, abnormal)
	}
	if got := interpretModule(t, root); got != 40 {
		t.Fatalf("pinned interpreted: %d", got)
	}
	// Supplied within the range: 16 / 2 = 8 tiles, DEPTH 3.
	t.Setenv("OAK_MEASURED_TILE", "2")
	t.Setenv("OAK_MEASURED_DEPTH", "3")
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 84 {
		t.Fatalf("supplied: exit=(%d,%v)", code, abnormal)
	}
	if got := interpretModule(t, root); got != 84 {
		t.Fatalf("supplied interpreted: %d", got)
	}
	// Outside the range, or not an integer: the program stops before main.
	for _, bad := range []string{"9", "1", "-3", "abc", "2x"} {
		t.Setenv("OAK_MEASURED_TILE", bad)
		if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); !abnormal {
			t.Fatalf("TILE=%s must stop the program, got exit %d", bad, code)
		}
	}
	t.Setenv("OAK_MEASURED_TILE", "")
	// The C: a mutable static with the pinned value, the weak hook, the
	// range check with the constant's name, run as a constructor.
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"static u32 TILE = 4;",
		"static i32 DEPTH = -( 1 );",
		"extern int64_t oak_measured_value(const char *name, int64_t pinned) __attribute__((weak));",
		"__attribute__((constructor)) static void oak_measured_init(void)",
		`{ int64_t v = oak_measured_value("TILE", 4ll); if (v < 2ll || v > 8ll) { oak_measured_out_of_range("TILE", v, 2ll, 8ll); } TILE = (u32)v; }`,
		`{ int64_t v = oak_measured_value("DEPTH", -1ll); if (v < -4ll || v > 4ll) { oak_measured_out_of_range("DEPTH", v, -4ll, 4ll); } DEPTH = (i32)v; }`,
	} {
		if !strings.Contains(emitted, want) {
			t.Fatalf("missing %q in the C:\n%s", want, emitted)
		}
	}
	if strings.Contains(emitted, "static const u32 TILE") {
		t.Fatalf("a measured constant is never a folded C constant:\n%s", emitted)
	}
	// The semantic model lists the knobs, and the declaration prints back.
	model, err := New().WithPackageDir(root).SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	measured := model.TypeChecker.MeasuredConstants()
	if len(measured) != 2 || measured[0].Name != "TILE" || measured[0].Type != "u32" || measured[0].Lo != 2 || measured[0].Hi != 8 || measured[0].Pinned != 4 ||
		measured[1].Name != "DEPTH" || measured[1].Lo != -4 || measured[1].Pinned != -1 {
		t.Fatalf("measured = %+v", measured)
	}
	tree, err := New().WithPackageDir(root).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	if printed := tree.Root.String(); !strings.Contains(printed, "TILE: u32 (measured: 2, 8) = 4") || !strings.Contains(printed, "DEPTH: i32 (measured: -4, 4) = (-1)") {
		t.Fatalf("the clause must print back:\n%s", printed)
	}
	// The extraction: opaque within the range, the range a hypothesis.
	lean, err := New().WithPackageDir(root).EmitLean("Oak.MeasuredTest").Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"opaque TILE : UInt32",
		"variable (TILE_range : (2 : UInt32) ≤ TILE ∧ TILE ≤ (8 : UInt32))",
		"opaque DEPTH : Int32",
		"variable (DEPTH_range : (-4 : Int32) ≤ DEPTH ∧ DEPTH ≤ (4 : Int32))",
	} {
		if !strings.Contains(lean, want) {
			t.Fatalf("missing %q in the Lean:\n%s", want, lean)
		}
	}
}

// The clause is checked: an integer type, a range of that type, a pinned
// literal inside it; the constant is not assignable and never folds.
func TestE2EMeasuredConstantsRejections(t *testing.T) {
	for name, c := range map[string][2]string{
		"float type":         {"TILE: f32 (measured: 2, 8) = 4.0", "needs a fixed-width integer type"},
		"inverted range":     {"TILE: u32 (measured: 8, 2) = 4", "is not a range of u32"},
		"range past type":    {"TILE: u8 (measured: 0, 300) = 4", "is not a range of u8"},
		"pinned outside":     {"TILE: u32 (measured: 2, 8) = 9", "is outside 2..8"},
		"pinned not literal": {"TILE: u32 (measured: 2, 8) = 2 + 2", "the pinned value is an integer literal"},
		"no pinned value":    {"TILE: u32 (measured: 2, 8)", "needs a pinned value"},
	} {
		src := "package main\n\n" + c[0] + "\n\nmain: (): i32 = i32_bits_u32(TILE)\n"
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
		_, err := New().WithPackageDir(root).SemanticModel().Get()
		if err == nil || !strings.Contains(err.Error(), c[1]) {
			t.Fatalf("%s: want %q, got %v", name, c[1], err)
		}
	}
	assign := "package main\n\nTILE: u32 (measured: 2, 8) = 4\n\nmain: (): i32 = {\n  TILE = 6\n  i32_bits_u32(TILE)\n}\n"
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": assign})
	if _, err := New().WithPackageDir(root).SemanticModel().Get(); err == nil || !strings.Contains(err.Error(), "measured constant TILE is not assignable") {
		t.Fatalf("assignment: %v", err)
	}
	// A later initializer may not fold a measured constant: it is not a constant.
	derived := "package main\n\nTILE: u32 (measured: 2, 8) = 4\nCELLS: u32 = TILE * 2\n\nmain: (): i32 = i32_bits_u32(CELLS)\n"
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": derived})
	if _, err := New().WithPackageDir(root).EmitC().Get(); err == nil || !strings.Contains(err.Error(), "not a compile-time constant") {
		t.Fatalf("derived: %v", err)
	}
	// The clause form is one of two.
	bad := "package main\n\nTILE: u32 (tuned: 2, 8) = 4\n\nmain: (): i32 = i32_bits_u32(TILE)\n"
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": bad})
	if _, err := New().WithPackageDir(root).Parse().Get(); err == nil || !strings.Contains(err.Error(), "(measured: lo, hi)") {
		t.Fatalf("unknown clause: %v", err)
	}
}
