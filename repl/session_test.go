package repl

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func writeFiles(t *testing.T, files map[string]string) string {
	t.Helper()
	root := t.TempDir()
	for name, text := range files {
		path := filepath.Join(root, filepath.FromSlash(name))
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	return root
}

func TestSessionEvaluatesExpressionsAndKeepsDeclarations(t *testing.T) {
	session := NewSession(t.TempDir())
	outcome, err := session.Submit("twice: (v: i32): i32 = v * 2")
	if err != nil || !outcome.Committed || outcome.Type == nil {
		t.Fatalf("declaration: %+v %v", outcome, err)
	}
	outcome, err = session.Submit("twice(21)")
	if err != nil || outcome.Value == nil || outcome.Value.Inspect() != "42" {
		t.Fatalf("expression: %+v %v", outcome, err)
	}
	if outcome.Committed {
		t.Fatal("expressions must not join the session")
	}
	if _, err := session.Submit("twice(true)"); err == nil || !strings.Contains(err.Error(), "type") {
		t.Fatalf("type errors must surface: %v", err)
	}
	// A rejected declaration does not join the session.
	if _, err := session.Submit("bad: (v: i32): i32 = v + true"); err == nil {
		t.Fatal("bad declaration accepted")
	}
	if strings.Contains(session.Source(), "bad") {
		t.Fatal("rejected declaration was kept")
	}
	typ, err := session.TypeOf("twice(1)")
	if err != nil || typ.String() != "i32" {
		t.Fatalf("typeof = %v %v", typ, err)
	}
}

func TestSessionResolvesImportsThroughTheEnclosingModule(t *testing.T) {
	root := writeFiles(t, map[string]string{
		"oak.mod": "module example.com/hello\n",
		"geometry/point.oak": `package geometry

pub(opaque) Point: type = struct { x: i32, y: i32 }
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
pub sum: (p: Point): i32 = p.x + p.y
pub Shape: type = Dot | Line: i32
pub length: (s: Shape): i32 = s ? .Dot => 0 | .Line(n) => n
`,
	})
	session := NewSession(filepath.Join(root, "geometry"))
	if _, err := session.Submit(`geo := import("example.com/hello/geometry")`); err != nil {
		t.Fatalf("import: %v", err)
	}
	outcome, err := session.Submit("geo.sum(geo.make(20, 22))")
	if err != nil || outcome.Value == nil || outcome.Value.Inspect() != "42" {
		t.Fatalf("qualified call: %+v %v", outcome, err)
	}
	outcome, err = session.Submit("geo.length(geo.Shape.Line(7))")
	if err != nil || outcome.Value == nil || outcome.Value.Inspect() != "7" {
		t.Fatalf("qualified variant: %+v %v", outcome, err)
	}
	// Opacity holds in the REPL too.
	if _, err := session.Submit("geo.make(1, 2).x"); err == nil || !strings.Contains(err.Error(), "OAK-M0110") {
		t.Fatalf("opaque projection must be rejected: %v", err)
	}
	// Derived declarations and sealed imports work as in a build.
	if _, err := session.Submit("P: type = struct { a: u8 }"); err != nil {
		t.Fatal(err)
	}
	if _, err := session.Submit("p_eq: (x: P, y: P): Bool = derive.equal"); err != nil {
		t.Fatal(err)
	}
	outcome, err = session.Submit("p_eq(P { a: 1 }, P { a: 1 })")
	if err != nil || outcome.Value == nil || outcome.Value.Inspect() != "true" {
		t.Fatalf("derive in session: %+v %v", outcome, err)
	}
}

func TestSessionOutsideAModuleUsesTheBootstrapLibrary(t *testing.T) {
	session := NewSession(t.TempDir())
	if _, err := session.Submit("import(std)"); err != nil {
		t.Fatalf("bootstrap import: %v", err)
	}
	outcome, err := session.Submit("ascii_upper(u8(97))")
	if err != nil || outcome.Value == nil || outcome.Value.Inspect() != "65" {
		t.Fatalf("prelude call: %+v %v", outcome, err)
	}
	if _, err := session.Submit(`import("example.com/other/pkg")`); err == nil {
		t.Fatal("an unresolvable import must be rejected")
	}
}

func TestSessionObligationsAndStrict(t *testing.T) {
	session := NewSession(t.TempDir())
	if _, err := session.Submit("spin: (n: u32): u32 = { i: u32 = 0\n  while i < n { i = i + 1 }\n  i }"); err != nil {
		t.Fatal(err)
	}
	if _, err := session.Submit("loop: (): u32 = { i: u32 = 0\n  running: Bool = true\n  while running { i = i + 1\n    running = i < 10 }\n  i }"); err != nil {
		t.Fatal(err)
	}
	open, err := session.Obligations()
	if err != nil {
		t.Fatal(err)
	}
	found := false
	for _, d := range open {
		if d.Code == "OAK-D0103" {
			found = true
		}
	}
	if !found {
		t.Fatalf("expected the unbounded-loop assumption among obligations, got %d: %+v", len(open), open)
	}
	// Under the strict profile the same declaration is rejected.
	strict := NewSession(t.TempDir())
	strict.Strict = true
	if _, err := strict.Submit("loop: (): u32 = { i: u32 = 0\n  running: Bool = true\n  while running { i = i + 1\n    running = i < 10 }\n  i }"); err == nil || !strings.Contains(err.Error(), "OAK-D0103") {
		t.Fatalf("strict profile must reject the recorded assumption, got %v", err)
	}
	// Expressions still evaluate under strict: their wrapper is judged in the
	// default profile.
	if _, err := session.Submit("spin(3)"); err != nil {
		t.Fatal(err)
	}
}

func TestLawsCoverRecordedAssumptionCodes(t *testing.T) {
	for _, code := range []string{"OAK-D0103", "OAK-D0102", "OAK-B0110", "OAK-T0501"} {
		if _, ok := LawFor(code); !ok {
			t.Fatalf("no law recorded for %s", code)
		}
	}
	if _, ok := LawFor("OAK-X9999"); ok {
		t.Fatal("unknown codes must not claim a law")
	}
}
