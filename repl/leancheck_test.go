package repl

import (
	"context"
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func trustProject(t *testing.T) string {
	t.Helper()
	if _, err := exec.LookPath("lake"); err != nil {
		t.Skip("lake not on PATH")
	}
	dir := t.TempDir()
	toolchain, err := os.ReadFile("../spec/lean/lean-toolchain")
	if err != nil {
		t.Fatal(err)
	}
	for name, data := range map[string]string{"lakefile.toml": "name = \"trust-test\"\n", "lean-toolchain": string(toolchain)} {
		if err := os.WriteFile(filepath.Join(dir, name), []byte(data), 0600); err != nil {
			t.Fatal(err)
		}
	}
	t.Setenv("OAK_LEAN_DIR", dir)
	return dir
}

func checkTrust(t *testing.T, text string) *CheckReport {
	t.Helper()
	path := filepath.Join(t.TempDir(), "check.lean")
	report, err := NewSession(".").LeanCheck(text, path)
	if err != nil {
		t.Fatal(err)
	}
	saved, err := os.ReadFile(path)
	if err != nil || string(saved) != text {
		t.Fatalf("source was changed: %v", err)
	}
	return report
}

func TestLeanCheckTransitiveTrust(t *testing.T) {
	dir := trustProject(t)
	// The imported admission must not issue any warning in the checked source.
	imported := filepath.Join(dir, "Admitted.lean")
	if err := os.WriteFile(imported, []byte("namespace Fixture\ntheorem admitted : False := by sorry\ntheorem alias : False := admitted\nend Fixture\n"), 0600); err != nil {
		t.Fatal(err)
	}
	lake, _ := exec.LookPath("lake")
	output, stderr, err := runLean(context.Background(), lake, dir, nil, "--json", "--root="+dir, "-o", filepath.Join(dir, "Admitted.olean"), imported)
	if err != nil {
		t.Fatalf("fixture: %v %s %s", err, output, stderr)
	}
	t.Setenv("LEAN_PATH", dir)
	report := checkTrust(t, `import Admitted
namespace Checks
theorem imported_alias : False := Fixture.alias
theorem closed : True := by trivial
private theorem hidden : True := by trivial
@[simp] theorem attributed : 1 = 1 := rfl
theorem native_result : 2 + 2 = 4 := by native_decide
axiom platformWordSize : Nat
theorem parameter_result : platformWordSize = platformWordSize := rfl
axiom assumed_fact : False
theorem assumed_result : False := assumed_fact
theorem logical : ∀ p : Prop, p ∨ ¬ p := Classical.em
-- OAK-OBLIGATION pending: open
def pending : Prop := False
-- OAK-OBLIGATION pending_parameterized: open
def pending_parameterized (n : Nat) : Prop := n = 0
-- OAK-OBLIGATION untranslated: unsupported
-- no formal proposition for this claim
end Checks
`)
	if !report.Complete {
		t.Fatalf("incomplete:\n%s", report)
	}
	want := map[string]Verdict{"imported_alias": Open, "closed": Proved, "hidden": Proved, "attributed": Proved, "native_result": Native, "parameter_result": Conditional, "assumed_result": Assumed, "logical": Proved, "pending": Open, "pending_parameterized": Open, "untranslated": Open}
	for _, theorem := range report.Theorems {
		expected, ok := want[theorem.Name]
		if !ok {
			t.Fatalf("unexpected theorem %+v", theorem)
		}
		if theorem.Verdict != expected {
			t.Fatalf("%s = %s, want %s\n%s", theorem.Name, theorem.Verdict, expected, report)
		}
		delete(want, theorem.Name)
	}
	if len(want) != 0 {
		t.Fatalf("missing verdicts: %v\n%s", want, report)
	}
	for _, dependency := range []string{"admission: sorryAx", "native:", "parameter: Checks.platformWordSize", "assumption: Checks.assumed_fact", "logical: Classical.choice"} {
		if !strings.Contains(report.String(), dependency) {
			t.Fatalf("missing %q\n%s", dependency, report)
		}
	}
}

func TestLeanCheckUnrelatedErrorsFailClosed(t *testing.T) {
	trustProject(t)
	for _, source := range []string{
		"def unrelated : Nat := true\ntheorem closed : True := by trivial\n",
		"theorem closed : True := by trivial\ndef unrelated : Nat := true\n",
		"import MissingModule\ntheorem closed : True := by trivial\n",
		"theorem closed : True := by trivial\n#error \"stop\"\n",
	} {
		report := checkTrust(t, source)
		if report.Complete {
			t.Fatalf("certified invalid file:\n%s", report)
		}
		for _, theorem := range report.Theorems {
			if theorem.Verdict != Failed {
				t.Fatalf("not failed closed:\n%s", report)
			}
		}
	}
}

func trustDiagnostic(t *testing.T, severity, data string) []byte {
	t.Helper()
	raw, err := json.Marshal(map[string]any{"severity": severity, "pos": map[string]int{"line": 1}, "data": data})
	if err != nil {
		t.Fatal(err)
	}
	return append(raw, '\n')
}

func TestLeanCheckDiagnosticsNeverProve(t *testing.T) {
	for name, output := range map[string][]byte{
		"empty":            nil,
		"warning":          trustDiagnostic(t, "warning", "declaration uses sorry"),
		"malformed":        []byte("{not json}\n"),
		"truncated":        []byte(`{"severity":"information"`),
		"unknown severity": []byte(`{"severity":"success","data":"done"}`),
		"scanner overflow": []byte(strings.Repeat("x", 17<<20)),
	} {
		t.Run(name, func(t *testing.T) {
			r := classify("theorem closed : True := by trivial\n", output)
			if r.Complete || len(r.Theorems) != 1 || r.Theorems[0].Verdict != Failed {
				t.Fatalf("diagnostics certified proof: %+v", r)
			}
		})
	}
}

func TestLeanCheckIncompleteAuditFailsClosed(t *testing.T) {
	text := "theorem closed : True := by trivial\n"
	for name, data := range map[string]string{
		"missing":              `{}`,
		"wrong token":          `{"oakTrust":"other","declarations":[]}`,
		"missing declarations": `{"oakTrust":"token"}`,
		"missing coverage":     `{"oakTrust":"token","declarations":[]}`,
		"missing axioms":       `{"oakTrust":"token","declarations":[{"name":"closed","line":1,"kind":"theorem"}]}`,
		"wrong name":           `{"oakTrust":"token","declarations":[{"name":"unrelated","line":1,"kind":"theorem","axioms":[]}]}`,
		"wrong kind":           `{"oakTrust":"token","declarations":[{"name":"closed","line":1,"kind":"other","axioms":[]}]}`,
		"bad line":             `{"oakTrust":"token","declarations":[{"name":"closed","line":-1,"kind":"theorem","axioms":[]}]}`,
	} {
		t.Run(name, func(t *testing.T) {
			r := classify(text, nil)
			if err := r.applyAudit(text, trustDiagnostic(t, "information", data), "token"); err == nil {
				t.Fatalf("accepted incomplete audit: %+v", r)
			}
			if r.Complete || r.Theorems[0].Verdict != Failed {
				t.Fatal("partial result promoted")
			}
		})
	}
}

func TestLeanCheckProcessFailureNeverProves(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "lakefile.toml"), nil, 0600); err != nil {
		t.Fatal(err)
	}
	t.Setenv("OAK_LEAN_DIR", dir)
	fake := filepath.Join(dir, "lake")
	if err := os.WriteFile(fake, []byte("#!/bin/sh\nexit 7\n"), 0700); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", dir+string(os.PathListSeparator)+os.Getenv("PATH"))
	r := checkTrust(t, "theorem closed : True := by trivial\n")
	if r.Complete || r.Theorems[0].Verdict != Failed || !strings.Contains(r.String(), "exit status 7") {
		t.Fatalf("exit failure lost: %s", r)
	}
	ctx, cancel := context.WithDeadline(context.Background(), time.Now().Add(-time.Second))
	defer cancel()
	_, _, err := runLean(ctx, fake, dir, nil, "--json")
	if err == nil {
		t.Fatal("expired context succeeded")
	}
}

func TestLeanAxiomKinds(t *testing.T) {
	for _, test := range []struct {
		name string
		prop bool
		want string
	}{
		{"sorryAx", false, "admission"}, {"Classical.choice", false, "logical"}, {"propext", true, "logical"}, {"Quot.sound", true, "logical"},
		{"T._native.bv_decide.ax_1_5", true, "native"}, {"T._native.native_decide.ax_1_1", true, "native"}, {"Lean.ofReduceBool", true, "native"},
		{"platformWordSize", false, "parameter"}, {"customAxiom", true, "assumption"},
	} {
		if got := axiomKind(test.name, test.prop); got != test.want {
			t.Errorf("%s: %s, want %s", test.name, got, test.want)
		}
	}
}

func TestLeanCheckModernPrivateDeclarations(t *testing.T) {
	trustProject(t)
	r := checkTrust(t, "module\n@[simp] private theorem hidden : True := by trivial\npublic theorem visible : True := hidden\n")
	if !r.Complete || len(r.Theorems) != 2 {
		t.Fatalf("modern private inventory: %s", r)
	}
	for _, v := range r.Theorems {
		if v.Verdict != Proved {
			t.Fatalf("modern private proof: %s", r)
		}
	}
}

func TestLeanCheckNativeBitvector(t *testing.T) {
	trustProject(t)
	r := checkTrust(t, "import Std.Tactic.BVDecide\ntheorem bitvector (x : BitVec 8) : ((x + 1) &&& 1) = ((x &&& 1) ^^^ 1) := by bv_decide\n")
	if !r.Complete || len(r.Theorems) != 1 || r.Theorems[0].Verdict != Native {
		t.Fatalf("bv_decide trust: %s", r)
	}
}
