package main

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

// Language errors must be rejected before any solver or optional output work,
// including when the self-hosted proof-decision comparison is disabled.
func TestProveRejectsInvalidSourceBeforeResults(t *testing.T) {
	cases := []struct{ name, source, diagnostic string }{
		{"duplicate", "law: theorem (a: u32, a: u32) { a == a }\n", "duplicate parameter"},
		{"operand", "law: theorem (a: u32) { (a + true) == a }\n", "requires numeric types"},
		{"unknown", "law: theorem (a: u32) { missing == a }\n", "undefined variable"},
		{"syntax", "law: theorem (a: u32 { a == a }\n", "parse failed"},
	}
	for _, mode := range []string{"go", "oak", "sat", "self"} {
		for _, cross := range []string{"go", "none"} {
			for _, c := range cases {
				t.Run(mode+"/"+cross+"/"+c.name, func(t *testing.T) {
					dir := t.TempDir()
					file := filepath.Join(dir, "original-law.oak")
					lean := filepath.Join(dir, "out.lean")
					cnf := filepath.Join(dir, "cnf")
					scratch := filepath.Join(dir, "scratch")
					if err := os.Mkdir(scratch, 0700); err != nil {
						t.Fatal(err)
					}
					// No source snapshot, solver build, or witness staging should occur.
					t.Setenv("TMPDIR", scratch)
					if err := os.WriteFile(file, []byte(c.source), 0600); err != nil {
						t.Fatal(err)
					}
					var out, errs bytes.Buffer
					code := proveCommand([]string{"-solver", mode, "-cross", cross, "-lean", lean, "-witness", "-cnf", cnf, file}, &out, &errs)
					if code != 2 || out.Len() != 0 || !strings.Contains(errs.String(), c.diagnostic) {
						t.Fatalf("exit %d, stdout %q, stderr %q", code, out.String(), errs.String())
					}
					if strings.Contains(errs.String(), "oak-prove-source-") {
						t.Fatalf("temporary source path in diagnostic: %s", &errs)
					}
					for _, path := range []string{lean, cnf} {
						if _, err := os.Stat(path); !os.IsNotExist(err) {
							t.Fatalf("unexpected output %s: %v", path, err)
						}
					}
					entries, err := os.ReadDir(scratch)
					if err != nil || len(entries) != 0 {
						t.Fatalf("validation started solver/witness work: %v, %v", entries, err)
					}
				})
			}
		}
	}
}

func TestSelfProveValidSourceProvenance(t *testing.T) {
	for _, cross := range []string{"none", "go"} {
		t.Run(cross, func(t *testing.T) {
			dir := t.TempDir()
			file := filepath.Join(dir, "law.oak")
			lean := filepath.Join(dir, "out.lean")
			if err := os.WriteFile(file, []byte("law: theorem (a: u32) { a == a }\n"), 0600); err != nil {
				t.Fatal(err)
			}
			var out, errs bytes.Buffer
			code := proveCommand([]string{"-solver", "self", "-cross", cross, "-lean", lean, file}, &out, &errs)
			if code != 0 || !strings.Contains(out.String(), "decided   law:") || !strings.Contains(out.String(), "the obligation folds to a constant in the clause engine") {
				t.Fatalf("exit %d:\n%s%s", code, &out, &errs)
			}
			compared := strings.Contains(out.String(), "the Go ladder agrees on 1 of 1 rows")
			if compared != (cross == "go") || strings.Contains(out.String(), "disagrees") {
				t.Fatalf("wrong proof provenance: %s", &out)
			}
			projection, err := os.ReadFile(lean)
			if err != nil || len(projection) == 0 {
				t.Fatalf("missing self projection: %v", err)
			}
		})
	}
}

func TestLawSourceSnapshotUnchangedAndCleaned(t *testing.T) {
	original := filepath.Join(t.TempDir(), "editing.oak")
	source := []byte("law: theorem (a: u32) { a == a }\n")
	if err := os.WriteFile(original, source, 0600); err != nil {
		t.Fatal(err)
	}
	// The same source bytes produce both the checked model (original path)
	// and the runner input; later saves do not change either one.
	model, err := compiler.New().WithSource(original, string(source)).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	snapshot, cleanup, err := snapshotLawSource(source)
	if err != nil {
		t.Fatal(err)
	}
	defer cleanup()
	if model.Tree.Source.Path != original {
		t.Fatalf("lost original source path: %q", model.Tree.Source.Path)
	}
	if err := os.WriteFile(original, []byte("law: theorem (a: u32, a: u32) { a == a }\n"), 0600); err != nil {
		t.Fatal(err)
	}
	got, err := os.ReadFile(snapshot)
	if err != nil || !bytes.Equal(got, source) || model.Tree.Source.Text != string(source) {
		t.Fatalf("changed runner/checked source: %q, %v", got, err)
	}
	cleanup()
	if _, err := os.Stat(filepath.Dir(snapshot)); !os.IsNotExist(err) {
		t.Fatalf("snapshot was not cleaned: %v", err)
	}
}

// Checking a well-typed false theorem must succeed: frontend validation is
// not a proof decision and does not require a theorem's claim to be true.
func TestProveFrontendDoesNotDecideTheorems(t *testing.T) {
	_, err := compiler.New().WithSource("false-law.oak", "law: theorem (a: u32) { a != a }\n").Check().Get()
	if err != nil {
		t.Fatalf("frontend decided a well-typed theorem: %v", err)
	}
}

// Unknown mode selectors are usage errors, never aliases for Go or for
// disabled comparison. Even a missing input must not be read first.
func TestProveRejectsInvalidModesBeforeSource(t *testing.T) {
	for _, flag := range []string{"-solver", "-cross"} {
		for _, value := range []string{"bogus", "GO", ""} {
			for _, input := range []string{"missing", "valid"} {
				t.Run(flag+"/"+value+"/"+input, func(t *testing.T) {
					dir := t.TempDir()
					file := filepath.Join(dir, "law.oak")
					if input == "valid" {
						if err := os.WriteFile(file, []byte("law: theorem (a: u32) { a == a }\n"), 0600); err != nil {
							t.Fatal(err)
						}
					}
					scratch := filepath.Join(dir, "scratch")
					if err := os.Mkdir(scratch, 0700); err != nil {
						t.Fatal(err)
					}
					t.Setenv("TMPDIR", scratch)
					lean, cnf := filepath.Join(dir, "out.lean"), filepath.Join(dir, "cnf")
					var out, errs bytes.Buffer
					code := proveCommand([]string{flag, value, "-lean", lean, "-witness", "-cnf", cnf, file}, &out, &errs)
					want := "invalid " + flag + " value"
					if code != 2 || out.Len() != 0 || !strings.Contains(errs.String(), want) {
						t.Fatalf("exit %d, stdout %q, stderr %q; want %q", code, out.String(), errs.String(), want)
					}
					for _, path := range []string{lean, cnf} {
						if _, err := os.Stat(path); !os.IsNotExist(err) {
							t.Fatalf("unexpected output %s: %v", path, err)
						}
					}
					entries, err := os.ReadDir(scratch)
					if err != nil || len(entries) != 0 {
						t.Fatalf("invalid mode started solver/witness work: %v, %v", entries, err)
					}
				})
			}
		}
	}
}
