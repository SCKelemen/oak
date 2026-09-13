package main

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

const satRungSource = `
shift_is_double: theorem (x: u32) { x << u32(1) == x + x }
mask_bound: theorem (x: u64, m: u64) { (x & m) <= m }
overflow: theorem (x: u32) { x + u32(1) > x }
main: (): i32 = 0
`

func writeSatRungFile(t *testing.T) string {
	dir := t.TempDir()
	path := filepath.Join(dir, "laws.oak")
	if err := os.WriteFile(path, []byte(satRungSource), 0o644); err != nil {
		t.Fatal(err)
	}
	return path
}

// Without a solver the rung is skipped by name and the rows stand.
func TestCertificateRungSkipsWithoutSolver(t *testing.T) {
	t.Setenv("OAK_SAT_SOLVER", "oak-no-such-solver")
	var out, errOut bytes.Buffer
	proveCommand([]string{"-solver", "sat", writeSatRungFile(t)}, &out, &errOut)
	text := out.String()
	for _, want := range []string{"the certificate rung was skipped", "decided   mask_bound: at the bit level", "refuted   overflow: counterexample"} {
		if !strings.Contains(text, want) {
			t.Fatalf("output lacks %q:\n%s%s", want, text, errOut.String())
		}
	}
}

// -cnf writes one DIMACS file per bit-level obligation.
func TestCertificateRungWritesClauses(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "cnf")
	var out, errOut bytes.Buffer
	proveCommand([]string{"-solver", "go", "-cnf", dir, writeSatRungFile(t)}, &out, &errOut)
	for _, name := range []string{"mask_bound", "overflow"} {
		text, err := os.ReadFile(filepath.Join(dir, name+".cnf"))
		if err != nil {
			t.Fatalf("%s: %v\n%s", name, err, out.String())
		}
		if !strings.HasPrefix(string(text), "c oak prove: "+name+"\np cnf ") {
			t.Fatalf("%s: header %q", name, string(text)[:40])
		}
	}
}

// A solver whose answers cannot be confirmed changes no row: a model the
// clause engine rejects, and a certificate the checkers refuse.
func TestCertificateRungTrustsOnlyCheckedAnswers(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("the fake solver is a shell script")
	}
	dir := t.TempDir()
	fake := func(name, script string) string {
		path := filepath.Join(dir, name)
		if err := os.WriteFile(path, []byte("#!/bin/sh\n"+script), 0o755); err != nil {
			t.Fatal(err)
		}
		return path
	}
	// A "model" of one literal that satisfies nothing about the obligation.
	t.Setenv("OAK_SAT_SOLVER", fake("model", "echo 's SATISFIABLE'\necho 'v 1 0'\nexit 10\n"))
	var out, errOut bytes.Buffer
	proveCommand([]string{"-solver", "sat", writeSatRungFile(t)}, &out, &errOut)
	if text := out.String(); !strings.Contains(text, "decided   mask_bound: at the bit level") || !strings.Contains(text, "model is not a counterexample") {
		t.Fatalf("a bogus model must change no row:\n%s%s", text, errOut.String())
	}
	// An "unsatisfiable" verdict with a certificate that proves nothing.
	t.Setenv("OAK_SAT_SOLVER", fake("cert", "echo 's UNSATISFIABLE'\necho '1 0 1 0' > \"$4\"\nexit 20\n"))
	out.Reset()
	errOut.Reset()
	proveCommand([]string{"-solver", "sat", writeSatRungFile(t)}, &out, &errOut)
	text := out.String()
	if !strings.Contains(text, "refuted   overflow: counterexample") || !strings.Contains(text, "certificate was refused, so its verdict does not count") {
		t.Fatalf("a refused certificate must change no row:\n%s%s", text, errOut.String())
	}
	if strings.Contains(text, "an LRAT certificate") {
		t.Fatalf("no certificate was accepted, none may be reported:\n%s", text)
	}
}

// With a real solver on the machine the whole path runs: the machines law
// file's step obligation closes with a certificate both checkers accept,
// and no row disagrees with the ladder. Skipped where no solver is
// installed.
func TestCertificateRungWithSolver(t *testing.T) {
	run := func(t *testing.T) {
		var out, errOut bytes.Buffer
		proveCommand([]string{"-solver", "sat", filepath.Join("spec", "oak", "machines.oak")}, &out, &errOut)
		text := out.String()
		for _, want := range []string{"bounded__step: at the bit level", "an LRAT certificate of", "checked in Go and in Oak", "oak prove: 15 decided"} {
			if !strings.Contains(text, want) {
				t.Fatalf("output lacks %q:\n%s%s", want, text, errOut.String())
			}
		}
		if strings.Contains(text, "disagrees") || strings.Contains(text, "was skipped") {
			t.Fatalf("a row disagrees or the rung was skipped:\n%s", text)
		}
	}
	t.Run("oak solver", func(t *testing.T) {
		t.Setenv("OAK_SAT_SOLVER", "")
		run(t)
	})
	t.Run("cadical", func(t *testing.T) {
		if _, err := exec.LookPath("cadical"); err != nil {
			t.Skip("no cadical on this machine")
		}
		t.Setenv("OAK_SAT_SOLVER", "cadical")
		run(t)
	})
}
