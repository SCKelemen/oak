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
		var out, errOut bytes.Buffer
		proveCommand([]string{"-solver", "sat", filepath.Join("spec", "oak", "machines.oak")}, &out, &errOut)
		if !strings.Contains(out.String(), "lowered to clauses in Oak, checked in Go and in Oak; the Go clause engine agrees") {
			t.Fatalf("the Oak path must lower, solve, and check in Oak with the Go engine agreeing:\n%s", out.String())
		}
	})
	t.Run("cadical", func(t *testing.T) {
		if _, err := exec.LookPath("cadical"); err != nil {
			t.Skip("no cadical on this machine")
		}
		t.Setenv("OAK_SAT_SOLVER", "cadical")
		run(t)
	})
}

// The prover written in Oak certifies in its own process: a row the
// diagram decided also carries an LRAT certificate lowered, solved, and
// checked in Oak, and the Go ladder agrees on every row.
func TestOakShellCertificates(t *testing.T) {
	var out, errOut bytes.Buffer
	code := proveCommand([]string{"-solver", "self", "-cross", "go", filepath.Join("spec", "oak", "machines.oak")}, &out, &errOut)
	text := out.String()
	if code != 0 {
		t.Fatalf("exit %d:\n%s%s", code, text, errOut.String())
	}
	for _, want := range []string{"bounded__step: at the bit level", "an LRAT certificate of", "lowered to clauses in Oak and checked in Oak", "the Go ladder agrees on 15 of 15 rows"} {
		if !strings.Contains(text, want) {
			t.Fatalf("output lacks %q:\n%s", want, text)
		}
	}
	if strings.Contains(text, "disagrees") {
		t.Fatalf("a certificate row disagrees:\n%s", text)
	}
}

// -conflicts bounds the solver on both paths: under a budget of one
// conflict every row that needs learning gives up, on the Go-driven rung
// and inside the shell, and the rows keep the ladder's verdict.
func TestCertificateRungBudget(t *testing.T) {
	var out, errOut bytes.Buffer
	code := proveCommand([]string{"-solver", "sat", "-conflicts", "1", filepath.Join("spec", "oak", "machines.oak")}, &out, &errOut)
	if code != 0 {
		t.Fatalf("exit %d:\n%s%s", code, out.String(), errOut.String())
	}
	if text := out.String(); !strings.Contains(text, "the solver gave up") || strings.Contains(text, "an LRAT certificate of") {
		t.Fatalf("-solver sat -conflicts 1 must give up on every learned row:\n%s", text)
	}
	out.Reset()
	errOut.Reset()
	code = proveCommand([]string{"-solver", "self", "-cross", "none", "-conflicts", "1", filepath.Join("spec", "oak", "machines.oak")}, &out, &errOut)
	if code != 0 {
		t.Fatalf("exit %d:\n%s%s", code, out.String(), errOut.String())
	}
	if text := out.String(); !strings.Contains(text, "the certificate rung gave no verdict") || strings.Contains(text, "an LRAT certificate of") || !strings.Contains(text, "bounded__step: at the bit level") {
		t.Fatalf("-solver self -conflicts 1 must give up on every learned row and keep the diagram's verdict:\n%s", text)
	}
}

// The default budget scales with the obligation: the extents row that
// needs 562,050 conflicts closes by certificate under the scaled budget
// (100 per clause over 6,442 clauses), while the row that needs 1.4
// million still gives up, so the corpus pays only for what closes.
func TestScaledBudgetClosesWideRow(t *testing.T) {
	var out, errOut bytes.Buffer
	code := proveCommand([]string{"-solver", "sat", filepath.Join("spec", "oak", "extents.oak")}, &out, &errOut)
	if code != 0 {
		t.Fatalf("exit %d:\n%s%s", code, out.String(), errOut.String())
	}
	rows := map[string]string{}
	for _, line := range strings.Split(out.String(), "\n") {
		fields := strings.Fields(line)
		if len(fields) >= 2 {
			rows[strings.TrimSuffix(fields[1], ":")] = line
		}
	}
	if row := rows["vector_under_literal_bound"]; !strings.Contains(row, "an LRAT certificate of") {
		t.Fatalf("vector_under_literal_bound must close by certificate under the scaled budget:\n%s", row)
	}
	if row := rows["vector_under_offset_bound"]; !strings.Contains(row, "the solver gave up") {
		t.Fatalf("vector_under_offset_bound is expected to give up under the scaled budget:\n%s", row)
	}
}
