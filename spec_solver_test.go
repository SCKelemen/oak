package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// TestOakSolverAgrees runs the default prover — the solver written in Oak
// (prove/solver/bdd.oak) deciding the bit-level rung, the Go decider
// replaying the winning order — over the self-hosted law corpus (spec/oak)
// and requires every verdict to agree node for node: the two solvers are
// twins, and a difference in either is a bug in one of them.
func TestOakSolverAgrees(t *testing.T) {
	files, err := filepath.Glob(filepath.Join("spec", "oak", "*.oak"))
	if err != nil || len(files) == 0 {
		t.Fatalf("spec/oak: %v (%d files)", err, len(files))
	}
	for _, file := range files {
		file := file
		if strings.HasSuffix(file, "_lean.oak") {
			continue // open theorems awaiting Lean; nothing for the solver to replay
		}
		t.Run(filepath.Base(file), func(t *testing.T) {
			code, out := runCLI(t, func(args []string) int { return proveCommand(args, os.Stdout, os.Stderr) }, []string{"-solver", "oak", "-cross", "go", file})
			if code != 0 || strings.Contains(out, "disagrees") || strings.Contains(out, "cannot restate") {
				t.Fatalf("exit %d:\n%s", code, out)
			}
		})
	}
}

// TestOakSolverSelfCheck runs the solver package's own main: the diagram
// laws on a few nodes and a hand-built problem through solve.
func TestOakSolverSelfCheck(t *testing.T) {
	code, out := runCLI(t, runPackage, []string{filepath.Join("prove", "solver")})
	if code != 0 {
		t.Fatalf("exit %d:\n%s", code, out)
	}
}
