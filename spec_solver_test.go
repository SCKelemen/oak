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
			// These law files are in the Oak lowering's subset: every
			// bit-level row there must have been lowered in Oak as well.
			if scalarLawFiles[filepath.Base(file)] {
				for _, line := range strings.Split(out, "\n") {
					if strings.Contains(line, "at the bit level") && !strings.Contains(line, "lowered and decided in Oak") {
						t.Fatalf("not lowered in Oak: %s", line)
					}
				}
			}
		})
	}
}

// scalarLawFiles are the law files whose bit-level theorems the Oak
// lowering must all take: every decided file of the corpus (the Lean
// file's open theorems aside).
var scalarLawFiles = map[string]bool{"layout.oak": true, "discharge.oak": true, "extents.oak": true, "intrinsics.oak": true, "witnesses.oak": true, "floats.oak": true, "adts.oak": true, "effects.oak": true, "mono.oak": true, "shapes.oak": true, "patterns.oak": true, "sums.oak": true, "lattice.oak": true}

// TestOakSolverSelfCheck runs the solver package's own main: the diagram
// laws on a few nodes and a hand-built problem through solve.
func TestOakSolverSelfCheck(t *testing.T) {
	code, out := runCLI(t, runPackage, []string{filepath.Join("prove", "solver")})
	if code != 0 {
		t.Fatalf("exit %d:\n%s", code, out)
	}
}
