package main

import (
	"os"
	"path/filepath"
	"runtime"
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

// theoremConstantsLaws name a package constant and reason about a
// remainder (prove/theorem_constants_test.go). The Oak lowering does not
// take them yet, so the Oak solver decides the Go lowering's serialized
// problem and the Go decider's replay must build the same diagram. Both
// blasters spell a comparison's eq bit by bit from the most significant
// bit down (asm/blast.go condition, prove/solver/bdd.oak bit_equality);
// when the twins drifted, every row here was a disagreement.
const theoremConstantsLaws = `
GAP: u32 = 4
CATALOG: u32 = 5

inset_len: (side: u32, gap: u32): u32 = side > gap * u32(2) ? side - gap * u32(2) | u32(0)

step: (c: u32, n: u32): u32 = n == u32(0) ? u32(0) | (c + u32(1)) % n

inset_fits: theorem (side: u32) { inset_len(side, GAP) <= side }

cursor_in_range: theorem (c: u32) { step(c, CATALOG) < CATALOG }

main: (): i32 = 0
`

func TestOakSolverAgreesOnSerializedProblems(t *testing.T) {
	file := filepath.Join(t.TempDir(), "constants.oak")
	if err := os.WriteFile(file, []byte(theoremConstantsLaws), 0o644); err != nil {
		t.Fatal(err)
	}
	code, out := runCLI(t, func(args []string) int { return proveCommand(args, os.Stdout, os.Stderr) }, []string{"-solver", "oak", "-cross", "go", file})
	if code != 0 || strings.Contains(out, "disagrees") || strings.Count(out, "the Oak solver); the Go decider agrees") != 2 {
		t.Fatalf("exit %d:\n%s", code, out)
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

// TestOakShellAgrees runs the prover written in Oak (-solver self: the
// file to the rows and the Lean projection, no Go on the path) on every law
// file and requires the Go ladder to agree on every row's status and the
// Go extractor to agree with the projection byte for byte.
func TestOakShellAgrees(t *testing.T) {
	shellAgrees(t)
}

// TestOakShellAgreesNative runs the same check with the prover built
// through the verified native backend (docs/spec/94-assembler.md §9,
// sixteenth increment; OAK_SOLVER_NATIVE=1): every function the backend
// reaches is checked, verified against its Oak body, and encoded by the
// Oak assembler, and the rows must be the C build's — the C realization is
// the oracle for the machine code.
func TestOakShellAgreesNative(t *testing.T) {
	if runtime.GOARCH != "arm64" {
		t.Skip("the native backend's host lane is AArch64")
	}
	t.Setenv("OAK_SOLVER_NATIVE", "1")
	shellAgrees(t)
}

func shellAgrees(t *testing.T) {
	files, err := filepath.Glob(filepath.Join("spec", "oak", "*.oak"))
	if err != nil || len(files) == 0 {
		t.Fatalf("spec/oak: %v (%d files)", err, len(files))
	}
	for _, file := range files {
		file := file
		if strings.HasSuffix(file, "_lean.oak") {
			continue // open theorems awaiting Lean: TestOakLeanAgrees projects them
		}
		t.Run(filepath.Base(file), func(t *testing.T) {
			out := filepath.Join(t.TempDir(), "out.lean")
			code, text := runCLI(t, func(args []string) int { return proveCommand(args, os.Stdout, os.Stderr) }, []string{"-solver", "self", "-cross", "go", "-witness", "-lean", out, file})
			if code != 0 || strings.Contains(text, "disagrees") || !strings.Contains(text, "the Go ladder agrees on") || strings.Contains(text, "agrees on 0 of") || !strings.Contains(text, "the Lean projection agrees with the Go extractor") {
				t.Fatalf("exit %d:\n%s", code, text)
			}
			// The compiled witness, driven from the shell, annotates the
			// rows whose domains the driver enumerates.
			if witnessedLawFiles[filepath.Base(file)] != strings.Contains(text, "witnessed in the compiled program") {
				t.Fatalf("witness annotation mismatch:\n%s", text)
			}
		})
	}
}

// witnessedLawFiles are the law files with a theorem the compiled
// witness's driver enumerates (the rest have only bit-level rows over
// wide or aggregate parameters).
var witnessedLawFiles = map[string]bool{"discharge.oak": true, "effects.oak": true, "floats.oak": true, "intrinsics.oak": true, "lattice.oak": true, "machines.oak": true, "patterns.oak": true, "protocols.oak": true, "quantifiers.oak": true, "shapes.oak": true, "witnesses.oak": true}

// TestOakLeanAgrees projects the law files whose theorems are left to Lean
// (the ones the ladder reports open) with the prover written in Oak and
// requires the Go extractor to agree byte for byte; the rows may be open.
func TestOakLeanAgrees(t *testing.T) {
	files, err := filepath.Glob(filepath.Join("spec", "oak", "*_lean.oak"))
	if err != nil || len(files) == 0 {
		t.Fatalf("spec/oak: %v (%d files)", err, len(files))
	}
	for _, file := range files {
		file := file
		t.Run(filepath.Base(file), func(t *testing.T) {
			out := filepath.Join(t.TempDir(), "out.lean")
			code, text := runCLI(t, func(args []string) int { return proveCommand(args, os.Stdout, os.Stderr) }, []string{"-solver", "self", "-cross", "go", "-lean", out, file})
			if code > 1 || strings.Contains(text, "disagrees") || strings.Contains(text, "differs") || !strings.Contains(text, "the Lean projection agrees with the Go extractor") {
				t.Fatalf("exit %d:\n%s", code, text)
			}
		})
	}
}
