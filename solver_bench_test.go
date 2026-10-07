package main

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"
)

// Build outside the timed region. Each iteration includes a fresh process
// and the whole self-hosted proof pipeline, including certificate checks.
func BenchmarkOakShell(b *testing.B) {
	solver, err := oakSolverBinary()
	if err != nil {
		b.Fatal(err)
	}
	for _, name := range []string{"layout.oak", "intrinsics.oak", "extents.oak"} {
		b.Run(name, func(b *testing.B) {
			source, err := filepath.Abs(filepath.Join("spec", "oak", name))
			if err != nil {
				b.Fatal(err)
			}
			for b.Loop() {
				ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
				cmd := exec.CommandContext(ctx, solver)
				cmd.Env = append(os.Environ(), "OAK_SOLVER_MODE=prove", "OAK_PROVE_FILE="+source, "OAK_PROVE_CASES=65536")
				output, err := cmd.CombinedOutput()
				cancel()
				if err != nil {
					b.Fatalf("%v: %s", err, output)
				}
			}
		})
	}
}
