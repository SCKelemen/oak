package main

import (
	"context"
	"github.com/SCKelemen/oak/asm"
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

// Repeated identical laws with alternating good/bad variable orders expose
// head-of-line blocking: each worker is the fast one on every other job.
func alternatingSolverJobs() []oakTheorem {
	problem := func(blocked bool) asm.Problem {
		const width = 16
		words := make([]uint32, 8+2*65+5*8+1)
		words[0], words[1], words[2], words[3] = 5, 2, 1, 65536
		for leaf := 0; leaf < 2; leaf++ {
			at := 8 + leaf*65
			words[at] = width
			for bit := 0; bit < 64; bit++ {
				words[at+1+bit] = ^uint32(0)
			}
			for bit := 0; bit < width; bit++ {
				v := bit*2 + leaf
				if blocked {
					v = leaf*width + bit
				}
				words[at+1+bit] = uint32(v)
			}
		}
		at := 8 + 2*65
		copy(words[at:], []uint32{
			0, 0, width, 0, 0, 0, 0, 0,
			0, 0, width, 1, 0, 0, 0, 0,
			2, 3, width, 0, 1, 0, 0, 0,
			2, 3, width, 1, 0, 0, 0, 0,
			3, 0, 1, 2, 3, 0, 0, 0,
			4,
		})
		return asm.Problem{Words: words, Terms: 5, Leaves: 2}
	}
	good, bad := problem(false), problem(true)
	jobs := make([]oakTheorem, 8)
	for i := range jobs {
		jobs[i] = oakTheorem{Problems: []asm.Problem{good, bad}}
		if i%2 == 0 {
			jobs[i].Problems = []asm.Problem{bad, good}
		}
	}
	return jobs
}

func BenchmarkOakAlternatingOrders(b *testing.B) {
	if _, err := oakSolverBinary(); err != nil {
		b.Fatal(err)
	}
	jobs := alternatingSolverJobs()
	for b.Loop() {
		vs, err := runOakSolver(jobs, nil, 0, 65536)
		if err != nil {
			b.Fatal(err)
		}
		for _, v := range vs {
			if v.Status != 0 {
				b.Fatalf("unexpected verdict %+v", v)
			}
		}
	}
}
