package prove

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

// The prover's baselines (docs/notes/formal-methods-performance-2026-09.md
// section 1): the whole ladder over the repository's own specification
// files, the model built once outside the timer so the number is the
// deciders' — enumeration, the bit-level decider, liveness — and nothing
// else. Nodes reports the largest diagram a bit-level decision built, so a
// change to the BDD engine shows in the same line as its wall time.
func benchmarkSpec(b *testing.B, file string) {
	src, err := os.ReadFile(filepath.Join("..", "spec", "oak", file))
	if err != nil {
		b.Fatal(err)
	}
	model, err := compiler.New().WithSyntaxRewrite(Obligations).WithSource(file, string(src)).Check().Get()
	if err != nil {
		b.Fatal(err)
	}
	var decided, nodes int
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		results, err := Theorems(model, DefaultCases)
		if err != nil {
			b.Fatal(err)
		}
		decided, nodes = 0, 0
		for _, r := range results {
			if r.Status == Decided || r.Status == Proved {
				decided++
			}
			if r.Nodes > nodes {
				nodes = r.Nodes
			}
		}
	}
	b.ReportMetric(float64(decided), "decided")
	b.ReportMetric(float64(nodes), "largest-bdd-nodes")
}

func BenchmarkTheoremsLattice(b *testing.B)   { benchmarkSpec(b, "lattice.oak") }
func BenchmarkTheoremsEffects(b *testing.B)   { benchmarkSpec(b, "effects.oak") }
func BenchmarkTheoremsPatterns(b *testing.B)  { benchmarkSpec(b, "patterns.oak") }
func BenchmarkTheoremsProtocols(b *testing.B) { benchmarkSpec(b, "protocols.oak") }
