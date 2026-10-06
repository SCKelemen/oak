package lrat

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
	"testing"

	production "github.com/SCKelemen/oak/internal/lrat"
)

// Keep this corpus in the shared ASCII profile. The production checker and
// the experiment intentionally have different resource and grammar limits.
// This is a bounded correspondence gate, not implementation refinement.
func TestProductionLineBoundaries(t *testing.T) {
	const formula = "p cnf 1 2\n1 0\n-1 0\n"
	fixtures := []struct {
		name, proof          string
		accepted             bool
		additions, deletions int
	}{
		{"refutation", "3 0 1 2 0", true, 1, 0},
		{"delete-refutation", "3 0 1 2 0\n3 d 3 0", true, 1, 1},
		{"deleted-hint", "2 d 1 0\n3 0 1 2 0", false, 0, 0},
		{"invalid-prefix", "garbage\n3 0 1 2 0", false, 0, 0},
		{"invalid-suffix", "3 0 1 2 0\ngarbage", false, 0, 0},
		{"unjustified-suffix", "3 0 1 2 0\n4 0 0", false, 0, 0},
		{"absent-deletion", "3 0 1 2 0\n3 d 99 0", false, 0, 0},
		{"duplicate-deletion", "3 0 1 2 0\n3 d 1 1 0", false, 0, 0},
	}
	type boundaryCase struct {
		Name     string `json:"name"`
		CNF      string `json:"cnf"`
		Proof    string `json:"proof"`
		Expected bool   `json:"expected"`
	}
	var corpus []boundaryCase
	accepted := 0
	for _, fixture := range fixtures {
		lines := strings.Split(fixture.proof, "\n")
		for at := 0; at <= len(lines); at++ {
			for gap, separator := range []string{"", "\n", " \t\r\n", "\n\n", "c comment\n", "\nc comment\n", "c comment\n\n"} {
				for end, ending := range []string{"", "\n", "\r\n"} {
					var text strings.Builder
					for i := 0; i <= len(lines); i++ {
						if i == at {
							text.WriteString(separator)
						}
						if i < len(lines) {
							text.WriteString(lines[i])
							if i+1 < len(lines) || at == len(lines) {
								text.WriteByte('\n')
							}
						}
					}
					text.WriteString(ending)
					c := boundaryCase{
						Name: fmt.Sprintf("%s/at-%d/gap-%d/end-%d", fixture.name, at, gap, end),
						CNF:  formula, Proof: text.String(), Expected: fixture.accepted,
					}
					t.Run(c.Name, func(t *testing.T) {
						got, err := production.Check(c.CNF, c.Proof)
						reference, referenceErr := Check(c.CNF, c.Proof)
						if (err == nil) != c.Expected || (referenceErr == nil && reference.Accepted) != c.Expected {
							t.Fatalf("expected %t; production=%+v (%v); reference=%+v (%v)",
								c.Expected, got, err, reference, referenceErr)
						}
						if c.Expected && (got.Additions != fixture.additions || got.Deletions != fixture.deletions ||
							reference.Additions != fixture.additions || reference.Deletions != fixture.deletions) {
							t.Fatalf("commands lost: production=%+v reference=%+v", got, reference)
						}
					})
					corpus = append(corpus, c)
					if c.Expected {
						accepted++
					}
				}
			}
		}
	}
	t.Logf("production/reference line boundaries: %d cases (%d accepted, %d rejected)",
		len(corpus), accepted, len(corpus)-accepted)
	if path := os.Getenv("OAK_PRODUCTION_LRAT_CORPUS_OUT"); path != "" {
		data, err := json.Marshal(corpus)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, data, 0600); err != nil {
			t.Fatal(err)
		}
	}
}
