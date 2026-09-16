package main

import (
	"testing"

	"github.com/SCKelemen/oak/prove"
)

// The certificate checker written in Oak (prove/solver/lrat.oak) and the Go
// acceptance kernel (internal/lrat/lrat.go, exposed through prove) agree on
// every certificate the shared word encoder admits
// (docs/spec/125-verification.md §3, the certificate rung).
func TestOakLRATAgrees(t *testing.T) {
	formula := "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
	cases := map[string]string{
		"accepted":         "5 2 0 1 2 0\n5 d 1 2 0\n6 0 5 3 4 0\n",
		"no conflict":      "5 2 0 1 0\n6 0 5 3 4 0\n",
		"hint not unit":    "5 0 1 0\n",
		"dead hint":        "5 2 0 1 2 0\n5 d 1 2 0\n6 0 5 1 2 0\n",
		"id order":         "4 2 0 1 2 0\n",
		"no empty clause":  "5 2 0 1 2 0\n",
		"satisfied hint":   "5 -2 0 1 2 0\n",
		"deletion of dead": "5 d 1 0\n5 d 1 0\n6 2 0 2 3 0\n",
	}
	for name, certificate := range cases {
		_, goErr := prove.CheckLRAT(formula, certificate)
		oak, err := runOakLRAT(formula, certificate)
		if err != nil {
			if goErr == nil {
				t.Fatalf("%s: Go accepted but Oak preparation failed: %v", name, err)
			}
			continue
		}
		if (goErr == nil) != (oak.Status == 0) {
			t.Errorf("%s: Go %v, Oak status %d", name, goErr, oak.Status)
		}
		if goErr == nil && (oak.Additions != 2 || oak.Deletions != 2) {
			t.Errorf("%s: Oak counted %d additions and %d deletions", name, oak.Additions, oak.Deletions)
		}
	}
}

func TestOakLRATAllocationBounds(t *testing.T) {
	normal := []uint32{prove.LRATMagic, 2, 0, 0, 0, 0, 0, 0}
	if err := checkOakLRATAllocationBounds(normal); err != nil {
		t.Fatal(err)
	}
	disproportionate := append([]uint32(nil), normal...)
	disproportionate[1] = 1 << 30
	if err := checkOakLRATAllocationBounds(disproportionate); err == nil {
		t.Fatal("accepted a disproportionate Oak-checker allocation header")
	}
}
