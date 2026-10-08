package repl

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Definitions state the complete claim but cannot be used as evidence for it.
// The marker is the interface to :lean check; omitting it would hide open work.
func TestLeanOpenObligationsHaveNoProofAuthority(t *testing.T) {
	cases := []struct {
		name   string
		inputs []string
		claims []string
	}{
		{"session", exampleSession, []string{"loop_loop_1_terminates", "loop_countdown_2_terminates", "loop_fill_3_terminates", "loop_walk_4_terminates", "loop_drive_5_terminates"}},
		{"symbolic_regions", []string{"f: (n: u32): u8 = { buf: [16]u8\n parent: [*]u8 = span(&buf)\n unsafe { left: [*]u8 = parent[0:8]\n mid: [*]u8 = parent[4:n] }\n 0 }"}, []string{"unsafe_1_disjoint"}},
		{"operator_laws", []string{"Hist: type = struct { n: u32 }", "hist_zero: (): Hist = Hist { n: u32(0) }", "operator(+) merge: (a: Hist, b: Hist): Hist laws { associative, commutative, identity(hist_zero()), idempotent } = Hist { n: a.n + b.n }"}, []string{"law_merge_associative", "law_merge_commutative", "law_merge_identity_left", "law_merge_identity_right", "law_merge_idempotent"}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			s := NewSession(t.TempDir())
			for _, input := range tc.inputs {
				if _, err := s.Submit(input); err != nil {
					t.Fatal(err)
				}
			}
			text, err := s.LeanObligations()
			if err != nil {
				t.Fatal(err)
			}
			if strings.Contains(text, "\n  sorry") || strings.Contains(text, "\naxiom ") {
				t.Fatalf("generated proof admission:\n%s", text)
			}
			if strings.Count(text, "-- OAK-OBLIGATION ") != len(tc.claims) {
				t.Fatalf("open obligations disappeared:\n%s", text)
			}
			for _, claim := range tc.claims {
				want := "-- OAK-OBLIGATION " + claim + ": open\ndef " + claim + " : Prop :="
				if !strings.Contains(text, want) {
					t.Fatalf("missing named open proposition %s:\n%s", claim, text)
				}
			}
			if lake, err := exec.LookPath("lake"); err == nil {
				dir, err := findLeanDir(".")
				if err != nil {
					t.Fatal(err)
				}
				file := filepath.Join(t.TempDir(), "OpenClaims.lean")
				if err := os.WriteFile(file, []byte(text), 0600); err != nil {
					t.Fatal(err)
				}
				cmd := exec.Command(lake, "env", "lean", file)
				cmd.Dir = dir
				if output, err := cmd.CombinedOutput(); err != nil {
					t.Fatalf("named propositions must elaborate: %v\n%s", err, output)
				}
			}
		})
	}
}
