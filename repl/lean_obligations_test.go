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
		{"scalar_laws", []string{"join: (a: u32, b: u32): u32 laws { associative, commutative } = a | b"}, []string{"law_join_associative", "law_join_commutative"}},
		{"float_law", []string{"join: (a: f64, b: f64): f64 laws { commutative } = a + b"}, []string{"law_join_commutative"}},
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

// Unsupported claims remain visible without inventing a proposition or proof.
func TestLeanUnsupportedObligationsStayVisible(t *testing.T) {
	for _, tc := range []struct {
		name, source string
		claims       []string
	}{
		{"identity_literal", "join: (a: u32, b: u32): u32 laws { identity(0) } = a + b", []string{"law_join_identity_left", "law_join_identity_right"}},
		{"unextractable_law", "join: (a: f32, b: f32): f32 laws { commutative } = min(a, b)", []string{"law_join_commutative"}},
		{"nested_loop", "spin: (n: u32): u32 = { i: u32 = 0\n while i != n { j: u32 = 0\n while j != i { j = j + 1 }\n i = i + 1 }\n i }", []string{"loop_spin_1_terminates"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			s := NewSession(t.TempDir())
			if _, err := s.Submit(tc.source); err != nil {
				t.Fatal(err)
			}
			text, err := s.LeanObligations()
			if err != nil {
				t.Fatal(err)
			}
			for _, name := range tc.claims {
				if !strings.Contains(text, "-- OAK-OBLIGATION "+name+": unsupported") {
					t.Fatalf("unsupported claim vanished: %s\n%s", name, text)
				}
				if strings.Contains(text, "\ndef "+name+" : Prop") || strings.Contains(text, "\ntheorem "+name) {
					t.Fatalf("unsupported claim acquired a fabricated statement/proof: %s", name)
				}
			}
		})
	}
}
