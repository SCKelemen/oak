package repl

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// sessionObligationsFile is the checked-in rendering of exampleSession's
// obligations; the Lean CI job elaborates it (and Oak/SessionObligationsProved
// discharges its statements), so the REPL's emitter is checked by Lean.
const sessionObligationsFile = "../spec/lean/Oak/SessionObligations.lean"

// exampleSession records one obligation of each stated kind: an unbounded
// flag-controlled loop, a conditional countdown, a mutual tail cycle, and an
// admitted span overlap whose regions are known.
var exampleSession = []string{
	"loop: (): u32 = { i: u32 = 0\n  running: Bool = true\n  while running { i = i + 1\n    running = i < 10 }\n  i }",
	"countdown: (n: u32): u32 = { k: u32 = n\n  while k > 0 { k > 5 ? { k = k - 2 } | { k = k - 1 } }\n  k }",
	"ping: (n: u32): u32 = n == 0 ? 0 | pong(n - 1)\n\npong: (n: u32): u32 = n == 0 ? 1 | ping(n - 1)",
	"buf: [16]u8",
	"unsafe {\n  a: [*]u8 = span(&buf)\n  b: [*]u8 = span(&buf)\n}",
}

func TestLeanObligationsMatchCheckedInFile(t *testing.T) {
	session := NewSession(t.TempDir())
	for _, input := range exampleSession {
		if _, err := session.Submit(input); err != nil {
			t.Fatalf("%s: %v", input, err)
		}
	}
	text, err := session.LeanObligations()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"def loop_loop_1 : Oak.Loops.Loop",
		"{ var := 0, ty := .b, value := (.bin .lt (.wrap (.u 32) (.bin .add (.var 1) (.lit 1))) (.lit 10)) }",
		"(.cond (.bin .gt (.var 0) (.lit 5)) (.bin .sub (.var 0) (.lit 2)) (.bin .sub (.var 0) (.lit 1)))",
		"Oak.Discipline.Ranked [] [(0, 1), (1, 0)] rank :=\n  ⟨fun _ => 0, by simp [Oak.Discipline.Ranked]⟩",
		"theorem unsafe_1_overlaps : ¬ Oak.Regions.Disjoint ⟨0, 16⟩ ⟨0, 16⟩ := by decide",
	} {
		if !strings.Contains(text, want) {
			t.Fatalf("emitted Lean lacks %q:\n%s", want, text)
		}
	}
	path := filepath.Clean(sessionObligationsFile)
	if os.Getenv("OAK_UPDATE") != "" {
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	checked, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if string(checked) != text {
		t.Fatalf("%s is out of date; run OAK_UPDATE=1 go test ./repl -run TestLeanObligationsMatchCheckedInFile", path)
	}
}

// Loops outside the fragment are reported, never approximated.
func TestLeanObligationsReportUntranslatableLoops(t *testing.T) {
	session := NewSession(t.TempDir())
	for _, input := range []string{
		"step: (v: u32): u32 = v + 1",
		"spin: (n: u32): u32 = { i: u32 = 0\n  while i != n { i = step(i) }\n  i }",
	} {
		if _, err := session.Submit(input); err != nil {
			t.Fatal(err)
		}
	}
	text, err := session.LeanObligations()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(text, "Not translatable into Oak.Loops: the loop calls a function") {
		t.Fatalf("call inside the loop must be reported:\n%s", text)
	}
	if strings.Contains(text, "def loop_spin") {
		t.Fatal("an untranslatable loop must not be approximated")
	}
	empty := NewSession(t.TempDir())
	if _, err := empty.Submit("twice: (v: i32): i32 = v * 2"); err != nil {
		t.Fatal(err)
	}
	text, err = empty.LeanObligations()
	if err != nil || !strings.Contains(text, "No recorded assumptions") {
		t.Fatalf("empty obligations = %v\n%s", err, text)
	}
}
