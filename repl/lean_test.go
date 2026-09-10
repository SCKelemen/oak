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
	"step: (v: u32): u32 = v + 1",
	"mystery: (v: u32): u32 = { w: u32 = v\n  w * 2 }",
	"fill: (n: u32): u32 = { buf: [8]u8 = [0, 0, 0, 0, 0, 0, 0, 0]\n  i: u32 = 0\n  while i != n { j: u32 = step(i)\n    buf[i % 8] = u8_trunc_u32(j)\n    i = i + u32(buf[0]) + mystery(1) }\n  i }",
	"ping: (n: u32): u32 = n == 0 ? 0 | pong(n - 1)\n\npong: (n: u32): u32 = n == 0 ? 1 | ping(n - 1)",
	"shared: [16]u8",
	"unsafe {\n  a: [*]u8 = span(&shared)\n  b: [*]u8 = span(&shared)\n}",
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
		"{ var := 0, ty := .b, value := (.bin .lt (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.var 1) (.lit 1)))) (.lit 10)) }",
		"(.cond (.bin .gt (.var 0) (.lit 5)) (.wrap (.u 32) (.bin .sub (.var 0) (.lit 2))) (.wrap (.u 32) (.bin .sub (.var 0) (.lit 1))))",
		// fill: the local j is substituted with step inlined, the store is
		// a write, the read sees it, and mystery (a block body) is
		// uninterpreted.
		"-- arrays: 0 ↦ `buf`",
		"-- uninterpreted functions (constrain F with hypotheses): 0 ↦ `mystery`",
		"writes := [{ arr := 0, ty := (.u 8), index := (.wrap (.u 32) (.bin .rem (.var 0) (.lit 8))), value := (.wrap (.u 8) (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.var 0) (.lit 1))))) }]",
		"(.cond (.bin .eq (.lit 0) (.wrap (.u 32) (.bin .rem (.var 0) (.lit 8)))) (.wrap (.u 8) (.wrap (.u 8) (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.var 0) (.lit 1)))))) (.index 0 (.lit 0)))",
		"(.call 0 [(.lit 1)])",
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
		"P: type = struct { v: u32 }",
		"spin: (n: u32): u32 = { p: P = P { v: 0 }\n  while p.v != n { p.v = p.v + 1 }\n  p.v }",
	} {
		if _, err := session.Submit(input); err != nil {
			t.Fatal(err)
		}
	}
	text, err := session.LeanObligations()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(text, "Not translatable into Oak.Loops:") {
		t.Fatalf("a field-mutating loop must be reported:\n%s", text)
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
