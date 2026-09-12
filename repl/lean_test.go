package repl

import (
	"os"
	"os/exec"
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
	"P: type = struct { v: u32, on: Bool }\n\nQ: type = struct { p: P, k: u8 }",
	"bump: (p: P): u32 = p.v + 1",
	"walk: (n: u32, cs: [2]P): u32 = { p: P = P { v: 0, on: true }\n  q: Q = Q { p: p, k: 1 }\n  while p.on { r: P = p\n    p.v = bump(r)\n    q.p.v = p.v\n    cs[0].v = cs[0].v + q.p.v\n    p.on = cs[0].v < n }\n  p.v }",
	"Step: type = Idle | Count: u32",
	"drive: (n: u32): u32 = { s: Step = Step.Count(0)\n  total: u32 = 0\n  while total < n { s = s ? .Idle => Step.Count(1) | .Count(k) => k < 3 ? Step.Count(k + 1) | Step.Idle\n    total = total + (s ? .Idle => 1 | .Count(k) => k) }\n  total }",
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
	path := filepath.Clean(sessionObligationsFile)
	if os.Getenv("OAK_UPDATE") != "" {
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
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
		// walk: records are flattened into per-field variables and memories;
		// the loop-local record r copies p, bump inlines over r's leaves.
		"-- variables: 0 ↦ `p.on`, 1 ↦ `p.v`, 2 ↦ `q.p.v`, 3 ↦ `n`",
		"-- arrays: 0 ↦ `cs.v`",
		"{ var := 1, ty := (.u 32), value := (.wrap (.u 32) (.bin .add (.wrap (.u 32) (.var 1)) (.lit 1))) }",
		"{ var := 2, ty := (.u 32), value := (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.wrap (.u 32) (.var 1)) (.lit 1)))) }",
		"writes := [{ arr := 0, ty := (.u 32), index := (.lit 0), value := (.wrap (.u 32) (.bin .add (.index 0 (.lit 0)) (.wrap (.u 32) (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.wrap (.u 32) (.var 1)) (.lit 1))))))) }]",
		// drive: a sum type is a tag leaf plus payload leaves; matches are
		// nested conditionals on the tag with the last arm as default.
		"-- variables: 0 ↦ `total`, 1 ↦ `n`, 2 ↦ `s.tag`, 3 ↦ `s.Count`",
		"{ var := 2, ty := (.u 8), value := (.cond (.bin .eq (.var 2) (.lit 0)) (.lit 1) (.cond (.bin .lt (.var 3) (.lit 3)) (.lit 1) (.lit 0))) }",
		"Oak.Discipline.Ranked [] [(0, 1), (1, 0)] rank :=\n  ⟨fun _ => 0, by simp [Oak.Discipline.Ranked]⟩",
		"theorem unsafe_1_overlaps : ¬ Oak.Regions.Disjoint ⟨0, 16⟩ ⟨0, 16⟩ := by decide",
	} {
		if !strings.Contains(text, want) {
			t.Fatalf("emitted Lean lacks %q:\n%s", want, text)
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
		"spin: (n: u32): u32 = { i: u32 = 0\n  while i != n { j: u32 = 0\n    while j != i { j = j + 1 }\n    i = i + 1 }\n  i }",
	} {
		if _, err := session.Submit(input); err != nil {
			t.Fatal(err)
		}
	}
	text, err := session.LeanObligations()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(text, "Not translatable into Oak.Loops: the body contains a nested loop") {
		t.Fatalf("a nested loop must be reported:\n%s", text)
	}
	// The inner loop is itself an obligation and is translatable; only it
	// gets a definition — the outer loop is reported, never approximated.
	if strings.Count(text, "def loop_spin") != 1 {
		t.Fatalf("exactly the inner loop must be translated:\n%s", text)
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

// :lean check elaborates the emitted file with the repository's toolchain
// and attributes Lean's verdicts to theorems. Skipped without lake.
func TestLeanCheckReportsVerdicts(t *testing.T) {
	if _, err := exec.LookPath("lake"); err != nil {
		t.Skip("lake not on PATH")
	}
	session := NewSession(".")
	for _, input := range exampleSession {
		if _, err := session.Submit(input); err != nil {
			t.Fatal(err)
		}
	}
	text, err := session.LeanObligations()
	if err != nil {
		t.Fatal(err)
	}
	// A deliberately false statement joins the file so the error path is
	// exercised.
	text = strings.Replace(text, "end Oak.Session", "theorem broken_disjoint : Oak.Regions.Disjoint ⟨0, 4⟩ ⟨2, 6⟩ := by decide\n\nend Oak.Session", 1)
	report, err := session.LeanCheck(text, filepath.Join(t.TempDir(), "check.lean"))
	if err != nil {
		t.Fatal(err)
	}
	verdicts := map[string]Verdict{}
	for _, theorem := range report.Theorems {
		verdicts[theorem.Name] = theorem.Verdict
	}
	for name, want := range map[string]Verdict{
		"loop_loop_1_terminates": Open,
		"cycle_1_ranked":         Proved,
		"unsafe_1_overlaps":      Proved,
		"broken_disjoint":        Failed,
	} {
		if verdicts[name] != want {
			t.Fatalf("%s = %s, want %s\n%s", name, verdicts[name], want, report)
		}
	}
}

// classify attributes messages by line range without running Lean.
func TestClassifyAttributesMessages(t *testing.T) {
	text := "theorem a : True := trivial\n\n/-- doc -/\ntheorem b : True := by\n  sorry\n\ntheorem c : False := by\n  decide\n"
	output := "{\"severity\":\"warning\",\"pos\":{\"line\":4},\"data\":\"declaration uses sorry\"}\n{\"severity\":\"error\",\"pos\":{\"line\":8},\"data\":\"failed to synthesize Decidable False\"}\n"
	report := classify(text, []byte(output))
	if len(report.Theorems) != 3 || report.Theorems[0].Verdict != Proved || report.Theorems[1].Verdict != Open || report.Theorems[2].Verdict != Failed {
		t.Fatalf("report = %+v", report.Theorems)
	}
}

// Declared operator laws (docs/spec/10-syntax.md section 14a) are stated by
// :lean as theorems over the extracted operator function.
func TestLeanObligationsStateOperatorLaws(t *testing.T) {
	session := NewSession(t.TempDir())
	for _, input := range []string{
		"Vec: type = struct { x: u32, y: u32 }",
		"operator(+) add: (a: Vec, b: Vec): Vec laws { associative, commutative } = Vec { x: a.x + b.x, y: a.y + b.y }",
	} {
		if _, err := session.Submit(input); err != nil {
			t.Fatal(err)
		}
	}
	text, err := session.LeanObligations()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"namespace Defs",
		"def add (a : Vec) (b : Vec) (fuel : Nat) : Option (Vec)",
		"theorem law_add_associative (a b c : Defs.Vec) (fuel : Nat) :\n    (Defs.add a b fuel >>= fun ab => Defs.add ab c fuel) = (Defs.add b c fuel >>= fun bc => Defs.add a bc fuel) := by\n  sorry",
		"theorem law_add_commutative (a b : Defs.Vec) (fuel : Nat) :\n    Defs.add a b fuel = Defs.add b a fuel := by\n  sorry",
	} {
		if !strings.Contains(text, want) {
			t.Fatalf("missing %q in:\n%s", want, text)
		}
	}
	if strings.Contains(text, "No recorded assumptions") {
		t.Fatalf("a declared law is an open claim:\n%s", text)
	}
}

// The vocabulary beyond associative and commutative (docs/spec/10-syntax.md
// section 14a): identity(e) states a left and a right theorem with the
// element as the extracted nullary function, idempotent one theorem.
func TestLeanStatesIdentityAndIdempotent(t *testing.T) {
	session := NewSession(t.TempDir())
	for _, input := range []string{
		"Hist: type = struct { n: u32 }",
		"hist_zero: (): Hist = Hist { n: u32(0) }",
		"operator(+) merge: (a: Hist, b: Hist): Hist laws { identity(hist_zero()), idempotent } = Hist { n: a.n + b.n }",
	} {
		if _, err := session.Submit(input); err != nil {
			t.Fatal(err)
		}
	}
	text, err := session.LeanObligations()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"declares `identity(hist_zero())`",
		"theorem law_merge_identity_left (a : Defs.Hist) (fuel : Nat) :\n    (Defs.hist_zero fuel >>= fun e => Defs.merge e a fuel) = some a := by\n  sorry",
		"theorem law_merge_identity_right (a : Defs.Hist) (fuel : Nat) :\n    (Defs.hist_zero fuel >>= fun e => Defs.merge a e fuel) = some a := by\n  sorry",
		"theorem law_merge_idempotent (a : Defs.Hist) (fuel : Nat) :\n    Defs.merge a a fuel = some a := by\n  sorry",
	} {
		if !strings.Contains(text, want) {
			t.Fatalf("missing %q in:\n%s", want, text)
		}
	}
}
