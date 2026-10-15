package prove

import (
	"crypto/sha256"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

const synthesisCounters = `
Counters: protocol = {
  data { x: u8, y: u8 }
  init { x: u8(0), y: u8(0) }
  initial Running
  tick: Running -> Running then {
    data.x = data.x + u8(1)
    data.y = data.y + u8(1)
  }
}
ordered: theorem (s: CountersState, d: CountersData) { d.x <= d.y }
main: (): i32 = 0
`

func synthesize(t *testing.T, source string, options SynthesisOptions) SynthesisResult {
	t.Helper()
	if options.Cases == 0 {
		options.Cases = 1 // Force symbolic checking of the full typed domains.
	}
	result, err := SynthesizeInvariant(compiler.SourceText{Path: "synthesis.oak", Text: source}, "ordered", options)
	if err != nil {
		t.Fatal(err)
	}
	return result
}

func TestSynthesisStrengthensNonInductiveProperty(t *testing.T) {
	// Without an auxiliary equality the universal step must fail, even though
	// full exploration could establish this small model's reachable invariant.
	without := synthesize(t, synthesisCounters, SynthesisOptions{Candidates: []string{}})
	if without.Status != Open || !strings.Contains(without.Detail, "oak_synth_step") {
		t.Fatalf("unstrengthened result: %+v", without)
	}
	got := synthesize(t, synthesisCounters, SynthesisOptions{})
	readable := strings.NewReplacer("(", "", ")", "").Replace(got.Invariant)
	if got.Status != Decided || !strings.Contains(readable, "d.x == d.y") || !strings.HasPrefix(got.Invariant, "ordered(s, d)") {
		t.Fatalf("strengthened result: %+v", got)
	}
	if got.Rounds < 2 || len(got.Rejected) == 0 || len(got.Checks) != 3 {
		t.Fatalf("missing pruning or final evidence: %+v", got)
	}
	for _, check := range got.Checks {
		if check.Status != Decided {
			t.Fatalf("unchecked final obligation: %+v", check)
		}
	}
	if got.SourceSHA256 != fmt.Sprintf("%x", sha256.Sum256([]byte(synthesisCounters))) {
		t.Fatal("report does not bind the original source bytes")
	}
}

func TestSynthesisRechecksAfterWeakening(t *testing.T) {
	source := `
Flags: protocol = {
  data { x: Bool, y: Bool }
  init { x: false, y: false }
  initial Running
  tick: Running -> Running then { data.y = data.x; data.x = true }
}
ordered: theorem (s: FlagsState, d: FlagsData) { true }
main: (): i32 = 0
`
	got := synthesize(t, source, SynthesisOptions{Candidates: []string{"!d.x", "!d.y"}})
	if got.Status != Decided || len(got.Retained) != 0 || got.Rounds != 3 || len(got.Rejected) != 2 {
		t.Fatalf("stale candidate retained: %+v", got)
	}
	if got.Rejected[0].Round != 1 || got.Rejected[1].Round != 2 {
		t.Fatalf("expected iterative weakening: %+v", got.Rejected)
	}
}

func TestSynthesisCannotProveBrokenProperty(t *testing.T) {
	broken := strings.Replace(synthesisCounters, "data.y = data.y + u8(1)", "data.y = data.y", 1)
	for _, candidates := range [][]string{nil, {"false"}, {"d.x == d.y"}, {"d.x != d.y"}} {
		got := synthesize(t, broken, SynthesisOptions{Candidates: candidates})
		if got.Status != Open {
			t.Fatalf("false property accepted with %v: %+v", candidates, got)
		}
	}
	initiallyFalse := strings.Replace(synthesisCounters, "d.x <= d.y", "d.x < d.y", 1)
	got := synthesize(t, initiallyFalse, SynthesisOptions{Candidates: []string{"false"}})
	if got.Status != Open || !strings.Contains(got.Detail, "oak_synth_base") {
		t.Fatalf("vacuous invariant accepted: %+v", got)
	}
}

func TestSynthesisSearchBudgetIsNotProof(t *testing.T) {
	got := synthesize(t, synthesisCounters, SynthesisOptions{Candidates: []string{"false", "d.x == d.y"}, MaxRounds: 1})
	if got.Status != Open || !strings.Contains(got.Detail, "round budget") || got.Invariant != "" {
		t.Fatalf("budget exhaustion accepted: %+v", got)
	}
}

func TestSynthesisCandidateInputIsNotCode(t *testing.T) {
	for _, candidate := range []string{
		"ordered(s, d)", "assume(false)", "oak_synth_invariant(s, d)",
		"true\nreplacement: theorem () = true", "{ d.x = u8(0); true }",
		"{ while true { }; true }", "other.x == u8(0)", "",
	} {
		t.Run(candidate, func(t *testing.T) {
			_, err := SynthesizeInvariant(compiler.SourceText{Path: "synthesis.oak", Text: synthesisCounters}, "ordered", SynthesisOptions{Candidates: []string{candidate}})
			if err == nil {
				t.Fatalf("accepted executable or injected candidate %q", candidate)
			}
		})
	}
	got := synthesize(t, synthesisCounters, SynthesisOptions{Candidates: []string{"d.x / u8(0) == u8(0)", "d.x == d.y"}})
	if got.Status != Decided || len(got.Rejected) != 1 || got.Rejected[0].Check.Status == Decided {
		t.Fatalf("trapping predicate did not get rejected: %+v", got)
	}
}

func TestSynthesisRequiresDeterministicProjection(t *testing.T) {
	for _, secondGuard := range []string{"when data.x < u8(2)", ""} {
		source := `
Choice: protocol = {
  data { x: u8 }
  init { x: u8(0) }
  initial Running
  tick: Running -> Running when data.x < u8(1)
  tick: Running -> Running ` + secondGuard + `
}
ordered: theorem (s: ChoiceState, d: ChoiceData) { true }
main: (): i32 = 0
`
		got := synthesize(t, source, SynthesisOptions{})
		if got.Status != Open || !strings.Contains(got.Detail, "determinism not established") {
			t.Fatalf("ambiguous transition accepted: %+v", got)
		}
	}
	source := `
Choice: protocol = {
  data { x: u8 }
  init { x: u8(0) }
  initial Running
  tick: Running -> Running when data.x < u8(1)
  tick: Running -> Running when data.x >= u8(1)
}
ordered: theorem (s: ChoiceState, d: ChoiceData) { true }
main: (): i32 = 0
`
	got := synthesize(t, source, SynthesisOptions{Candidates: []string{}})
	if got.Status != Decided || len(got.Checks) != 4 || !strings.Contains(got.Checks[0].Name, "__exclusive__") {
		t.Fatalf("missing exclusivity evidence: %+v", got)
	}
}

func TestSynthesisStateOnlyAndSourceIdentity(t *testing.T) {
	source := `
Switch: protocol = {
  initial Off
  on: Off -> On
  off: On -> Off
}
ordered: theorem (state: SwitchState) { state == .Off || state == .On }
main: (): i32 = 0
`
	// Enumerate the complete small state/action domains. The bit-level rung
	// does not support every enum expression. Step names deliberately overlap
	// state names: the evaluator must use the checker's enum resolution.
	got := synthesize(t, source, SynthesisOptions{Cases: 16})
	if got.Status != Decided {
		t.Fatalf("state-only protocol: %+v", got)
	}
	broken := strings.Replace(source, "state == .Off || state == .On", "state == .Off", 1)
	if result := synthesize(t, broken, SynthesisOptions{Cases: 16}); result.Status != Open {
		t.Fatalf("state-changing protocol accepted a false property: %+v", result)
	}
	for _, bad := range []string{
		"import(std)\n" + source,
		source + "\noak_synth_base: theorem () = true\n",
	} {
		_, err := SynthesizeInvariant(compiler.SourceText{Path: "synthesis.oak", Text: bad}, "ordered", SynthesisOptions{})
		if err == nil {
			t.Fatal("accepted unbound imports or generated-name collision")
		}
	}
}
