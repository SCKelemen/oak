package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// The verified profile closes the proven verdicts over the callees their
// summaries took (asm.Verdict.Callees): a proven body resting on a body
// that is trusted, or on one resting on such a body, is refused and named
// with the callee; a cycle of proven bodies stands; a callee the native
// backend never lowered is not accepted.
func TestVerifiedProfileClosesOverCallees(t *testing.T) {
	verdicts := map[string]asm.Verdict{
		"leaf":     {Kind: asm.VerdictProven},
		"mid":      {Kind: asm.VerdictProven, Callees: []string{"leaf"}},
		"top":      {Kind: asm.VerdictProven, Callees: []string{"mid"}},
		"shaky":    {Kind: asm.VerdictTrusted, Message: "asm unit shaky: not verified (the Oak body contains a non-constant shift count) — trusted per docs/spec/94-assembler.md §5"},
		"on_shaky": {Kind: asm.VerdictProven, Callees: []string{"shaky"}},
		"on_that":  {Kind: asm.VerdictProven, Callees: []string{"leaf", "on_shaky"}},
		"ping":     {Kind: asm.VerdictProven, Callees: []string{"pong"}},
		"pong":     {Kind: asm.VerdictProven, Callees: []string{"ping"}},
		"on_c":     {Kind: asm.VerdictProven, Callees: []string{"in_c"}},
	}
	resting := provenRestingOnUnproven(verdicts)
	for _, name := range []string{"leaf", "mid", "top", "ping", "pong"} {
		if callee, dropped := resting[name]; dropped {
			t.Errorf("%s must stay accepted; dropped via %s", name, callee)
		}
	}
	for name, want := range map[string]string{"on_shaky": "shaky", "on_that": "on_shaky", "on_c": "in_c"} {
		if got := resting[name]; got != want {
			t.Errorf("%s: rests on %q, want %q", name, got, want)
		}
	}
	comp := New().WithVerifiedProfile()
	err := comp.verifiedProfile(&LoweredProgram{Model: &SemanticModel{NativeVerdicts: verdicts, NativeFallbacks: map[string]string{"in_c": "a float parameter"}}})
	if err == nil {
		t.Fatal("the profile must refuse")
	}
	for _, want := range []string{
		"verified profile: 5 bodies are not proven",
		"proven, resting on a callee that is not proven (3): on_c (via in_c), on_shaky (via shaky), on_that (via on_shaky)",
		"trusted: the Oak body contains a non-constant shift count (1): shaky",
		"left to the C backend: a float parameter (1): in_c",
	} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("refusal lacks %q:\n%s", want, err)
		}
	}
}
