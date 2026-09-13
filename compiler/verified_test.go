package compiler

import (
	"strings"
	"testing"
)

// The verified gate's closure: a proven function rests on the callees its
// verdict took at their Oak bodies, so it is accepted only when they are,
// through any depth, and a cycle of proven functions stands.
func TestAcceptedClosure(t *testing.T) {
	outcomes := map[string]NativeOutcome{
		"leaf":     {Name: "leaf", Kind: OutcomeProven},
		"mid":      {Name: "mid", Kind: OutcomeProven, Callees: []string{"leaf"}},
		"top":      {Name: "top", Kind: OutcomeProven, Callees: []string{"mid"}},
		"shaky":    {Name: "shaky", Kind: OutcomeWitnessed, Reason: "the bit-level decision exceeded its node budget"},
		"on_shaky": {Name: "on_shaky", Kind: OutcomeProven, Callees: []string{"shaky"}},
		"on_that":  {Name: "on_that", Kind: OutcomeProven, Callees: []string{"on_shaky", "leaf"}},
		"ping":     {Name: "ping", Kind: OutcomeProven, Callees: []string{"pong"}},
		"pong":     {Name: "pong", Kind: OutcomeProven, Callees: []string{"ping"}},
		"unknown":  {Name: "unknown", Kind: OutcomeProven, Callees: []string{"ghost"}},
	}
	var names []string
	for name := range outcomes {
		names = append(names, name)
	}
	accepted := map[string]bool{}
	for name, outcome := range outcomes {
		if outcome.Kind == OutcomeProven {
			accepted[name] = true
		}
	}
	why := acceptedClosure(names, outcomes, accepted)
	for _, name := range []string{"leaf", "mid", "top", "ping", "pong"} {
		if !accepted[name] {
			t.Errorf("%s must stay accepted: %s", name, why[name])
		}
	}
	for name, want := range map[string]string{
		"on_shaky": "rests on the call to shaky, which is not accepted (witnessed)",
		"on_that":  "rests on the call to on_shaky, which is not accepted (proven)",
		"unknown":  "rests on the call to ghost, which is not accepted (not judged)",
	} {
		if accepted[name] {
			t.Errorf("%s must be dropped", name)
		}
		if !strings.Contains(why[name], want) {
			t.Errorf("%s: want %q, got %q", name, want, why[name])
		}
	}
	if accepted["shaky"] {
		t.Error("a witnessed function is never accepted")
	}
}

func TestAbstractReason(t *testing.T) {
	for reason, want := range map[string]string{
		"a call to ratio whose body contains operator /":                   "a call to F whose body contains operator /",
		"a call to text_take: parameter s is not a fixed-width integer":    "a call to F: parameter P is not a fixed-width integer",
		"a record stride of 409600 bytes":                                  "a record stride of N bytes",
		"a call to f returning ((Result.u32).TextError)":                   "a call to F returning ((Result.u32).TextError)",
		"the span local classes: the callee-saved registers are exhausted": "the span local P: the callee-saved registers are exhausted",
	} {
		if got := abstractReason(reason); got != want {
			t.Errorf("abstractReason(%q) = %q, want %q", reason, got, want)
		}
	}
}
