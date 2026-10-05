package opt

import (
	"fmt"
	"reflect"
	"strings"
	"testing"
)

type validationFallbackDriver struct {
	*fakeDriver
	requests int
	proposal func(*Candidate) *Candidate
}

func (d *validationFallbackDriver) ValidationFallback(c *Candidate, _ Verdict) *Candidate {
	d.requests++
	return d.proposal(c)
}

func TestValidationFallbackBudgetAndAdmission(t *testing.T) {
	for _, tc := range []struct {
		name         string
		first, next  Outcome
		budget       int
		refused      bool
		unlowered    bool
		duplicate    bool
		wantRequests int
		wantBody     string
		wantChecks   []string
	}{
		{"trusted recovery", Trusted, Proven, 3, false, false, false, 1, "recovered", []string{"a", "recovered"}},
		{"witnessed recovery", Witnessed, Proven, 3, false, false, false, 1, "recovered", []string{"a", "recovered"}},
		{"proven needs none", Proven, Proven, 3, false, false, false, 0, "a", []string{"a"}},
		{"mismatch has none", Mismatch, Proven, 3, false, false, false, 0, "", []string{"a", ""}},
		{"refused has none", Refused, Proven, 3, false, false, false, 0, "", []string{"a", ""}},
		{"identity reservation", Trusted, Proven, 2, false, false, false, 0, "", []string{"a", ""}},
		{"identity only", Trusted, Proven, 1, false, false, false, 0, "", []string{""}},
		{"no recursive proposal", Trusted, Trusted, 4, false, false, false, 1, "", []string{"a", "recovered", ""}},
		{"wrong fallback", Trusted, Mismatch, 3, false, false, false, 1, "", []string{"a", "recovered", ""}},
		{"checker refusal", Trusted, Proven, 3, true, false, false, 1, "", []string{"a", ""}},
		{"lowering failure", Trusted, Proven, 3, false, true, false, 1, "", []string{"a", ""}},
		{"duplicate body", Trusted, Proven, 3, false, false, true, 1, "", []string{"a", ""}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			s := newSearch(&Report{}, &toggle{name: "a", phase: PhaseCanonical, fires: true})
			s.Validations = tc.budget
			d := &validationFallbackDriver{fakeDriver: &fakeDriver{
				metrics:  map[string]Metrics{"a": {Instructions: 5}, "recovered": {Instructions: 6}},
				verdicts: map[string]Outcome{"a": tc.first, "recovered": tc.next},
				findings: map[string][]string{}, unlowered: map[string]bool{},
			}}
			d.proposal = func(c *Candidate) *Candidate {
				key := "recovered"
				if tc.duplicate {
					key = "a"
				}
				return c.With("fallback", config{switches: []string{key}})
			}
			if tc.refused {
				d.findings["recovered"] = []string{"out-of-bounds store"}
			}
			d.unlowered["recovered"] = tc.unlowered
			sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
			if err != nil {
				t.Fatal(err)
			}
			if sel.Candidate.Body != tc.wantBody || sel.Verdict.Outcome != Proven {
				t.Fatalf("selected %q (%s), want %q proven", sel.Candidate.Body, sel.Verdict.Outcome, tc.wantBody)
			}
			if d.requests != tc.wantRequests || !reflect.DeepEqual(d.validated, tc.wantChecks) {
				t.Fatalf("requests=%d, validated=%v; want %d, %v", d.requests, d.validated, tc.wantRequests, tc.wantChecks)
			}
			if len(sel.Validations) > tc.budget {
				t.Fatalf("exceeded validation budget: %d > %d", len(sel.Validations), tc.budget)
			}
			if tc.wantBody == "recovered" && (!strings.Contains(s.Report.String(), "validation-fallback") || !reflect.DeepEqual(d.checked, []string{"", "a", "recovered"})) {
				t.Fatalf("recovery bypassed admission or report: checked=%v\n%s", d.checked, s.Report.String())
			}
		})
	}
}

type identityOnlyToggle struct{ toggle }

func (t *identityOnlyToggle) Apply(c *Candidate) *Candidate {
	if !c.IsIdentity() {
		return nil
	}
	return t.toggle.Apply(c)
}

func TestValidationFallbackRetainsCostOrder(t *testing.T) {
	s := newSearch(nil,
		&identityOnlyToggle{toggle{name: "a", phase: PhaseCanonical, fires: true}},
		&identityOnlyToggle{toggle{name: "b", phase: PhaseCanonical, fires: true}},
	)
	d := &validationFallbackDriver{fakeDriver: &fakeDriver{
		metrics:  map[string]Metrics{"a": {Instructions: 5}, "b": {Instructions: 7}, "recovered": {Instructions: 9}},
		verdicts: map[string]Outcome{"a": Trusted},
	}}
	d.proposal = func(c *Candidate) *Candidate { return c.With("fallback", config{switches: []string{"recovered"}}) }
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if sel.Candidate.Body != "b" || d.requests != 1 || !reflect.DeepEqual(d.validated, []string{"a", "b"}) {
		t.Fatalf("fallback displaced cheaper proven candidate: selected %v, requested %d, validated %v", sel.Candidate.Body, d.requests, d.validated)
	}
}

func TestValidationFallbackRetainsGatedRefusal(t *testing.T) {
	s := newSearch(nil, &gatedToggle{toggle{name: "a", phase: PhaseCanonical, fires: true}})
	d := &validationFallbackDriver{fakeDriver: &fakeDriver{
		metrics:  map[string]Metrics{"a": {Instructions: 5}, "recovered": {Instructions: 6}},
		verdicts: map[string]Outcome{"": Trusted, "a": Trusted, "recovered": Trusted},
	}}
	d.proposal = func(c *Candidate) *Candidate { return c.With("fallback", config{switches: []string{"recovered"}}) }
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if !sel.Candidate.IsIdentity() || sel.Verdict.Outcome != Trusted || len(sel.Validations) != 3 {
		t.Fatalf("unproved gated fallback admitted: %s (%s), validations %v", sel.Candidate.Name(), sel.Verdict.Outcome, d.validated)
	}
}

func TestValidationFallbackRejectsParentReuse(t *testing.T) {
	s := newSearch(nil, &toggle{name: "a", phase: PhaseCanonical, fires: true})
	d := &validationFallbackDriver{fakeDriver: &fakeDriver{
		metrics:  map[string]Metrics{"a": {Instructions: 5}},
		verdicts: map[string]Outcome{"a": Trusted},
	}}
	d.proposal = func(c *Candidate) *Candidate { return c }
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if !sel.Candidate.IsIdentity() || d.requests != 1 || !reflect.DeepEqual(d.lowered, []string{"", "a"}) || !reflect.DeepEqual(d.validated, []string{"a", ""}) {
		t.Fatalf("parent reuse mutated artifacts: selected %s, lowered %v, validated %v", sel.Candidate.Name(), d.lowered, d.validated)
	}
}

func TestValidationFallbackEqualOutcomesUseFinalRank(t *testing.T) {
	for _, outcome := range []Outcome{Trusted, Witnessed} {
		for _, identityCost := range []int{1, 100} {
			t.Run(outcome.String()+"/identity-cost-"+fmt.Sprint(identityCost), func(t *testing.T) {
				s := newSearch(nil, &toggle{name: "a", phase: PhaseCanonical, fires: true})
				d := &validationFallbackDriver{fakeDriver: &fakeDriver{
					metrics:  map[string]Metrics{"": {Instructions: identityCost}, "a": {Instructions: 5}, "recovered": {Instructions: 3}},
					verdicts: map[string]Outcome{"": outcome, "a": outcome, "recovered": outcome},
				}}
				d.proposal = func(c *Candidate) *Candidate { return c.With("fallback", config{switches: []string{"recovered"}}) }
				sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
				if err != nil {
					t.Fatal(err)
				}
				if sel.Candidate.Body != "recovered" || sel.Verdict.Outcome != outcome || !reflect.DeepEqual(d.validated, []string{"a", "recovered", ""}) {
					t.Fatalf("equal outcome chose validation chronology or moved identity first: selected %v (%s), validated %v", sel.Candidate.Body, sel.Verdict.Outcome, d.validated)
				}
			})
		}
	}
}

type identityOnlyGatedToggle struct{ identityOnlyToggle }

func (t *identityOnlyGatedToggle) NeedsVerdict() bool { return true }

func TestValidationFallbackGatedRecoveryCannotExceedBudget(t *testing.T) {
	s := newSearch(nil,
		&identityOnlyGatedToggle{identityOnlyToggle{toggle{name: "a", phase: PhaseCanonical, fires: true}}},
		&identityOnlyGatedToggle{identityOnlyToggle{toggle{name: "b", phase: PhaseCanonical, fires: true}}},
	)
	s.Validations = 3
	d := &validationFallbackDriver{fakeDriver: &fakeDriver{
		metrics:  map[string]Metrics{"": {Instructions: 100}, "a": {Instructions: 5}, "b": {Instructions: 7}, "recovered": {Instructions: 9}},
		verdicts: map[string]Outcome{"": Trusted, "a": Trusted, "b": Trusted},
	}}
	d.proposal = func(c *Candidate) *Candidate {
		// Like removing the only gated transform from a parent, this
		// configuration is ungated, but still needs its own validation.
		return optFallbackWithoutGates(c, config{switches: []string{"recovered"}})
	}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if !sel.Candidate.IsIdentity() || sel.Verdict.Outcome != Trusted || !reflect.DeepEqual(d.validated, []string{"a", "b", ""}) || len(sel.Validations) != 3 {
		t.Fatalf("gated recovery exceeded reserved budget: selected %s (%s), validated %v", sel.Candidate.Name(), sel.Verdict.Outcome, d.validated)
	}
}

func optFallbackWithoutGates(parent *Candidate, cfg config) *Candidate {
	next := parent.Reconfigured(cfg)
	next.Applied = []string{"ungated-fallback"}
	return next
}
