package opt

import (
	"errors"
	"strings"
	"testing"
)

// A fake lane for the search: a configuration is a set of switches, a
// body is the spelled switches, and the driver's tables say what each body
// costs and how validation judges it.
type config struct{ switches []string }

func (c config) has(name string) bool {
	for _, s := range c.switches {
		if s == name {
			return true
		}
	}
	return false
}

func (c config) with(name string) config {
	return config{switches: append(append([]string(nil), c.switches...), name)}
}

func (c config) key() string { return strings.Join(c.switches, "+") }

type toggle struct {
	name  string
	phase Phase
	reqs  []Requirement
	// fires says whether the switch changes the body.
	fires bool
	// refines maps a finding to the switch to add on refinement.
	refines map[string]string
}

func (t *toggle) Name() string                { return t.name }
func (t *toggle) Phase() Phase                { return t.phase }
func (t *toggle) Proof() ProofKind            { return Mechanical }
func (t *toggle) Requirements() []Requirement { return t.reqs }
func (t *toggle) Apply(c *Candidate) *Candidate {
	cfg := c.Config.(config)
	if cfg.has(t.name) {
		return nil
	}
	return c.With(t.name, cfg.with(t.name))
}
func (t *toggle) Fired(c *Candidate) int {
	if t.fires {
		return 1
	}
	return 0
}
func (t *toggle) Refine(c *Candidate, finding string) (*Candidate, bool) {
	add, ok := t.refines[finding]
	if !ok {
		return nil, false
	}
	cfg := c.Config.(config)
	if cfg.has(add) {
		return nil, false
	}
	return c.Reconfigured(cfg.with(add)), true
}

type fakeDriver struct {
	metrics   map[string]Metrics  // by body key; absent means the identity's metrics
	verdicts  map[string]Outcome  // by body key; absent means Proven
	findings  map[string][]string // by body key; absent means admitted
	unlowered map[string]bool     // bodies that do not lower
	lowerErrs map[string]error    // exact lowering errors used by artifact tests
	validated []string
	checked   []string
	measured  []string
	lowered   []string
}

func (d *fakeDriver) MaterializationKey(c *Candidate) (string, error) {
	return "fake:" + c.Config.(config).key(), nil
}

func (d *fakeDriver) Materialize(c *Candidate) error {
	key := c.Config.(config).key()
	d.lowered = append(d.lowered, key)
	if err := d.lowerErrs[key]; err != nil {
		return err
	}
	if d.unlowered[key] {
		return errors.New("unsupported form")
	}
	c.Body = key
	return nil
}
func (d *fakeDriver) Key(c *Candidate) string { return c.Body.(string) }
func (d *fakeDriver) Measure(c *Candidate) Metrics {
	d.measured = append(d.measured, c.Body.(string))
	if m, ok := d.metrics[c.Body.(string)]; ok {
		return m
	}
	return Metrics{Instructions: 10, Branches: 2, Loads: 2, Guards: 1}
}
func (d *fakeDriver) Check(c *Candidate) []string {
	d.checked = append(d.checked, c.Body.(string))
	return d.findings[c.Body.(string)]
}
func (d *fakeDriver) Validate(c *Candidate) Verdict {
	key := c.Body.(string)
	d.validated = append(d.validated, key)
	if outcome, ok := d.verdicts[key]; ok {
		return Verdict{Outcome: outcome, Message: outcome.String()}
	}
	return Verdict{Outcome: Proven, Message: "proven"}
}

func newSearch(report *Report, transforms ...Transform) *Search {
	return &Search{Registry: NewRegistry(transforms...), Costs: AArch64Costs, Report: report}
}

func TestSearchSelectsCheapestProven(t *testing.T) {
	report := &Report{}
	s := newSearch(report,
		&toggle{name: "a", phase: PhaseCanonical, fires: true},
		&toggle{name: "b", phase: PhaseLoop, fires: true},
	)
	d := &fakeDriver{metrics: map[string]Metrics{
		"a":   {Instructions: 8, Branches: 2, Loads: 2, Guards: 1},
		"b":   {Instructions: 9, Branches: 2, Loads: 2, Guards: 1},
		"a+b": {Instructions: 6, Branches: 1, Loads: 2},
	}}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if got := sel.Candidate.Name(); got != "a+b" {
		t.Fatalf("selected %s, want a+b", got)
	}
	if sel.Verdict.Outcome != Proven {
		t.Fatalf("verdict %s", sel.Verdict.Outcome)
	}
	if len(d.validated) != 1 || d.validated[0] != "a+b" {
		t.Fatalf("validated %v, want only the cheapest", d.validated)
	}
	text := report.String()
	for _, want := range []string{"passed    a", "passed    b", "analysis  metrics", "instructions:      10 -> 6", "guards:            1 -> 0"} {
		if !strings.Contains(text, want) {
			t.Errorf("report lacks %q:\n%s", want, text)
		}
	}
}

func TestSearchFallsBackToIdentity(t *testing.T) {
	report := &Report{}
	s := newSearch(report, &toggle{name: "a", phase: PhaseCanonical, fires: true})
	d := &fakeDriver{
		metrics:  map[string]Metrics{"a": {Instructions: 5}},
		verdicts: map[string]Outcome{"a": Witnessed},
	}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if !sel.Candidate.IsIdentity() || sel.Verdict.Outcome != Proven {
		t.Fatalf("selected %s (%s), want the proven identity", sel.Candidate.Name(), sel.Verdict.Outcome)
	}
	if len(d.validated) != 2 {
		t.Fatalf("validated %v, want the candidate then the identity", d.validated)
	}
	if !strings.Contains(report.String(), "the a form was judged witnessed") {
		t.Errorf("report lacks the set-aside remark:\n%s", report.String())
	}
}

func TestSearchKeepsStrongerVerdictOnTie(t *testing.T) {
	// Both witnessed: the cheaper (optimized) body is kept, as the
	// compiler's reduction fallback did.
	s := newSearch(nil, &toggle{name: "a", phase: PhaseCanonical, fires: true})
	d := &fakeDriver{
		metrics:  map[string]Metrics{"a": {Instructions: 5}},
		verdicts: map[string]Outcome{"a": Witnessed, "": Witnessed},
	}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if sel.Candidate.Name() != "a" || sel.Verdict.Outcome != Witnessed {
		t.Fatalf("selected %s (%s), want the witnessed a", sel.Candidate.Name(), sel.Verdict.Outcome)
	}
}

func TestSearchRequirementsGate(t *testing.T) {
	report := &Report{}
	need := Require(Prop("index-in-extent"), Checked)
	s := newSearch(report, &toggle{name: "elide", phase: PhaseMemory, fires: true, reqs: []Requirement{need}})
	d := &fakeDriver{metrics: map[string]Metrics{"elide": {Instructions: 5}}}
	sel, err := s.Run("f", Identity(config{}), NewFacts(Fact{Proposition: Prop("index-in-extent", "v[i]"), Provenance: Analyzed}), d)
	if err != nil {
		t.Fatal(err)
	}
	if !sel.Candidate.IsIdentity() {
		t.Fatalf("selected %s without a checked fact", sel.Candidate.Name())
	}
	if !strings.Contains(report.String(), "requires index-in-extent with proof >= checked") {
		t.Errorf("report lacks the missing requirement:\n%s", report.String())
	}
	if len(d.lowered) != 1 {
		t.Fatalf("lowered %v: a transform without its fact must not be proposed", d.lowered)
	}

	report = &Report{}
	s.Report = report
	d = &fakeDriver{metrics: map[string]Metrics{"elide": {Instructions: 5}}}
	fact := Fact{Proposition: Prop("index-in-extent", "v[i]"), Provenance: Checked, Source: "IndexProven"}
	sel, err = s.Run("f", Identity(config{}), NewFacts(fact), d)
	if err != nil {
		t.Fatal(err)
	}
	if sel.Candidate.Name() != "elide" {
		t.Fatalf("selected %s with the fact", sel.Candidate.Name())
	}
	if !strings.Contains(report.String(), "fact index-in-extent(v[i]) [checked, IndexProven]") {
		t.Errorf("report does not name the licensing fact:\n%s", report.String())
	}
}

func TestSearchPrunesUnfiredAndDuplicateBodies(t *testing.T) {
	report := &Report{}
	s := newSearch(report,
		&toggle{name: "quiet", phase: PhaseCanonical, fires: false},
		&toggle{name: "same", phase: PhaseControl, fires: true},
	)
	d := &fakeDriver{}
	// "same" materializes to a body with the identity's key.
	d.metrics = map[string]Metrics{}
	same := &fakeDriverSameBody{fakeDriver: d}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), same)
	if err != nil {
		t.Fatal(err)
	}
	if !sel.Candidate.IsIdentity() {
		t.Fatalf("selected %s", sel.Candidate.Name())
	}
	text := report.String()
	if !strings.Contains(text, "quiet              no site to transform") || !strings.Contains(text, "the same body as identity") {
		t.Errorf("report lacks the pruning remarks:\n%s", text)
	}
	if len(d.validated) != 1 {
		t.Fatalf("validated %v", d.validated)
	}
}

// fakeDriverSameBody keys every body as the identity's.
type fakeDriverSameBody struct{ *fakeDriver }

func (d *fakeDriverSameBody) Key(c *Candidate) string { return "" }

func TestSearchRefinesRefusedCandidate(t *testing.T) {
	report := &Report{}
	elide := &toggle{name: "elide", phase: PhaseMemory, fires: true, refines: map[string]string{"f:12: guard": "keep12"}}
	s := newSearch(report, elide)
	d := &fakeDriver{
		findings: map[string][]string{"elide": {"f:12: guard"}},
		metrics:  map[string]Metrics{"elide+keep12": {Instructions: 7}},
	}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if sel.Candidate.Name() != "elide" || sel.Candidate.Refined != 1 {
		t.Fatalf("selected %s refined %d", sel.Candidate.Name(), sel.Candidate.Refined)
	}
	if cfg := sel.Candidate.Config.(config); !cfg.has("keep12") {
		t.Fatalf("refined configuration %v lacks the kept line", cfg)
	}

	// A finding the transform cannot act on drops the candidate.
	d = &fakeDriver{findings: map[string][]string{"elide": {"f: something else"}}}
	sel, err = s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if !sel.Candidate.IsIdentity() {
		t.Fatalf("selected %s", sel.Candidate.Name())
	}
}

func TestSearchRefusedIdentity(t *testing.T) {
	s := newSearch(nil, &toggle{name: "a", phase: PhaseCanonical, fires: true})
	d := &fakeDriver{findings: map[string][]string{"": {"f:3: width"}}}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if sel.Verdict.Outcome != Refused || len(sel.Verdict.Findings) != 1 || len(d.validated) != 0 {
		t.Fatalf("verdict %v, validated %v", sel.Verdict, d.validated)
	}
}

func TestSearchIdentityDoesNotLower(t *testing.T) {
	s := newSearch(nil)
	d := &fakeDriver{unlowered: map[string]bool{"": true}}
	if _, err := s.Run("f", Identity(config{}), NewFacts(), d); err == nil {
		t.Fatal("expected the identity's error")
	}
}

func TestSearchBeamAndValidationBudget(t *testing.T) {
	var transforms []Transform
	metrics := map[string]Metrics{}
	verdicts := map[string]Outcome{}
	for _, name := range []string{"a", "b", "c", "d", "e"} {
		transforms = append(transforms, &toggle{name: name, phase: PhaseCanonical, fires: true})
	}
	// Every combination lowers to a distinct body; cost falls with the
	// number of switches, and no optimized body proves.
	d := &budgetDriver{fakeDriver: &fakeDriver{metrics: metrics, verdicts: verdicts}}
	report := &Report{}
	s := &Search{Registry: NewRegistry(transforms...), Costs: AArch64Costs, Beam: 3, Validations: 3, Report: report}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if !sel.Candidate.IsIdentity() {
		t.Fatalf("selected %s", sel.Candidate.Name())
	}
	if len(d.validated) != 3 || d.validated[2] != "" {
		t.Fatalf("validated %v: want two candidates then the identity", d.validated)
	}
	// Beam 3 with the identity among them: at most three parents per
	// transform, so at most fifteen proposals beyond the identity.
	if len(d.lowered) > 16 {
		t.Fatalf("lowered %d bodies under beam 3", len(d.lowered))
	}
}

// budgetDriver costs a body by its switch count and never proves an
// optimized body.
type budgetDriver struct{ *fakeDriver }

func (d *budgetDriver) Measure(c *Candidate) Metrics {
	n := len(c.Config.(config).switches)
	return Metrics{Instructions: 20 - n}
}

func (d *budgetDriver) Validate(c *Candidate) Verdict {
	d.validated = append(d.validated, c.Body.(string))
	if c.IsIdentity() {
		return Verdict{Outcome: Proven, Message: "proven"}
	}
	return Verdict{Outcome: Witnessed, Message: "witnessed"}
}

func TestFactsAndRequirements(t *testing.T) {
	facts := NewFacts(
		Fact{Proposition: Prop("aligned", "p", "16"), Provenance: Checked},
		Fact{Proposition: Prop("associative", "+", "integer"), Provenance: ProvedKernel},
	)
	if _, ok := Require(Prop("aligned", "p", "16"), ProvedKernel).Discharge(facts); ok {
		t.Error("a checked fact discharged a kernel requirement")
	}
	if _, ok := Require(Prop("aligned", "p", "16"), Checked).Discharge(facts); !ok {
		t.Error("a checked fact did not discharge a checked requirement")
	}
	if _, ok := Require(Prop("aligned", "p", "32"), Heuristic).Discharge(facts); ok {
		t.Error("a different term discharged")
	}
	if fact, ok := Require(Prop("associative"), ProvedKernel).Discharge(facts); !ok || fact.Proposition.String() != "associative(+, integer)" {
		t.Errorf("kind-only requirement: %v %v", fact, ok)
	}
}

func TestCostPrefersShorterLoops(t *testing.T) {
	straight := Metrics{Instructions: 20, Branches: 2}
	loop := Metrics{Instructions: 12, Branches: 2, Loops: 1, LoopInstructions: 6, LoopBranches: 2}
	if AArch64Costs.Estimate(loop) <= AArch64Costs.Estimate(straight) {
		t.Errorf("a six-instruction loop (%.1f) should cost more than twenty straight instructions (%.1f)", AArch64Costs.Estimate(loop), AArch64Costs.Estimate(straight))
	}
	guarded := Metrics{Instructions: 10, Branches: 2, Guards: 1}
	unguarded := Metrics{Instructions: 8, Branches: 1}
	if AArch64Costs.Estimate(unguarded) >= AArch64Costs.Estimate(guarded) {
		t.Error("removing a guard should lower the cost")
	}
}

// A nested loop's body runs its trips for every trip of its outer loop:
// an instruction saved there is worth LoopWeight times one saved in the
// outer loop's own body, and the two loops' items are not double-counted.
func TestCostWeighsNesting(t *testing.T) {
	nested := func(outer, inner int) Metrics {
		return Metrics{Instructions: outer + inner + 4, Branches: 4, Loops: 2, LoopInstructions: outer + inner, LoopBranches: 4,
			LoopBodies: []LoopMetrics{{Instructions: outer, Branches: 2, Stride: 1}, {Instructions: inner, Branches: 2, Stride: 1, Depth: 1, Outer: 1}}}
	}
	base := AArch64Costs.Estimate(nested(10, 10))
	innerSaved := AArch64Costs.Estimate(nested(10, 9))
	outerSaved := AArch64Costs.Estimate(nested(9, 10))
	if base-innerSaved != AArch64Costs.LoopWeight*AArch64Costs.LoopWeight || base-outerSaved != AArch64Costs.LoopWeight {
		t.Errorf("an inner instruction weighs %.1f and an outer one %.1f; want %.1f and %.1f", base-innerSaved, base-outerSaved, AArch64Costs.LoopWeight*AArch64Costs.LoopWeight, AArch64Costs.LoopWeight)
	}
}

func TestPruneKeepsIdentity(t *testing.T) {
	identity := Identity(config{})
	identity.Cost = 100
	cheap := []*Candidate{{Applied: []string{"a"}, Cost: 1}, {Applied: []string{"b"}, Cost: 2}, {Applied: []string{"c"}, Cost: 3}}
	kept := prune(append(cheap, identity), 2, identity)
	if len(kept) != 2 || kept[0].Name() != "a" || kept[1] != identity {
		t.Fatalf("kept %v", kept)
	}
}

func TestSearchWeighsLoopStride(t *testing.T) {
	report := &Report{}
	s := newSearch(report, &toggle{name: "unroll", phase: PhaseLoop, fires: true})
	// The unrolled body is longer — a main loop and a remainder loop — but
	// the main loop's trips advance four elements and the remainder runs
	// three trips at most, so it is the cheaper candidate.
	d := &fakeDriver{metrics: map[string]Metrics{
		"": {Instructions: 10, Branches: 2, Loads: 1, Loops: 1, LoopInstructions: 6, LoopBranches: 2, LoopLoads: 1,
			LoopBodies: []LoopMetrics{{Instructions: 6, Branches: 2, Loads: 1, Stride: 1}}},
		"unroll": {Instructions: 24, Branches: 4, Loads: 5, Loops: 2, LoopInstructions: 18, LoopBranches: 4, LoopLoads: 5,
			LoopBodies: []LoopMetrics{{Instructions: 12, Branches: 2, Loads: 4, Stride: 4}, {Instructions: 6, Branches: 2, Loads: 1, Stride: 1, MaxTrips: 3}}},
	}}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if sel.Candidate.Name() != "unroll" {
		t.Fatalf("selected %s (cost %.1f vs identity %.1f)", sel.Candidate.Name(), sel.Candidate.Cost, sel.Identity.Cost)
	}
	if sel.Candidate.Cost >= sel.Identity.Cost {
		t.Fatalf("unrolled cost %.1f not below identity %.1f", sel.Candidate.Cost, sel.Identity.Cost)
	}
}

// gatedToggle ships only on a verdict.
type gatedToggle struct{ toggle }

func (g *gatedToggle) NeedsVerdict() bool { return true }

func TestSearchTrustedVerdictNeedsUngatedForm(t *testing.T) {
	// The verifier could judge neither form. A transform that ships only
	// on a verdict is set aside for the plain lowering, priced higher or
	// not; a transform that ships on the checker's admission stays.
	report := &Report{}
	s := newSearch(report, &gatedToggle{toggle{name: "a", phase: PhaseCanonical, fires: true}})
	d := &fakeDriver{
		metrics:  map[string]Metrics{"a": {Instructions: 5}},
		verdicts: map[string]Outcome{"a": Trusted, "": Trusted},
	}
	sel, err := s.Run("f", Identity(config{}), NewFacts(), d)
	if err != nil {
		t.Fatal(err)
	}
	if !sel.Candidate.IsIdentity() || sel.Verdict.Outcome != Trusted {
		t.Fatalf("selected %s (%s)", sel.Candidate.Name(), sel.Verdict.Outcome)
	}
	if !strings.Contains(report.String(), "ships only on a verdict") {
		t.Errorf("report:\n%s", report.String())
	}
	s = newSearch(nil, &toggle{name: "b", phase: PhaseCanonical, fires: true})
	d = &fakeDriver{metrics: map[string]Metrics{"b": {Instructions: 5}}, verdicts: map[string]Outcome{"b": Trusted, "": Trusted}}
	sel, _ = s.Run("f", Identity(config{}), NewFacts(), d)
	if sel.Candidate.Name() != "b" {
		t.Fatalf("selected %s: an ungated transform ships on the checker's admission", sel.Candidate.Name())
	}
	// Both together: the gated one goes, the ungated form is kept.
	report = &Report{}
	s = newSearch(report, &toggle{name: "b", phase: PhaseCanonical, fires: true}, &gatedToggle{toggle{name: "a", phase: PhaseMachine, fires: true}})
	d = &fakeDriver{metrics: map[string]Metrics{"b": {Instructions: 6}, "a": {Instructions: 6}, "b+a": {Instructions: 4}}, verdicts: map[string]Outcome{"b+a": Trusted, "a": Trusted, "b": Trusted, "": Trusted}}
	sel, _ = s.Run("f", Identity(config{}), NewFacts(), d)
	if sel.Candidate.Name() != "b" {
		t.Fatalf("selected %s, want b:\n%s", sel.Candidate.Name(), report.String())
	}
	// A witnessed transformed form is evidence and may ship.
	s = newSearch(nil, &gatedToggle{toggle{name: "a", phase: PhaseCanonical, fires: true}})
	d = &fakeDriver{metrics: map[string]Metrics{"a": {Instructions: 5}}, verdicts: map[string]Outcome{"a": Witnessed, "": Witnessed}}
	sel, _ = s.Run("f", Identity(config{}), NewFacts(), d)
	if sel.Candidate.Name() != "a" {
		t.Fatalf("selected %s", sel.Candidate.Name())
	}
}
