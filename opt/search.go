package opt

import (
	"fmt"
	"sort"
	"strings"
)

// Outcome is what validation said of a candidate, ordered by strength.
// The native lane's verdicts map onto it (asm.VerdictKind): a candidate
// the seam checker refuses is Refused; the verifier's kinds follow.
type Outcome int

const (
	Refused   Outcome = iota // the checker did not admit the body
	Mismatch                 // the verifier found a witness that disagrees: a definite bug
	Trusted                  // not verified; trusted per the assembler's §5
	Witnessed                // witnesses agree; no proof
	Proven                   // the body is proven equal to its Oak body
)

func (o Outcome) String() string {
	switch o {
	case Refused:
		return "refused"
	case Mismatch:
		return "mismatch"
	case Trusted:
		return "trusted"
	case Witnessed:
		return "witnessed"
	case Proven:
		return "proven"
	}
	return "outcome?"
}

// Verdict is validation's answer for one candidate.
type Verdict struct {
	Outcome Outcome
	Message string
	// Cached marks a verdict served from the verdict cache rather than
	// computed (the compiler's tally).
	Cached bool
	// Findings are the checker's findings for a Refused candidate.
	Findings []string
}

// Driver is the backend's side of the search: it materializes a
// candidate's configuration into a body, identifies and measures the
// body, and validates it. The search never inspects a body itself.
type Driver interface {
	// Materialize lowers c.Config into c.Body. An error means the
	// configuration does not lower (the lane does not support the form);
	// the candidate is dropped with a remark.
	Materialize(c *Candidate) error
	// Key identifies the materialized body so equal bodies are one
	// candidate.
	Key(c *Candidate) string
	// Measure reads the body's structural metrics.
	Measure(c *Candidate) Metrics
	// Check runs the cheap admissibility check (the seam checker): the
	// findings, none when admitted.
	Check(c *Candidate) []string
	// Validate runs the expensive validation (the semantic verifier).
	Validate(c *Candidate) Verdict
}

// Search is the bounded candidate search of one region
// (docs/notes/optimizer-search-2026-09.md §6, §15):
//
//	start with identity
//	for each phase, for each transform: propose from the frontier
//	materialize; drop what does not lower, what changed nothing, and
//	  duplicates; check, refining what the checker refuses; cost
//	keep the best Beam candidates (the identity always among them)
//	validate in cost order within Validations, the identity last
//	take the cheapest proven candidate, else the strongest verdict
type Search struct {
	Registry *Registry
	Costs    CostModel
	// Beam is how many candidates survive each transform's proposals
	// (default 4).
	Beam int
	// Validations bounds how many bodies the expensive validation runs on
	// per region (default 3); the identity always has the last of them
	// when nothing cheaper proved.
	Validations int
	// RefineRounds bounds checker-driven refinement of one candidate
	// (default 8).
	RefineRounds int
	// Report receives the remarks; nil drops them.
	Report *Report
	// Refused, when set, sees every candidate the checker refused with
	// its findings and refinement round (a debugging aid).
	Refused func(c *Candidate, round int, findings []string)
}

// Validated is one candidate the search validated and its verdict.
type Validated struct {
	Candidate *Candidate
	Verdict   Verdict
}

// Selection is the search's result for one region.
type Selection struct {
	// Candidate is the selected implementation; Verdict its validation.
	Candidate *Candidate
	Verdict   Verdict
	// Identity is the identity candidate as materialized, for before/after
	// comparison; it may be the selected candidate.
	Identity *Candidate
	// Validations lists every candidate validated, in the order tried.
	Validations []Validated
	// Frontier is the set of admitted candidates the search ended with, in
	// cost order, the identity last.
	Frontier []*Candidate
	// Considered counts the candidates proposed, Materialized those that
	// lowered.
	Considered, Materialized int
}

// Run searches one region. The identity candidate carries the plain
// configuration; facts are what is known of the region. An error is the
// identity's failure to materialize — the region has no implementation on
// this lane at all.
func (s *Search) Run(function string, identity *Candidate, facts *Facts, d Driver) (*Selection, error) {
	beam, budget, rounds := s.Beam, s.Validations, s.RefineRounds
	if beam <= 0 {
		beam = 4
	}
	if budget <= 0 {
		budget = 3
	}
	if rounds <= 0 {
		rounds = 8
	}
	costs := s.Costs
	if costs == nil {
		costs = AArch64Costs
	}
	sel := &Selection{Identity: identity, Considered: 1}
	if err := d.Materialize(identity); err != nil {
		return nil, err
	}
	sel.Materialized++
	identity.Key = d.Key(identity)
	if findings := s.check(function, identity, d, rounds); len(findings) > 0 {
		// The plain lowering is not admitted: no transform mends a body
		// the checker refuses as written, so the refusal is the answer.
		sel.Candidate = identity
		sel.Verdict = Verdict{Outcome: Refused, Message: findings[0], Findings: findings}
		s.Report.Missed(function, "check", "the checker refuses the plain lowering: "+findings[0])
		return sel, nil
	}
	identity.Metrics = d.Measure(identity)
	identity.Cost = s.cost(costs, identity)

	frontier := []*Candidate{identity}
	seen := map[string]*Candidate{identity.Key: identity}
	for _, phase := range s.Registry.Phases() {
		for _, t := range s.Registry.ForPhase(phase) {
			used, ok := s.discharge(function, t, facts)
			if !ok {
				continue
			}
			var proposals []*Candidate
			for _, parent := range frontier {
				next := t.Apply(parent)
				if next == nil {
					continue
				}
				sel.Considered++
				next.Facts = append(next.Facts, used...)
				if err := d.Materialize(next); err != nil {
					s.Report.Missed(function, t.Name(), fmt.Sprintf("the %s form did not lower: %v", next.Name(), err))
					continue
				}
				sel.Materialized++
				if counted, isCounted := t.(Counted); isCounted && counted.Fired(next) == 0 {
					if parent.IsIdentity() {
						s.Report.Missed(function, t.Name(), "no site to transform")
					}
					continue
				}
				next.Key = d.Key(next)
				if prev, dup := seen[next.Key]; dup {
					if parent.IsIdentity() {
						s.Report.Missed(function, t.Name(), "the same body as "+prev.Name())
					}
					continue
				}
				seen[next.Key] = next
				if findings := s.check(function, next, d, rounds); len(findings) > 0 {
					s.Report.Missed(function, t.Name(), fmt.Sprintf("the checker did not admit the %s form: %s", next.Name(), findings[0]))
					continue
				}
				seen[next.Key] = next // the refinement may have changed the key
				next.Metrics = d.Measure(next)
				next.Cost = s.cost(costs, next)
				proposals = append(proposals, next)
			}
			frontier = prune(append(frontier, proposals...), beam, identity)
		}
	}

	// Validation in cost order, the identity last: a proven candidate ends
	// the search; otherwise the strongest verdict wins, the cheaper body
	// on a tie, so a faster body never ships on a weaker verdict than the
	// plain lowering earns (docs/spec/90-backend.md §16 item 5).
	order := make([]*Candidate, 0, len(frontier))
	for _, c := range frontier {
		if !c.IsIdentity() {
			order = append(order, c)
		}
	}
	sort.SliceStable(order, func(i, j int) bool { return cheaper(order[i], order[j]) })
	order = append(order, identity)
	sel.Frontier = order
	var best *Validated
	for i, c := range order {
		if !c.IsIdentity() && len(sel.Validations) >= budget-1 {
			s.Report.Missed(function, "verify", fmt.Sprintf("the %s form was not verified: %d of %d validations spent on cheaper candidates", c.Name(), len(sel.Validations), budget))
			continue
		}
		verdict := d.Validate(c)
		sel.Validations = append(sel.Validations, Validated{Candidate: c, Verdict: verdict})
		v := &sel.Validations[len(sel.Validations)-1]
		if best == nil || verdict.Outcome > best.Verdict.Outcome {
			best = v
		}
		if verdict.Outcome == Proven {
			for _, rest := range order[i+1:] {
				if !rest.IsIdentity() {
					s.Report.Missed(function, "verify", fmt.Sprintf("the %s form was not verified: the cheaper %s form proved", rest.Name(), c.Name()))
				}
			}
			break
		}
	}
	sel.Candidate, sel.Verdict = best.Candidate, best.Verdict
	s.remark(function, sel)
	return sel, nil
}

// cost estimates a candidate from its metrics.
func (s *Search) cost(costs CostModel, c *Candidate) float64 {
	return costs.Estimate(c.Metrics)
}

// discharge finds the facts a transform requires, or records the missing
// requirement.
func (s *Search) discharge(function string, t Transform, facts *Facts) ([]Fact, bool) {
	var used []Fact
	for _, req := range t.Requirements() {
		fact, found := req.Discharge(facts)
		if !found {
			s.Report.Missed(function, t.Name(), "requires "+req.String()+"; no such fact is known of the body")
			return nil, false
		}
		used = append(used, fact)
	}
	return used, true
}

// check runs the checker on a candidate, refining it through its
// Refinable transforms while the checker refuses and a transform can act
// on the finding; the candidate is updated in place through its
// configuration and body. It returns the findings that remain.
func (s *Search) check(function string, c *Candidate, d Driver, rounds int) []string {
	findings := d.Check(c)
	for round := 0; len(findings) > 0 && round < rounds; round++ {
		if s.Refused != nil {
			s.Refused(c, round, findings)
		}
		refined, ok := s.refine(c, findings[0])
		if !ok {
			break
		}
		if err := d.Materialize(refined); err != nil {
			break
		}
		refined.Key = d.Key(refined)
		*c = *refined
		findings = d.Check(c)
	}
	return findings
}

// refine asks the candidate's transforms, last applied first, to narrow
// it from the finding.
func (s *Search) refine(c *Candidate, finding string) (*Candidate, bool) {
	for i := len(c.Applied) - 1; i >= 0; i-- {
		t, ok := s.Registry.Lookup(c.Applied[i])
		if !ok {
			continue
		}
		if refinable, ok := t.(Refinable); ok {
			if refined, ok := refinable.Refine(c, finding); ok {
				return refined, true
			}
		}
	}
	return nil, false
}

// cheaper orders candidates by the model's cost; at one cost the
// candidate with more transforms applied comes first, since the static
// model cannot see what a residency transform saves (a vector home
// against a slot round trip is one load and one store either way) and an
// admitted transformed body is preferred to a plainer one at equal price
// (docs/notes/optimizer-search-2026-09.md §0, the tie-break).
func cheaper(a, b *Candidate) bool {
	if a.Cost != b.Cost {
		return a.Cost < b.Cost
	}
	return len(a.Applied) > len(b.Applied)
}

// prune keeps the beam cheapest candidates, the identity always among
// them; order among equal costs is by transforms applied, then the order
// proposed.
func prune(candidates []*Candidate, beam int, identity *Candidate) []*Candidate {
	if len(candidates) <= beam {
		return candidates
	}
	sort.SliceStable(candidates, func(i, j int) bool { return cheaper(candidates[i], candidates[j]) })
	kept := candidates[:beam]
	for _, c := range kept {
		if c == identity {
			return kept
		}
	}
	return append(kept[:beam-1:beam-1], identity)
}

// remark explains the selection: a passed remark per transform of the
// selected candidate with the facts it consumed, a missed remark per
// validated candidate the verdict set aside, and the structural
// before/after.
func (s *Search) remark(function string, sel *Selection) {
	if s.Report == nil {
		return
	}
	best := sel.Candidate
	for _, name := range best.Applied {
		t, _ := s.Registry.Lookup(name)
		message := "selected"
		if counted, ok := t.(Counted); ok {
			message = fmt.Sprintf("%d site(s), %s", counted.Fired(best), sel.Verdict.Outcome)
		} else {
			message = message + ", " + sel.Verdict.Outcome.String()
		}
		var facts []string
		if t != nil {
			for _, req := range t.Requirements() {
				for _, fact := range best.Facts {
					if fact.Proposition.Kind == req.Proposition.Kind {
						facts = append(facts, fact.String())
						break
					}
				}
			}
		}
		s.Report.Passed(function, name, message, facts...)
	}
	for _, v := range sel.Validations {
		if v.Candidate == best {
			continue
		}
		s.Report.Missed(function, "verify", fmt.Sprintf("the %s form was judged %s: %s", v.Candidate.Name(), v.Verdict.Outcome, v.Verdict.Message))
	}
	s.Report.Analysis(function, "search", fmt.Sprintf("%d candidate(s) considered, %d lowered, %d verified; selected %s (%s, cost %.1f; identity %.1f)", sel.Considered, sel.Materialized, len(sel.Validations), best.Name(), sel.Verdict.Outcome, best.Cost, sel.Identity.Cost))
	if len(sel.Frontier) > 1 {
		lines := make([]string, 0, len(sel.Frontier))
		for _, c := range sel.Frontier {
			lines = append(lines, fmt.Sprintf("%-32s cost %7.1f  %s", c.Name(), c.Cost, c.Metrics))
		}
		s.Report.Analysis(function, "candidates", strings.Join(lines, "\n"))
	}
	if best != sel.Identity {
		s.Report.Analysis(function, "metrics", Delta(sel.Identity.Metrics, best.Metrics))
	}
}
