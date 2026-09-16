// Package opt is the candidate-search optimization substrate of the Oak
// compiler (docs/notes/optimizer-search-2026-09.md, Phase A;
// docs/notes/proof-guided-optimization-2026-09.md §1, §3, §26).
//
// The rule the package encodes: an optimizer proposes implementations, a
// cost model chooses among them, and independent validation decides
// whether the chosen implementation is admissible. Nothing in this package
// is part of the semantic trusted base — a transform is an untrusted
// proposal generator, a cost estimate can make code slower but never
// wrong, and the Driver's validation (the seam checker and the semantic
// verifier on the native lane) is the only authority on whether a
// candidate ships. The identity implementation is always a candidate, and
// the fallback when nothing else is admitted.
//
// The package is target-independent: a Candidate's configuration and body
// are opaque to it, and a Driver supplied by the backend materializes,
// measures, checks, and validates them.
package opt

import (
	"fmt"
	"strings"
)

// Provenance says how a Fact was established, ordered by strength: a
// Requirement names the weakest provenance that satisfies it
// (docs/notes/proof-guided-optimization-2026-09.md §1, §27). The order
// follows the proof statuses of the checked semantic model
// (semir.ProofStatus) with two optimizer-only rungs below them: a
// Heuristic is a cost model's or planner's guess and never licenses a
// removal; an Analyzed fact is derived by an optimizer analysis from
// stronger facts and is a candidate fact, not a semantic license.
type Provenance int

const (
	Heuristic Provenance = iota
	Analyzed
	Tested
	ModelChecked
	Refined
	Checked // established by the typechecker, the borrow checker, or the extents decider
	ProvedSMT
	ProvedKernel // a kernel-checked theorem (Lean)
)

func (p Provenance) String() string {
	switch p {
	case Heuristic:
		return "heuristic"
	case Analyzed:
		return "analyzed"
	case Tested:
		return "tested"
	case ModelChecked:
		return "model-checked"
	case Refined:
		return "refined"
	case Checked:
		return "checked"
	case ProvedSMT:
		return "proved-smt"
	case ProvedKernel:
		return "proved-kernel"
	}
	return fmt.Sprintf("provenance(%d)", int(p))
}

// Proposition is a semantic statement a transform may consume: a kind
// (`index-in-extent`, `associative`, `aligned`, `noalias`, `pure`, ...)
// over its terms, spelled as the compiler names them. Two propositions
// are the same when their kinds and terms agree.
type Proposition struct {
	Kind  string
	Terms []string
}

// Prop builds a Proposition.
func Prop(kind string, terms ...string) Proposition {
	return Proposition{Kind: kind, Terms: terms}
}

func (p Proposition) String() string {
	if len(p.Terms) == 0 {
		return p.Kind
	}
	return p.Kind + "(" + strings.Join(p.Terms, ", ") + ")"
}

// Equal reports whether two propositions agree in kind and terms.
func (p Proposition) Equal(q Proposition) bool {
	if p.Kind != q.Kind || len(p.Terms) != len(q.Terms) {
		return false
	}
	for i := range p.Terms {
		if p.Terms[i] != q.Terms[i] {
			return false
		}
	}
	return true
}

// Fact is a Proposition with its provenance and where it was established,
// carried into the optimizer instead of collapsed to a boolean, so a
// remark can name the fact that licensed a transform
// (docs/notes/proof-guided-optimization-2026-09.md §1).
type Fact struct {
	// ID is the stable identity of the checked/proved fact when one exists.
	// Empty IDs are permitted for language-wide laws, but a downstream seam
	// that consumes source-specific evidence must require one.
	ID          string
	Proposition Proposition
	Provenance  Provenance
	// Source names the establishing authority: a checker and its entry
	// point, a Lean theorem, a solver query.
	Source string
	// Scope is the program point the fact holds at (a function, a source
	// line, a loop); empty for a fact of the whole body or the language.
	Scope string
	// Dependencies name the already-checked propositions used by the
	// establishing authority. They are explanatory/provenance data, not a
	// second way to satisfy a Requirement.
	Dependencies []Proposition
}

func (f Fact) String() string {
	out := f.Proposition.String() + " [" + f.Provenance.String()
	if f.Source != "" {
		out += ", " + f.Source
	}
	out += "]"
	if f.Scope != "" {
		out += " at " + f.Scope
	}
	return out
}

// Facts is the set of facts known of one region (a function body today).
type Facts struct {
	facts []Fact
}

// NewFacts builds a fact set.
func NewFacts(facts ...Fact) *Facts {
	set := &Facts{}
	set.Add(facts...)
	return set
}

// Add records facts.
func (f *Facts) Add(facts ...Fact) {
	if f == nil {
		return
	}
	for _, fact := range facts {
		f.facts = append(f.facts, cloneFact(fact))
	}
}

// Len is the number of facts.
func (f *Facts) Len() int {
	if f == nil {
		return 0
	}
	return len(f.facts)
}

// All returns the facts in the order added.
func (f *Facts) All() []Fact {
	if f == nil {
		return nil
	}
	out := make([]Fact, len(f.facts))
	for index, fact := range f.facts {
		out[index] = cloneFact(fact)
	}
	return out
}

func cloneFact(fact Fact) Fact {
	fact.Proposition.Terms = append([]string(nil), fact.Proposition.Terms...)
	fact.Dependencies = append([]Proposition(nil), fact.Dependencies...)
	for index := range fact.Dependencies {
		fact.Dependencies[index].Terms = append([]string(nil), fact.Dependencies[index].Terms...)
	}
	return fact
}

// Has finds a fact stating p with at least the given provenance.
func (f *Facts) Has(p Proposition, min Provenance) (Fact, bool) {
	if f == nil {
		return Fact{}, false
	}
	for _, fact := range f.facts {
		if fact.Provenance >= min && fact.Proposition.Equal(p) {
			return fact, true
		}
	}
	return Fact{}, false
}

// OfKind returns every fact of the kind with at least the given
// provenance.
func (f *Facts) OfKind(kind string, min Provenance) []Fact {
	if f == nil {
		return nil
	}
	var out []Fact
	for _, fact := range f.facts {
		if fact.Provenance >= min && fact.Proposition.Kind == kind {
			out = append(out, fact)
		}
	}
	return out
}

// Requirement is what a transform asks of the fact set before it may
// propose: a proposition at a minimum provenance. A requirement whose
// proposition has no terms is satisfied by any fact of the kind — the
// transform then decides per site which fact it uses.
type Requirement struct {
	Proposition Proposition
	Min         Provenance
}

// Require builds a Requirement.
func Require(p Proposition, min Provenance) Requirement {
	return Requirement{Proposition: p, Min: min}
}

func (r Requirement) String() string {
	return r.Proposition.String() + " with proof >= " + r.Min.String()
}

// Discharge finds a fact satisfying the requirement.
func (r Requirement) Discharge(f *Facts) (Fact, bool) {
	if len(r.Proposition.Terms) == 0 {
		facts := f.OfKind(r.Proposition.Kind, r.Min)
		if len(facts) == 0 {
			return Fact{}, false
		}
		return facts[0], true
	}
	return f.Has(r.Proposition, r.Min)
}
