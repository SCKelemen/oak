package opt

import "strings"

// Candidate is one proposed implementation of a region
// (docs/notes/optimizer-search-2026-09.md §3): the transforms applied to
// reach it, its configuration for the backend (opaque here; the native
// lane's nativegen.Lane), the body the Driver materialized from that
// configuration, the body's structural metrics and estimated cost, and the
// facts its transforms consumed. Plans share nothing mutable: Apply and
// Refine clone.
type Candidate struct {
	// Applied names the transforms applied, in order; empty for the
	// identity.
	Applied []string
	// Config is the backend's plan for lowering this candidate.
	Config any
	// Body is the materialized implementation, nil until the Driver
	// materializes it.
	Body any
	// Key identifies the body for de-duplication (Driver.Key); two
	// candidates with one key are one implementation.
	Key string
	// Metrics are the body's structural measurements (Driver.Measure).
	Metrics Metrics
	// Cost is the cost model's estimate of Metrics; lower is better.
	Cost float64
	// Facts are the facts the applied transforms consumed, for the remark
	// that explains the selection.
	Facts []Fact
	// Refined counts the checker-driven refinements of this candidate.
	Refined int
}

// Identity is the candidate with no transform applied: the plain lowering,
// always in the search and always the fallback.
func Identity(config any) *Candidate {
	return &Candidate{Config: config}
}

// Name spells the candidate: the transforms applied joined with `+`, or
// `identity`.
func (c *Candidate) Name() string {
	if c == nil || len(c.Applied) == 0 {
		return "identity"
	}
	return strings.Join(c.Applied, "+")
}

// IsIdentity reports whether no transform was applied.
func (c *Candidate) IsIdentity() bool { return c == nil || len(c.Applied) == 0 }

// Has reports whether the named transform was applied.
func (c *Candidate) Has(transform string) bool {
	if c == nil {
		return false
	}
	for _, name := range c.Applied {
		if name == transform {
			return true
		}
	}
	return false
}

// With clones the candidate with one more transform applied and the new
// configuration; the body, key, metrics, and cost are the Driver's to fill
// again.
func (c *Candidate) With(transform string, config any, facts ...Fact) *Candidate {
	out := &Candidate{
		Applied: append(append([]string(nil), c.Applied...), transform),
		Config:  config,
		Facts:   append(append([]Fact(nil), c.Facts...), facts...),
	}
	return out
}

// Reconfigured clones the candidate with the same transforms applied and
// a new configuration (a refinement).
func (c *Candidate) Reconfigured(config any) *Candidate {
	return &Candidate{
		Applied: append([]string(nil), c.Applied...),
		Config:  config,
		Facts:   append([]Fact(nil), c.Facts...),
		Refined: c.Refined + 1,
	}
}
