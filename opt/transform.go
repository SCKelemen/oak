package opt

import "sort"

// Phase orders the planning: a transform declares the phase it
// participates in, and the search applies phases in this order so it does
// not explore arbitrary permutations
// (docs/notes/optimizer-search-2026-09.md §6).
type Phase int

const (
	PhaseCanonical Phase = iota // constant folding, strength reduction, canonical arithmetic
	PhaseMemory                 // guard elimination, load fusion, addressing forms
	PhaseControl                // condition selection, flag reuse, branch shape
	PhaseLoop                   // hoisting, rotation, unrolling, induction
	PhaseVector                 // vector plans
	PhaseCall                   // inlining, specialization
	PhaseMachine                // selection, scheduling, allocation alternatives
)

func (p Phase) String() string {
	switch p {
	case PhaseCanonical:
		return "canonical"
	case PhaseMemory:
		return "memory"
	case PhaseControl:
		return "control"
	case PhaseLoop:
		return "loop"
	case PhaseVector:
		return "vector"
	case PhaseCall:
		return "call"
	case PhaseMachine:
		return "machine"
	}
	return "phase?"
}

// ProofKind is the correctness mechanism a transform relies on
// (docs/notes/optimizer-search-2026-09.md §2): which boundary decides that
// its candidate is admissible.
type ProofKind int

const (
	// Mechanical changes representation or machine shape without changing
	// the source-level evaluation law; the seam checker and the semantic
	// verifier validate the final candidate.
	Mechanical ProofKind = iota
	// Canonical is a local equality that follows from Oak's fixed-width
	// semantics or an already-proved semantic law (a Lean theorem where
	// one exists); the verifier remains the authority on the body.
	Canonical
	// LawLicensed changes the source evaluation shape and needs an
	// explicit source-level license — a declared operator law or a source
	// theorem — after which the rewritten body is the verifier's reference.
	LawLicensed
)

func (k ProofKind) String() string {
	switch k {
	case Mechanical:
		return "mechanical"
	case Canonical:
		return "canonical"
	case LawLicensed:
		return "law-licensed"
	}
	return "proof?"
}

// Transform is one small proposal generator
// (docs/notes/optimizer-search-2026-09.md §4). It names the facts it
// consumes as Requirements rather than rediscovering them, and proposes a
// new Candidate from an existing one by editing its configuration; the
// Driver materializes the body. A transform never decides admissibility.
type Transform interface {
	Name() string
	Phase() Phase
	Proof() ProofKind
	// Requirements are the facts the transform consumes; the search
	// discharges them against the region's fact set before proposing and
	// records a missed remark naming the missing one otherwise.
	Requirements() []Requirement
	// Apply proposes the candidate with this transform added, or nil when
	// it does not apply to c's configuration (already applied, not on this
	// lane).
	Apply(c *Candidate) *Candidate
}

// Counted is a transform that can report, from the materialized body,
// how many sites it changed: a candidate whose transform changed nothing
// is the same body as its parent and is pruned with a remark instead of
// being costed and validated again.
type Counted interface {
	Fired(c *Candidate) int
}

// Gated is a transform whose candidates ship only on a verifier's
// verdict: when a body cannot be judged (a trusted verdict is the absence
// of a check), a candidate carrying such a transform is set aside for the
// cheapest one without it, at worst the plain lowering. A transform that
// is not Gated ships on the seam checker's admission alone, as the lane's
// transforms did before the search; a new transform is Gated until it has
// earned that standing (docs/spec/90-backend.md §16 rule 3).
type Gated interface {
	NeedsVerdict() bool
}

// Neutral is a gated transform that changes no evaluation shape the
// verifier reads — a register assignment, an instruction order — so a
// candidate carrying it shares its shape with the candidate without it,
// and one validation judges both (Search.shape). A gated transform that
// changes instructions or branches is not neutral: its verdict can
// differ from its parent's, and it is validated on its own.
type Neutral interface {
	ShapeNeutral() bool
}

// Refinable is a transform that can narrow a candidate the checker
// refused — verifier-guided search in its smallest form
// (docs/notes/proof-guided-optimization-2026-09.md §16): the finding
// names what the checker could not admit, and the refined candidate keeps
// the transform everywhere else. Refine returns false when the finding
// names nothing it can act on.
type Refinable interface {
	Refine(c *Candidate, finding string) (*Candidate, bool)
}

// Registry holds the transforms available on a lane, by phase
// (docs/notes/optimizer-search-2026-09.md §16, Phase A item 2).
type Registry struct {
	transforms []Transform
}

// NewRegistry builds a registry of the transforms.
func NewRegistry(transforms ...Transform) *Registry {
	r := &Registry{}
	r.Register(transforms...)
	return r
}

// Register adds transforms; registration order is the order transforms
// compose within a phase.
func (r *Registry) Register(transforms ...Transform) {
	r.transforms = append(r.transforms, transforms...)
}

// Transforms returns every registered transform in phase order,
// registration order within a phase.
func (r *Registry) Transforms() []Transform {
	if r == nil {
		return nil
	}
	out := append([]Transform(nil), r.transforms...)
	sort.SliceStable(out, func(i, j int) bool { return out[i].Phase() < out[j].Phase() })
	return out
}

// Phases returns the phases some registered transform participates in,
// in order.
func (r *Registry) Phases() []Phase {
	if r == nil {
		return nil
	}
	seen := map[Phase]bool{}
	var out []Phase
	for _, t := range r.transforms {
		if !seen[t.Phase()] {
			seen[t.Phase()] = true
			out = append(out, t.Phase())
		}
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}

// ForPhase returns the transforms of one phase in registration order.
func (r *Registry) ForPhase(p Phase) []Transform {
	if r == nil {
		return nil
	}
	var out []Transform
	for _, t := range r.transforms {
		if t.Phase() == p {
			out = append(out, t)
		}
	}
	return out
}

// Lookup finds a transform by name.
func (r *Registry) Lookup(name string) (Transform, bool) {
	if r == nil {
		return nil, false
	}
	for _, t := range r.transforms {
		if t.Name() == name {
			return t, true
		}
	}
	return nil, false
}
