package typechecker

import "strings"

// GeneralizationBarrier records one reason a locally inferred type must remain
// monomorphic. Inference may still determine a precise type; this gate controls
// only whether free type variables may be universally quantified for reuse.
type GeneralizationBarrier uint32

const (
	GeneralizationMutableAuthority GeneralizationBarrier = 1 << iota
	GeneralizationUniqueAuthority
	GeneralizationRegionBound
	GeneralizationExternalAuthority
	GeneralizationEffectfulCapture
	GeneralizationUnsafeAssumption
	GeneralizationUnknownAuthority
)

// GeneralizationFacts are supplied by ownership/effect/region analysis. Keeping
// these facts separate from Type preserves Oak's orthogonal semantic axes: a
// semantic type does not become a different type merely because one expression
// captures authority that prevents polymorphic generalization.
type GeneralizationFacts struct {
	Barriers GeneralizationBarrier
}

func (facts GeneralizationFacts) Safe() bool {
	return facts.Barriers == 0
}

func (facts GeneralizationFacts) Has(barrier GeneralizationBarrier) bool {
	return facts.Barriers&barrier != 0
}

func (facts GeneralizationFacts) With(barrier GeneralizationBarrier) GeneralizationFacts {
	facts.Barriers |= barrier
	return facts
}

// Reasons returns stable human-facing barrier names for diagnostics/tooling.
func (facts GeneralizationFacts) Reasons() []string {
	var reasons []string
	for _, entry := range []struct {
		barrier GeneralizationBarrier
		name    string
	}{
		{GeneralizationMutableAuthority, "mutable authority"},
		{GeneralizationUniqueAuthority, "unique authority"},
		{GeneralizationRegionBound, "region-bound value"},
		{GeneralizationExternalAuthority, "external authority"},
		{GeneralizationEffectfulCapture, "effectful capture"},
		{GeneralizationUnsafeAssumption, "unsafe assumption"},
		{GeneralizationUnknownAuthority, "unresolved authority"},
	} {
		if facts.Has(entry.barrier) {
			reasons = append(reasons, entry.name)
		}
	}
	return reasons
}

func (facts GeneralizationFacts) String() string {
	if facts.Safe() {
		return "safe to generalize"
	}
	return "cannot generalize: " + strings.Join(facts.Reasons(), ", ")
}

// GeneralizeWithFacts performs ordinary free-variable generalization only when
// the authority/effect/region facts prove that universal quantification is safe.
// A blocked binding remains fully inferred but monomorphic.
func GeneralizeWithFacts(typ Type, env *TypeEnvironment, facts GeneralizationFacts) *TypeScheme {
	if facts.Safe() {
		return Generalize(typ, env)
	}
	return &TypeScheme{
		TypeVars:    []string{},
		Constraints: []Constraint{},
		Type:        typ,
	}
}
