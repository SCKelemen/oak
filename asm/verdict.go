package asm

// Verdict is the outcome of verifying one asm function against its Oak body.
type Verdict struct {
	Kind    VerdictKind
	Message string
	// TransientResourceExhausted prevents persisting a negative result that
	// overlapped temporary admission pressure, possibly in a concurrent
	// query. It is false for proven results and concrete mismatches.
	TransientResourceExhausted bool `json:"-"`
	// Callees are the program functions the verdict took at their Oak
	// bodies (call summaries, docs/spec/94-assembler.md §8): a proven
	// verdict is relative to theirs, so the verified profile accepts the
	// body only when every one of them is proven too (compiler.verifiedProfile).
	Callees []string
}

// verdictWithCallees attaches the exact dependency union accumulated by
// independent verifier runs (result chunks or vector halves). First occurrence
// determines the stable order; the returned slice never aliases an executor.
func verdictWithCallees(verdict Verdict, groups ...[]string) Verdict {
	seen := make(map[string]bool)
	callees := make([]string, 0)
	for _, group := range groups {
		for _, callee := range group {
			if seen[callee] {
				continue
			}
			seen[callee] = true
			callees = append(callees, callee)
		}
	}
	verdict.Callees = callees
	return verdict
}

type VerdictKind int

const (
	VerdictTrusted   VerdictKind = iota // not verified; trusted per §5
	VerdictProven                       // canonical normal forms agree
	VerdictWitnessed                    // witnesses agree; no proof
	VerdictMismatch                     // a witness disagrees: definite bug
)

func (k VerdictKind) String() string {
	switch k {
	case VerdictProven:
		return "proven"
	case VerdictWitnessed:
		return "witness-checked"
	case VerdictMismatch:
		return "mismatch"
	}
	return "trusted"
}

// composeProvenPair joins two independently established proof results. Callers
// retain their existing evaluation and failure-selection order; this boundary
// cannot upgrade either missing proof. Each input must already include all of
// its value, effect and trap-domain obligations. Callee closure remains the
// compiler's responsibility, and Verdict remains a public, writable record.
func composeProvenPair(first, second Verdict, message string) Verdict {
	if first.Kind != VerdictProven {
		return first
	}
	if second.Kind != VerdictProven {
		return second
	}
	return verdictWithCallees(
		Verdict{Kind: VerdictProven, Message: message},
		first.Callees, second.Callees,
	)
}
