package asm

// This file owns verifier outcomes, not the decision procedures that produce
// them. A witnessed match is never promoted to a proof by this layer.

// Verdict is the outcome of verifying one asm function against its Oak body.
type Verdict struct {
	Kind    VerdictKind
	Message string
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
