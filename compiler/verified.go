package compiler

import (
	"fmt"
	"regexp"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// The verified build (docs/spec/94-assembler.md §9, the verified gate): a
// program is accepted only when every function with a body reached the
// native backend, passed the seam checker, and was proven equal to its Oak
// body — and, since a proven verdict is relative to the callees it took at
// their Oak bodies, only when every such callee is accepted too, to a
// fixpoint. Everything else is rejected with its reason, and the reasons
// are counted: the list of what stands between the program and a proof.

// NativeOutcome is what the native backend did with one function.
type NativeOutcome struct {
	Name string
	// Kind: OutcomeProven, OutcomeWitnessed, OutcomeTrusted, OutcomeMismatch,
	// OutcomeLeft (the body stayed with the C backend), OutcomeRefused (the
	// seam checker refused the lowering).
	Kind   string
	Reason string
	// Callees the verdict rests on (asm.Verdict.Callees).
	Callees []string
}

const (
	OutcomeProven    = "proven"
	OutcomeWitnessed = "witnessed"
	OutcomeTrusted   = "trusted"
	OutcomeMismatch  = "mismatch"
	OutcomeLeft      = "left to the C backend"
	OutcomeRefused   = "refused by the checker"
)

// VerifiedReport is the verified build's finding: the accepted functions,
// the rejected ones with their reasons, and the reasons counted.
type VerifiedReport struct {
	Total    int
	Accepted []string
	Rejected []NativeOutcome // Reason is the final reason: its own, or the callee it rests on
	Kinds    map[string]int  // outcome kind -> functions
	// Histogram counts the rejection reasons with names and numbers
	// abstracted (`a call to F`, `parameter P`, `N bytes`), so alike
	// reasons fall together.
	Histogram map[string]int
}

// Verified runs the native backend over the program and applies the gate.
func (comp Compilation) Verified() Stage[*VerifiedReport] {
	comp.options.NativeBodies = true
	comp.options.NativeAsm = true
	return comp.Lower().Then(func(lowered *LoweredProgram) (*VerifiedReport, error) {
		if comp.options.Target.AsmArch() == "" {
			return nil, fmt.Errorf("verified: %s has no native lane; the verified build needs the arm64 or rv64 lane", comp.options.Target)
		}
		return verifiedGate(lowered), nil
	})
}

// verifiedGate decides the report from the lowered program's outcomes.
func verifiedGate(lowered *LoweredProgram) *VerifiedReport {
	outcomes := map[string]NativeOutcome{}
	for _, outcome := range lowered.Model.NativeReport {
		outcomes[outcome.Name] = outcome
	}
	// Every function with a body is judged; one the native backend never
	// saw (a method, a generic template, an asm unit's declaration) is
	// outside the lane.
	var names []string
	for _, stmt := range lowered.Root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.ExternSymbol != "" {
			continue
		}
		if fn.Body == nil && !fn.AsmBacked {
			continue
		}
		name := fn.Name.Value
		names = append(names, name)
		if _, seen := outcomes[name]; seen {
			continue
		}
		switch {
		case fn.AsmBacked:
			outcomes[name] = NativeOutcome{Name: name, Kind: OutcomeTrusted, Reason: "an asm unit (trusted per docs/spec/94-assembler.md §5)"}
		case fn.Receiver != nil:
			outcomes[name] = NativeOutcome{Name: name, Kind: OutcomeLeft, Reason: "a method (outside the native backend)"}
		case len(fn.TypeParams) > 0:
			outcomes[name] = NativeOutcome{Name: name, Kind: OutcomeLeft, Reason: "a generic template (its instantiations are judged)"}
		default:
			outcomes[name] = NativeOutcome{Name: name, Kind: OutcomeLeft, Reason: "not reached by the native backend"}
		}
	}
	sort.Strings(names)
	report := &VerifiedReport{Total: len(names), Kinds: map[string]int{}, Histogram: map[string]int{}}
	accepted := map[string]bool{}
	for _, name := range names {
		report.Kinds[outcomes[name].Kind]++
		if outcomes[name].Kind == OutcomeProven {
			accepted[name] = true
		}
	}
	why := acceptedClosure(names, outcomes, accepted)
	for _, name := range names {
		if accepted[name] {
			report.Accepted = append(report.Accepted, name)
			continue
		}
		outcome := outcomes[name]
		if reason, relative := why[name]; relative {
			outcome.Reason = reason
		} else if outcome.Reason == "" {
			outcome.Reason = outcome.Kind
		} else if outcome.Kind != OutcomeProven {
			outcome.Reason = outcome.Kind + ": " + outcome.Reason
		}
		report.Rejected = append(report.Rejected, outcome)
		report.Histogram[abstractReason(outcome.Reason)]++
	}
	return report
}

// acceptedClosure removes from accepted, to a fixpoint, every function
// whose verdict rests on a callee that is not accepted, and says why: a
// proven verdict is relative to the callees it took at their Oak bodies.
func acceptedClosure(names []string, outcomes map[string]NativeOutcome, accepted map[string]bool) map[string]string {
	why := map[string]string{}
	for changed := true; changed; {
		changed = false
		for _, name := range names {
			if !accepted[name] {
				continue
			}
			for _, callee := range outcomes[name].Callees {
				if accepted[callee] {
					continue
				}
				kind := "not judged"
				if c, known := outcomes[callee]; known {
					kind = c.Kind
				}
				why[name] = fmt.Sprintf("rests on the call to %s, which is not accepted (%s)", callee, kind)
				delete(accepted, name)
				changed = true
				break
			}
		}
	}
	return why
}

var (
	reasonCallees = regexp.MustCompile(`\b(a call to|the call to|calls|for) [A-Za-z_][A-Za-z_0-9]*`)
	reasonLocals  = regexp.MustCompile(`\b(parameter|the span local|the span argument|the local|local|the global|global) [A-Za-z_][A-Za-z_0-9]*`)
	reasonTypes   = regexp.MustCompile(`\b(of type|the field|the variant|the record|the array field) [A-Za-z_][A-Za-z_0-9]*`)
	reasonShapes  = regexp.MustCompile(`\(([A-Za-z_][A-Za-z_0-9]*)\.\*?\)`)
	reasonNumbers = regexp.MustCompile(`\b[0-9]+\b`)
)

// abstractReason folds the names and numbers out of a reason so the
// histogram counts shapes: `a call to F`, `parameter P of type T`.
func abstractReason(reason string) string {
	out := reasonCallees.ReplaceAllString(reason, "$1 F")
	out = reasonLocals.ReplaceAllString(out, "$1 P")
	out = reasonTypes.ReplaceAllString(out, "$1 T")
	out = reasonShapes.ReplaceAllString(out, "(T)")
	out = reasonNumbers.ReplaceAllString(out, "N")
	return out
}

// String renders the report: the totals, the histogram (largest first),
// and every rejected function with its reason.
func (r *VerifiedReport) String() string {
	var b strings.Builder
	fmt.Fprintf(&b, "verified: %d functions: %d accepted, %d rejected", r.Total, len(r.Accepted), len(r.Rejected))
	var kinds []string
	for kind := range r.Kinds {
		kinds = append(kinds, kind)
	}
	sort.Slice(kinds, func(i, j int) bool {
		if r.Kinds[kinds[i]] != r.Kinds[kinds[j]] {
			return r.Kinds[kinds[i]] > r.Kinds[kinds[j]]
		}
		return kinds[i] < kinds[j]
	})
	var parts []string
	for _, kind := range kinds {
		parts = append(parts, fmt.Sprintf("%d %s", r.Kinds[kind], kind))
	}
	fmt.Fprintf(&b, " (%s)\n", strings.Join(parts, ", "))
	if len(r.Rejected) == 0 {
		return b.String()
	}
	type bucket struct {
		reason string
		count  int
	}
	var buckets []bucket
	for reason, count := range r.Histogram {
		buckets = append(buckets, bucket{reason, count})
	}
	sort.Slice(buckets, func(i, j int) bool {
		if buckets[i].count != buckets[j].count {
			return buckets[i].count > buckets[j].count
		}
		return buckets[i].reason < buckets[j].reason
	})
	b.WriteString("what stands between the program and a proof:\n")
	for _, bk := range buckets {
		fmt.Fprintf(&b, "  %4d  %s\n", bk.count, bk.reason)
	}
	b.WriteString("rejected:\n")
	for _, outcome := range r.Rejected {
		fmt.Fprintf(&b, "  %s: %s\n", outcome.Name, outcome.Reason)
	}
	return b.String()
}

// outcomeKind names a verdict kind as the report does.
func outcomeKind(kind interface{ String() string }) string {
	switch kind.String() {
	case "proven":
		return OutcomeProven
	case "witness-checked":
		return OutcomeWitnessed
	case "mismatch":
		return OutcomeMismatch
	}
	return OutcomeTrusted
}
