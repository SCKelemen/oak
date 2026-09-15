package opt

import (
	"fmt"
	"sort"
	"strings"
)

// RemarkKind classes an optimization remark
// (docs/notes/optimizer-search-2026-09.md §9): an opportunity taken, one
// missed with the reason, or an analysis result such as structural
// before/after metrics.
type RemarkKind int

const (
	Passed RemarkKind = iota
	Missed
	Analysis
)

func (k RemarkKind) String() string {
	switch k {
	case Passed:
		return "passed"
	case Missed:
		return "missed"
	case Analysis:
		return "analysis"
	}
	return "remark?"
}

// Remark is one line of the optimization report: which function, which
// transform (or `search`, `cost`, `verify` for the substrate's own
// remarks), what happened, and the facts used or missing so the report
// names the proposition that licensed or blocked a transform
// (docs/notes/proof-guided-optimization-2026-09.md §30 items 8-9).
type Remark struct {
	Function  string
	Transform string
	Kind      RemarkKind
	Message   string
	Facts     []string
}

// Report collects remarks over a compilation. A nil *Report accepts and
// drops remarks, so callers need not test for one.
type Report struct {
	Remarks []Remark
}

// Add records a remark.
func (r *Report) Add(remark Remark) {
	if r == nil {
		return
	}
	r.Remarks = append(r.Remarks, remark)
}

// Passed records an opportunity taken.
func (r *Report) Passed(function, transform, message string, facts ...string) {
	r.Add(Remark{Function: function, Transform: transform, Kind: Passed, Message: message, Facts: facts})
}

// Missed records an opportunity not taken, with the reason.
func (r *Report) Missed(function, transform, message string, facts ...string) {
	r.Add(Remark{Function: function, Transform: transform, Kind: Missed, Message: message, Facts: facts})
}

// Analysis records an analysis result.
func (r *Report) Analysis(function, transform, message string) {
	r.Add(Remark{Function: function, Transform: transform, Kind: Analysis, Message: message})
}

// For returns the remarks of one function in order.
func (r *Report) For(function string) []Remark {
	if r == nil {
		return nil
	}
	var out []Remark
	for _, remark := range r.Remarks {
		if remark.Function == function {
			out = append(out, remark)
		}
	}
	return out
}

// Functions lists the functions with remarks, sorted.
func (r *Report) Functions() []string {
	if r == nil {
		return nil
	}
	seen := map[string]bool{}
	var out []string
	for _, remark := range r.Remarks {
		if !seen[remark.Function] {
			seen[remark.Function] = true
			out = append(out, remark.Function)
		}
	}
	sort.Strings(out)
	return out
}

// String renders the report in the layout of the design note:
//
//	utf8.valid_with:
//	  passed    strength-reduce   2 constant operation(s) as shifts and masks
//	  missed    elide-guards      the checker did not admit line 84: ...
//	  analysis  search            instructions: 83 -> 57
//	                              guards:       8 -> 0
func (r *Report) String() string {
	if r == nil || len(r.Remarks) == 0 {
		return ""
	}
	var b strings.Builder
	for _, function := range r.Functions() {
		fmt.Fprintf(&b, "%s:\n", function)
		for _, remark := range r.For(function) {
			lines := strings.Split(remark.Message, "\n")
			fmt.Fprintf(&b, "  %-9s %-18s %s\n", remark.Kind, remark.Transform, lines[0])
			for _, line := range lines[1:] {
				fmt.Fprintf(&b, "  %-9s %-18s %s\n", "", "", line)
			}
			for _, fact := range remark.Facts {
				fmt.Fprintf(&b, "  %-9s %-18s   fact %s\n", "", "", fact)
			}
		}
	}
	return b.String()
}
