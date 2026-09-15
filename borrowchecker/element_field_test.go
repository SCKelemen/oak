package borrowchecker

import (
	"strings"
	"testing"
)

// view(&s[i].field) / span(&s[i].field): an owned-array field of a span,
// view, or array element (docs/spec/50-borrowing.md section 2). Through an
// owned array the borrow is of the array; through a span or view binding
// it is a reborrow of that binding, so a writable field span needs a span.
const elementFieldSource = `
Stage: type = struct { coeffs: [5]f32, state: [2]f32 }
total: (xs: []f32): f32 { 0.0 }
fill: (ys: [*]f32): u32 { u32(0) }
`

func TestElementFieldBorrowsAccepted(t *testing.T) {
	for name, src := range map[string]string{
		"view through a view param": elementFieldSource + "fn f(stages: []Stage, k: u32) -> f32 { total(view(&stages[k].coeffs)) }",
		"view through a span param": elementFieldSource + "fn f(stages: [*]Stage, k: u32) -> f32 { total(view(&stages[k].coeffs)) }",
		"span through a span param": elementFieldSource + "fn f(stages: [*]Stage, k: u32) -> u32 { fill(span(&stages[k].state)) }",
		"bound view through a view": elementFieldSource + "fn f(stages: []Stage, k: u32) -> f32 { c: []f32 = view(&stages[k].coeffs)\ntotal(c) }",
		"view of an owned array":    elementFieldSource + "fn f() -> f32 { stages: [2]Stage = [Stage { coeffs: [1.0, 2.0, 3.0, 4.0, 5.0], state: [0.0, 0.0] }, Stage { coeffs: [1.0, 1.0, 1.0, 1.0, 1.0], state: [0.0, 0.0] }]\nc: []f32 = view(&stages[1].coeffs)\ntotal(c) }",
		"span of an owned array":    elementFieldSource + "fn f() -> u32 { stages: [2]Stage = [Stage { coeffs: [1.0, 2.0, 3.0, 4.0, 5.0], state: [0.0, 0.0] }, Stage { coeffs: [1.0, 1.0, 1.0, 1.0, 1.0], state: [0.0, 0.0] }]\ns: [*]f32 = span(&stages[1].state)\nfill(s) }",
	} {
		bc := checkSource(t, src)
		if len(bc.Diagnostics()) != 0 {
			t.Errorf("%s: expected clean, got:\n%s", name, diagText(bc))
		}
	}
}

func TestElementFieldSpanThroughViewRejected(t *testing.T) {
	src := elementFieldSource + "fn f(stages: []Stage, k: u32) -> u32 { fill(span(&stages[k].state)) }"
	bc := checkSource(t, src)
	text := diagText(bc)
	if !strings.Contains(text, "is a read-only view; a writable field span needs a span") {
		t.Fatalf("a writable field span through a read-only view must be refused, got:\n%s", text)
	}
}

func TestElementFieldSpanWhileOwnerViewedRejected(t *testing.T) {
	// The field span borrows the owned array whole: a live view of the
	// array refuses it, as span(&stages) would.
	src := elementFieldSource + "fn f() -> u32 { stages: [2]Stage = [Stage { coeffs: [1.0, 2.0, 3.0, 4.0, 5.0], state: [0.0, 0.0] }, Stage { coeffs: [1.0, 1.0, 1.0, 1.0, 1.0], state: [0.0, 0.0] }]\nc: []f32 = view(&stages[0].coeffs)\ns: [*]f32 = span(&stages[1].state)\nfill(s) }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeSpanConflictsWithView)); got != 1 {
		t.Fatalf("a field span of a viewed array produced %d conflicts, want 1:\n%s", got, diagText(bc))
	}
}
