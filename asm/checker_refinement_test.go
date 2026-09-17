package asm

import (
	"fmt"
	"math"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// The seam checker's region decisions against their Lean transliteration
// (spec/lean/Oak/CheckerRefinement.lean): each case renders the Go
// decision — the inputs and the derived region or the admission — as the
// `example` the Lean file states and Lean's kernel checks by `decide`, so
// the two cannot drift: a case the Go decides differently fails here, a
// case the Lean decides differently fails `lake build`.
func TestCheckerDecisionsMatchLeanTransliteration(t *testing.T) {
	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "CheckerRefinement.lean"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(lean)
	i64 := func(v int64) *int64 { return &v }
	imm := func(bound int64) idxFact { return idxFact{boundReg: -1, bound: bound} }
	reg := func(r int, bound int64, slack bool) idxFact { return idxFact{boundReg: r, bound: bound, slack: slack} }
	span := func(elem int64, writable, hasMin bool, minLen int64, lens ...int) *spanFact {
		f := &spanFact{lenReg: -1, elem: elem, writable: writable, hasMin: hasMin, minLen: minLen, lenRegs: map[int]bool{}}
		for _, l := range lens {
			f.lenRegs[l] = true
			if f.lenReg < 0 {
				f.lenReg = l
			}
		}
		return f
	}
	type elementCase struct {
		name      string
		frame     int64
		frameAddr *int64
		span      *spanFact
		extent    *region
		bound     idxFact
		size      int64
	}
	elementCases := []elementCase{
		{"frame array of four words", 16, i64(-16), nil, nil, imm(4), 4},
		{"frame array past the frame", 16, i64(-16), nil, nil, imm(5), 4},
		{"frame array under a register bound", 16, i64(-16), nil, nil, reg(1, 0, false), 4},
		{"span element under its length register", 0, nil, span(8, true, false, 0, 1), nil, reg(1, 0, false), 8},
		{"span element under a constant below the minimum", 0, nil, span(8, false, true, 4, 1), nil, imm(4), 8},
		{"span element above the minimum", 0, nil, span(8, false, true, 4, 1), nil, imm(5), 8},
		{"span lanes under a slack guard", 0, nil, span(1, true, true, 16, 1), nil, reg(1, 16, true), 1},
		{"four u64 span cells under a slack guard", 0, nil, span(8, true, true, 4, 1), nil, reg(1, 4, true), 8},
		{"span of another element size", 0, nil, span(4, true, false, 0, 1), nil, reg(1, 0, false), 8},
		{"table of thirty-two bytes", 0, nil, nil, &region{size: 32}, imm(32), 1},
		{"table read past its size", 0, nil, nil, &region{size: 32}, imm(33), 1},
	}
	var missing []string
	for _, tc := range elementCases {
		var want string
		if r, ok := elementRegionOf(tc.frame, tc.frameAddr, tc.span, tc.extent, tc.bound, tc.size); ok {
			want = fmt.Sprintf("some ⟨%d, %v⟩", r.size, r.writable)
		} else {
			want = "none"
		}
		line := fmt.Sprintf("example : elementRegion %d %s (some %s) %d = %s := by decide", tc.frame, renderBase(tc.frameAddr, tc.span, tc.extent), renderIdx(tc.bound), tc.size, want)
		if !strings.Contains(text, line) {
			missing = append(missing, tc.name+":\n  "+line)
		}
	}
	type accessCase struct {
		name    string
		extent  region
		isStore bool
		off     int64
		size    int64
		index   *idxFact
	}
	for _, tc := range []accessCase{
		{"a word at offset four of a twelve-byte record", region{size: 12, writable: true}, false, 4, 4, nil},
		{"a word past the record", region{size: 12, writable: true}, false, 12, 4, nil},
		{"a store through a read-only copy", region{size: 12, writable: false}, true, 0, 4, nil},
		{"an indexed byte under a guard that fits", region{size: 32, writable: false}, false, 0, 1, ptrIdx(imm(32))},
		{"an indexed word under a guard that does not fit", region{size: 12, writable: true}, false, 0, 4, ptrIdx(imm(4))},
		{"a pair store over the first two of four u64 cells", region{size: 32, writable: true}, true, 0, 16, nil},
		{"a pair store over the last two of four u64 cells", region{size: 32, writable: true}, true, 16, 16, nil},
		{"a pair store past four u64 cells", region{size: 32, writable: true}, true, 24, 16, nil},
		{"a pair store through a read-only u64 view", region{size: 32, writable: false}, true, 0, 16, nil},
	} {
		got := regionAdmits(tc.extent, tc.isStore, tc.off, tc.size, tc.index)
		line := fmt.Sprintf("example : regionAdmits ⟨%d, %v⟩ %v %d %d %s = %v := by decide", tc.extent.size, tc.extent.writable, tc.isStore, tc.off, tc.size, renderOptIdx(tc.index), got)
		if !strings.Contains(text, line) {
			missing = append(missing, tc.name+":\n  "+line)
		}
	}
	type frameCase struct {
		name  string
		frame int64
		base  int64
		off   int64
		size  int64
		index *idxFact
	}
	for _, tc := range []frameCase{
		{"a word inside the frame", 16, -16, 4, 4, nil},
		{"a word past the frame's end", 16, -16, 12, 8, nil},
		{"four words under a constant guard", 16, -16, 0, 4, ptrIdx(imm(4))},
		{"five words under a constant guard", 16, -16, 0, 4, ptrIdx(imm(5))},
		{"a register bound", 16, -16, 0, 4, ptrIdx(reg(1, 0, false))},
	} {
		got := frameArrayAdmits(tc.frame, tc.base, tc.off, tc.size, tc.index)
		line := fmt.Sprintf("example : frameArrayAdmits %d %s %d %d %s = %v := by decide", tc.frame, renderInt(tc.base), tc.off, tc.size, renderOptIdx(tc.index), got)
		if !strings.Contains(text, line) {
			missing = append(missing, tc.name+":\n  "+line)
		}
	}
	type recordCase struct {
		name  string
		span  *spanFact
		bound idxFact
		size  int64
	}
	record := span(2072, true, false, 0, 1)
	record.record = "Regime"
	slackRecord := span(2072, true, true, 4, 1)
	slackRecord.record = "Regime"
	for _, tc := range []recordCase{
		{"one exact Regime element", record, reg(1, 0, false), 2072},
		{"a slack region has no single-record provenance", slackRecord, reg(1, 4, true), 2072},
		{"a different stride has no Regime provenance", record, reg(1, 0, false), 8},
	} {
		place, ok := exactSpanRecord(tc.span, tc.bound, tc.size)
		want := "none"
		if ok {
			want = fmt.Sprintf("some ⟨%q, %d⟩", place.name, place.offset)
		}
		line := fmt.Sprintf("example : exactSpanRecord %q %s %s %d = %s := by decide", tc.span.record, renderSpanFact(tc.span), renderIdx(tc.bound), tc.size, want)
		if !strings.Contains(text, line) {
			missing = append(missing, tc.name+":\n  "+line)
		}
	}
	for _, tc := range []struct {
		name   string
		place  recordPlace
		offset int64
	}{
		{"the pages field offset", recordPlace{name: "Regime"}, 0},
		{"a field tail offset", recordPlace{name: "Regime"}, 16},
		{"negative offsets are refused", recordPlace{name: "Regime"}, -1},
	} {
		place, ok := narrowRecordPlace(tc.place, tc.offset)
		want := "none"
		if ok {
			want = fmt.Sprintf("some ⟨%q, %d⟩", place.name, place.offset)
		}
		line := fmt.Sprintf("example : narrowRecordPlace ⟨%q, %d⟩ %s = %s := by decide", tc.place.name, tc.place.offset, renderInt(tc.offset), want)
		if !strings.Contains(text, line) {
			missing = append(missing, tc.name+":\n  "+line)
		}
	}
	if len(missing) != 0 {
		t.Fatalf("%d decision(s) not stated in spec/lean/Oak/CheckerRefinement.lean — update the Lean file or the checker:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}

func TestCheckerNominalRecordProvenanceFailsClosed(t *testing.T) {
	spanType := &ast.IndexExpression{Left: &ast.Identifier{Value: "Regime"}, Index: &ast.Identifier{Value: "*"}}
	composites := map[string]Composite{
		"Regime": {Size: 2072},
		"Decoy":  {Size: 2072},
	}
	unit, parseErrors := ParseUnit("provenance.oakasm", "touch: (s: [*]Regime) -> () = {\n  bind x0, w1 = s\n  ret\n}\n")
	if len(parseErrors) != 0 {
		t.Fatal(parseErrors)
	}
	unit.Functions[0].Composites = composites
	bound := &checker{fn: unit.Functions[0]}
	bound.bindContract()
	if len(bound.errors) != 0 || bound.spans[0] == nil || bound.spans[0].record != "Regime" {
		t.Fatalf("checked record-span binding did not retain Regime provenance: errors=%v fact=%+v", bound.errors, bound.spans[0])
	}
	roundTrip := &checker{}
	roundTrip.applyGuards(bound.guardSnapshot())
	if roundTrip.spans[0] == nil || roundTrip.spans[0].record != "Regime" {
		t.Fatalf("guard-state round trip lost Regime provenance: %+v", roundTrip.spans[0])
	}
	if got := recordSpanName(composites, spanType, 2072); got != "Regime" {
		t.Fatalf("exact record span name = %q, want Regime", got)
	}
	if got := recordSpanName(composites, spanType, 2048); got != "" {
		t.Fatalf("mismatched record stride retained provenance %q", got)
	}
	if _, ok := shiftedNonnegative(math.MaxInt64, 12); ok {
		t.Fatal("a shifted immediate that overflows int64 retained provenance")
	}
	if got, ok := shiftedNonnegative(4095, 12); !ok || got != 4095<<12 {
		t.Fatalf("legal shifted immediate = (%d, %v), want (%d, true)", got, ok, 4095<<12)
	}

	base := &spanFact{lenReg: 1, elem: 2072, writable: true, record: "Regime", lenRegs: map[int]bool{1: true}}
	exact, ok := elementRegionOf(0, nil, base, nil, idxFact{boundReg: 1}, 2072)
	if !ok || exact.record != "Regime" || exact.recordOffset != 0 || exact.size != 2072 {
		t.Fatalf("exact record element = %+v, ok=%v", exact, ok)
	}
	base.hasMin, base.minLen = true, 4
	widened, ok := elementRegionOf(0, nil, base, nil, idxFact{boundReg: 1, bound: 4, slack: true, need: 4}, 2072)
	if !ok || widened.record != "" || widened.recordOffset != 0 || widened.size != 4*2072 {
		t.Fatalf("slack-derived multi-record region retained provenance: %+v, ok=%v", widened, ok)
	}

	tail, ok := narrowRegion(exact, 2048)
	if !ok || tail.record != "Regime" || tail.recordOffset != 2048 || tail.size != 24 {
		t.Fatalf("record tail = %+v, ok=%v", tail, ok)
	}
	malformed := region{size: 8, writable: true, record: "Regime", recordOffset: math.MaxInt64}
	overflow, ok := narrowRegion(malformed, 1)
	if !ok || overflow.record != "" || overflow.recordOffset != 0 || overflow.size != 7 {
		t.Fatalf("overflowing provenance must be cleared without widening bytes: %+v, ok=%v", overflow, ok)
	}

	a := newGuardState()
	b := newGuardState()
	a.spans[0] = &spanImage{lenReg: 1, elem: 2072, writable: true, record: "Regime", lens: map[int]bool{1: true}}
	b.spans[0] = &spanImage{lenReg: 1, elem: 2072, writable: true, record: "Decoy", lens: map[int]bool{1: true}}
	if _, retained := meetGuards(a, b).spans[0]; retained {
		t.Fatal("same-sized nominally different record spans met as one fact")
	}
}

func ptrIdx(f idxFact) *idxFact { return &f }

func renderInt(v int64) string {
	if v < 0 {
		return fmt.Sprintf("(%d)", v)
	}
	return fmt.Sprintf("%d", v)
}

func renderIdx(f idxFact) string {
	return fmt.Sprintf("⟨%s, %d, %v, %d⟩", renderInt(int64(f.boundReg)), f.bound, f.slack, f.need)
}

func renderOptIdx(f *idxFact) string {
	if f == nil {
		return "none"
	}
	return "(some " + renderIdx(*f) + ")"
}

func renderBase(frameAddr *int64, span *spanFact, extent *region) string {
	frame, sp, reg := "none", "none", "none"
	if frameAddr != nil {
		frame = "(some " + renderInt(*frameAddr) + ")"
	}
	if span != nil {
		sp = "(some " + renderSpanFact(span) + ")"
	}
	if extent != nil {
		reg = fmt.Sprintf("(some ⟨%d, %v⟩)", extent.size, extent.writable)
	}
	return fmt.Sprintf("⟨%s, %s, %s⟩", frame, sp, reg)
}

func renderSpanFact(span *spanFact) string {
	var lens []string
	for l := range span.lenRegs {
		lens = append(lens, fmt.Sprintf("%d", l))
	}
	return fmt.Sprintf("⟨%d, %v, %v, %d, [%s]⟩", span.elem, span.writable, span.hasMin, span.minLen, strings.Join(lens, ", "))
}
