package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"
)

// The alias rules against their Lean transliteration
// (spec/lean/Oak/SpanAlias.lean): each case builds the checker's fact maps,
// runs the write's forgetting and the move's aliasing as the checker does
// at `mov`, and renders what each register then holds as the
// `example … := by decide` line the Lean file states — so the Go and the
// model whose soundness is proved there cannot drift.
func TestSpanAliasMatchesLeanTransliteration(t *testing.T) {
	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "SpanAlias.lean"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(lean)
	type state struct {
		name    string
		spans   map[int]*spanFact
		regions map[int]region
		idx     map[int]idxFact
	}
	// A span in x0 measured by w1 and w5 with a proven minimum, a record
	// region in x2, guards on w3 (below w1), w4 (below an immediate), and
	// w6 (two short of w5).
	st0 := func() state {
		return state{
			name: "st0",
			spans: map[int]*spanFact{
				0: {lenReg: 1, elem: 8, writable: true, hasMin: true, minLen: 4, lenRegs: map[int]bool{1: true, 5: true}},
			},
			regions: map[int]region{2: {size: 24, writable: false}},
			idx: map[int]idxFact{
				3: {boundReg: 1, bound: 0, slack: false},
				4: {boundReg: -1, bound: 16, slack: false},
				6: {boundReg: 5, bound: 2, slack: true},
			},
		}
	}
	// A span whose only length register is w5.
	st1 := func() state {
		return state{
			name: "st1",
			spans: map[int]*spanFact{
				0: {lenReg: 5, elem: 1, writable: false, hasMin: true, minLen: 4, lenRegs: map[int]bool{5: true}},
			},
			regions: map[int]region{},
			idx:     map[int]idxFact{},
		}
	}
	x := func(n int) Register { return Register{Text: fmt.Sprintf("x%d", n), Class: ClassX, Num: n} }
	w := func(n int) Register { return Register{Text: fmt.Sprintf("w%d", n), Class: ClassW, Num: n} }
	cases := []struct {
		name      string
		st        func() state
		dest, src Register
	}{
		{"a base parked", st0, x(19), x(0)},
		{"a region parked", st0, x(20), x(2)},
		{"a length copied", st0, w(21), w(1)},
		{"a guard copied", st0, w(22), w(3)},
		{"a slack guard copied", st0, w(7), w(6)},
		{"a length register overwritten by a base copy", st0, x(1), x(0)},
		{"the last length register overwritten", st1, x(5), x(9)},
		{"a base moved onto itself", st0, x(0), x(0)},
	}
	sortedKeys := func(ks []int) []int { sort.Ints(ks); return ks }
	renderSpan := func(f *spanFact) string {
		var regs []int
		for r := range f.lenRegs {
			regs = append(regs, r)
		}
		var parts []string
		for _, r := range sortedKeys(regs) {
			parts = append(parts, fmt.Sprint(r))
		}
		return fmt.Sprintf("⟨%d, %v, %v, %d, [%s]⟩", f.elem, f.writable, f.hasMin, f.minLen, strings.Join(parts, ", "))
	}
	renderRegion := func(e region) string { return fmt.Sprintf("⟨%d, %v⟩", e.size, e.writable) }
	renderIdx := func(g idxFact) string { return fmt.Sprintf("⟨%d, %d, %v⟩", g.boundReg, g.bound, g.slack) }
	renderState := func(s state) string {
		var spans, regions, idx []string
		var keys []int
		for k := range s.spans {
			keys = append(keys, k)
		}
		for _, k := range sortedKeys(keys) {
			spans = append(spans, fmt.Sprintf("(%d, %s)", k, renderSpan(s.spans[k])))
		}
		keys = nil
		for k := range s.regions {
			keys = append(keys, k)
		}
		for _, k := range sortedKeys(keys) {
			regions = append(regions, fmt.Sprintf("(%d, %s)", k, renderRegion(s.regions[k])))
		}
		keys = nil
		for k := range s.idx {
			keys = append(keys, k)
		}
		for _, k := range sortedKeys(keys) {
			idx = append(idx, fmt.Sprintf("(%d, %s)", k, renderIdx(s.idx[k])))
		}
		return fmt.Sprintf("def %s : Facts := ⟨[%s], [%s], [%s]⟩", s.name, strings.Join(spans, ", "), strings.Join(regions, ", "), strings.Join(idx, ", "))
	}
	var missing []string
	require := func(name, line string) {
		if !strings.Contains(text, line) {
			missing = append(missing, name+":\n  "+line)
		}
	}
	for _, s := range []state{st0(), st1()} {
		require(s.name, renderState(s))
	}
	for _, tc := range cases {
		s := tc.st()
		// Every register a fact names, and the move's two.
		query := map[int]bool{tc.dest.Num: true, tc.src.Num: true}
		for k := range s.spans {
			query[k] = true
		}
		for k := range s.regions {
			query[k] = true
		}
		for k := range s.idx {
			query[k] = true
		}
		c := &checker{spans: s.spans, regions: s.regions, idxFacts: s.idx}
		c.forgetRegisterFacts(tc.dest.Num)
		c.aliasSpan(tc.dest, tc.src)
		move := "movX"
		if tc.dest.Class == ClassW {
			move = "movW"
		}
		after := fmt.Sprintf("(%s %s %d %d)", move, s.name, tc.dest.Num, tc.src.Num)
		var regs []int
		for r := range query {
			regs = append(regs, r)
		}
		for _, r := range sortedKeys(regs) {
			span, region, idx := "none", "none", "none"
			if f, has := c.spans[r]; has {
				span = "some " + renderSpan(f)
			}
			if e, has := c.regions[r]; has {
				region = "some " + renderRegion(e)
			}
			if g, has := c.idxFacts[r]; has {
				idx = "some " + renderIdx(g)
			}
			// The move's own registers are stated whatever they hold; the
			// others only where a fact survives.
			moved := r == tc.dest.Num || r == tc.src.Num
			if moved || span != "none" {
				require(tc.name, fmt.Sprintf("example : lookupReg %s.spans %d = %s := by decide", after, r, span))
			}
			if moved || region != "none" {
				require(tc.name, fmt.Sprintf("example : lookupReg %s.regions %d = %s := by decide", after, r, region))
			}
			if moved || idx != "none" {
				require(tc.name, fmt.Sprintf("example : lookupReg %s.idx %d = %s := by decide", after, r, idx))
			}
		}
	}
	if len(missing) != 0 {
		t.Fatalf("%d fact(s) not stated in spec/lean/Oak/SpanAlias.lean — update the Lean file or the alias rules:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}
