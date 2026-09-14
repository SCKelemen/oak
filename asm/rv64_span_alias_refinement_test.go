package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"
)

// The RV64 checker's move rule against its Lean transliteration
// (spec/lean/Oak/RiscVSpanAlias.lean): each case builds the checker's fact
// maps, runs the write's forgetting and `addi rd, rs, 0`'s aliasing from
// the snapshot as the checker does, and renders what each register then
// holds as the `example … := by decide` line the Lean file states — so
// the Go and the model whose soundness is proved there cannot drift.
func TestRV64SpanAliasMatchesLeanTransliteration(t *testing.T) {
	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "RiscVSpanAlias.lean"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(lean)
	type state struct {
		name     string
		spans    map[int]*rvSpan
		lenNorm  map[int]int
		lenAlias map[int]int
		consts   map[int]int64
		regions  map[int]rvRegion
		rawDead  map[int]bool
	}
	// A span based in a0 bound with raw length a1 and a proven minimum,
	// its length normalized into a2 and parked raw in s2, a constant in
	// a3, a record's address in a4.
	rv0 := func() state {
		return state{
			name:     "rv0",
			spans:    map[int]*rvSpan{10: {rawLen: 11, elem: 8, writable: true, hasMin: true, minLen: 4}},
			lenNorm:  map[int]int{12: 11},
			lenAlias: map[int]int{18: 11},
			consts:   map[int]int64{13: 7},
			regions:  map[int]rvRegion{14: {size: 24, writable: false, rawLen: -1, idxReg: -2}},
			rawDead:  map[int]bool{},
		}
	}
	// The same span after its raw length register died.
	rv1 := func() state {
		return state{
			name:     "rv1",
			spans:    map[int]*rvSpan{10: {rawLen: 11, elem: 1, writable: false}},
			lenNorm:  map[int]int{12: 11},
			lenAlias: map[int]int{},
			consts:   map[int]int64{},
			regions:  map[int]rvRegion{},
			rawDead:  map[int]bool{11: true},
		}
	}
	x := func(n int) Register { return Register{Text: fmt.Sprintf("x%d", n), Class: ClassRV64X, Num: n} }
	cases := []struct {
		name      string
		st        func() state
		dest, src Register
	}{
		{"a base parked", rv0, x(19), x(10)},
		{"a raw length parked", rv0, x(20), x(11)},
		{"a parked raw length copied again", rv0, x(21), x(18)},
		{"a normalized length copied", rv0, x(22), x(12)},
		{"a constant copied", rv0, x(23), x(13)},
		{"a region parked", rv0, x(24), x(14)},
		{"the raw length register overwritten by a base copy", rv0, x(11), x(10)},
		{"li from x0", rv0, x(25), x(0)},
		{"a base moved onto itself", rv0, x(10), x(10)},
		{"a dead raw length register copied", rv1, x(26), x(11)},
		{"a normalized copy of a dead raw length copied", rv1, x(27), x(12)},
	}
	sortedKeys := func(ks []int) []int { sort.Ints(ks); return ks }
	renderSpan := func(f *rvSpan) string {
		return fmt.Sprintf("⟨%d, %d, %v, %v, %d⟩", f.rawLen, f.elem, f.writable, f.hasMin, f.minLen)
	}
	renderRegion := func(e rvRegion) string { return fmt.Sprintf("⟨%d, %v⟩", e.size, e.writable) }
	renderState := func(s state) string {
		var spans, norms, aliases, consts, regions, dead []string
		var keys []int
		for k := range s.spans {
			keys = append(keys, k)
		}
		for _, k := range sortedKeys(keys) {
			spans = append(spans, fmt.Sprintf("(%d, %s)", k, renderSpan(s.spans[k])))
		}
		keys = nil
		for k := range s.lenNorm {
			keys = append(keys, k)
		}
		for _, k := range sortedKeys(keys) {
			norms = append(norms, fmt.Sprintf("(%d, %d)", k, s.lenNorm[k]))
		}
		keys = nil
		for k := range s.lenAlias {
			keys = append(keys, k)
		}
		for _, k := range sortedKeys(keys) {
			aliases = append(aliases, fmt.Sprintf("(%d, %d)", k, s.lenAlias[k]))
		}
		keys = nil
		for k := range s.consts {
			keys = append(keys, k)
		}
		for _, k := range sortedKeys(keys) {
			consts = append(consts, fmt.Sprintf("(%d, %d)", k, s.consts[k]))
		}
		keys = nil
		for k := range s.regions {
			keys = append(keys, k)
		}
		for _, k := range sortedKeys(keys) {
			regions = append(regions, fmt.Sprintf("(%d, %s)", k, renderRegion(s.regions[k])))
		}
		keys = nil
		for k, isDead := range s.rawDead {
			if isDead {
				keys = append(keys, k)
			}
		}
		for _, k := range sortedKeys(keys) {
			dead = append(dead, fmt.Sprint(k))
		}
		return fmt.Sprintf("def %s : Facts := ⟨[%s], [%s], [%s], [%s], [%s], [%s]⟩", s.name,
			strings.Join(spans, ", "), strings.Join(norms, ", "), strings.Join(aliases, ", "),
			strings.Join(consts, ", "), strings.Join(regions, ", "), strings.Join(dead, ", "))
	}
	var missing []string
	require := func(name, line string) {
		if !strings.Contains(text, line) {
			missing = append(missing, name+":\n  "+line)
		}
	}
	for _, s := range []state{rv0(), rv1()} {
		require(s.name, renderState(s))
	}
	for _, tc := range cases {
		s := tc.st()
		query := map[int]bool{tc.dest.Num: true, tc.src.Num: true}
		for k := range s.spans {
			query[k] = true
		}
		for k := range s.lenNorm {
			query[k] = true
		}
		for k := range s.lenAlias {
			query[k] = true
		}
		for k := range s.consts {
			query[k] = true
		}
		for k := range s.regions {
			query[k] = true
		}
		for k := range s.rawDead {
			query[k] = true
		}
		c := &rvChecker{spans: s.spans, lenNorm: s.lenNorm, lenAlias: s.lenAlias, consts: s.consts, regions: s.regions, rawDead: s.rawDead, gen: map[int]int{}}
		// As the instruction handler does: snapshot, write, derive.
		pre := c.snapshot()
		if tc.dest.Num != 0 {
			c.forgetRegister(tc.dest.Num)
		}
		pre.deriveShift(c, "addi", tc.dest, tc.src, 0)
		after := fmt.Sprintf("(mv %s %d %d)", s.name, tc.dest.Num, tc.src.Num)
		var regs []int
		for r := range query {
			regs = append(regs, r)
		}
		for _, r := range sortedKeys(regs) {
			moved := r == tc.dest.Num || r == tc.src.Num
			state := func(field, value string, has bool) {
				if !moved && !has {
					return
				}
				if !has {
					value = "none"
				}
				require(tc.name, fmt.Sprintf("example : lookupReg %s.%s %d = %s := by decide", after, field, r, value))
			}
			f, hasSpan := c.spans[r]
			span := ""
			if hasSpan {
				span = "some " + renderSpan(f)
			}
			state("spans", span, hasSpan)
			raw, hasNorm := c.lenNorm[r]
			state("lenNorm", fmt.Sprintf("some %d", raw), hasNorm)
			raw, hasAlias := c.lenAlias[r]
			state("lenAlias", fmt.Sprintf("some %d", raw), hasAlias)
			k, hasConst := c.consts[r]
			state("consts", fmt.Sprintf("some %d", k), hasConst)
			e, hasRegion := c.regions[r]
			region := ""
			if hasRegion {
				region = "some " + renderRegion(e)
			}
			state("regions", region, hasRegion)
			if moved || c.rawDead[r] {
				require(tc.name, fmt.Sprintf("example : %s.rawDead.contains %d = %v := by decide", after, r, c.rawDead[r]))
			}
		}
	}
	if len(missing) != 0 {
		t.Fatalf("%d fact(s) not stated in spec/lean/Oak/RiscVSpanAlias.lean — update the Lean file or the move rule:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}
