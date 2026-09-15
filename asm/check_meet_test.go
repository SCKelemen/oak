package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"
)

// The meet of index facts at a label (docs/spec/94-assembler.md §7): a
// bound register still holding its initial constant makes the entry's
// compare an immediate one (`wI < 512`), while the back edge compares the
// index against the register (`wI < wB`); the register form holds on both
// paths when the constant side's register holds at least the constant.
func TestMeetIdxReconcilesConstantAndRegisterBounds(t *testing.T) {
	entry := newGuardState()
	entry.idx[14] = idxFact{boundReg: -1, bound: 512}
	entry.consts[23] = 512
	back := newGuardState()
	back.idx[14] = idxFact{boundReg: 23}
	want := idxFact{boundReg: 23}
	if got := meetIdx(entry, back)[14]; got != want {
		t.Errorf("meet(entry, back) = %+v, want %+v", got, want)
	}
	if got := meetIdx(back, entry)[14]; got != want {
		t.Errorf("meet(back, entry) = %+v, want %+v", got, want)
	}
	// The register's constant below the bound proves nothing; a slack fact
	// is not reconciled; an identical fact survives as before.
	entry.consts[23] = 511
	if _, kept := meetIdx(entry, back)[14]; kept {
		t.Error("a register holding less than the constant bound must not carry the register form")
	}
	entry.consts[23] = 512
	back.idx[14] = idxFact{boundReg: 23, bound: 4, slack: true}
	if _, kept := meetIdx(entry, back)[14]; kept {
		t.Error("a slack fact is not reconciled with a constant bound")
	}
	back.idx[14] = idxFact{boundReg: -1, bound: 512}
	if got := meetIdx(entry, back)[14]; got != back.idx[14] {
		t.Errorf("identical facts survive the meet, got %+v", got)
	}
}

// The production decision table is stated verbatim as executable examples in
// Oak.CheckerMeetRefinement. Lean proves universally that every fact the
// decision retains holds on both predecessors; this test keeps the Go branch
// conditions and result shapes pinned to that model.
func TestMeetIdxMatchesLeanRefinement(t *testing.T) {
	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "CheckerMeetRefinement.lean"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(lean)
	imm := func(bound int64) idxFact { return idxFact{boundReg: -1, bound: bound} }
	reg := func(r int) idxFact { return idxFact{boundReg: r} }
	state := func(fact idxFact, constants map[int]int64) *guardState {
		st := newGuardState()
		st.idx[14] = fact
		for r, value := range constants {
			st.consts[r] = value
		}
		return st
	}
	type meetCase struct {
		name string
		a    *guardState
		b    *guardState
	}
	cases := []meetCase{
		{"constant entry and register back edge", state(imm(512), map[int]int64{23: 512}), state(reg(23), nil)},
		{"register back edge and constant entry", state(reg(23), nil), state(imm(512), map[int]int64{23: 512})},
		{"bound register constant is too small", state(imm(512), map[int]int64{23: 511}), state(reg(23), nil)},
		{"slack register fact", state(imm(512), map[int]int64{23: 512}), state(idxFact{boundReg: 23, bound: 4, slack: true}, nil)},
		{"identical immediate facts", state(imm(512), map[int]int64{23: 512}), state(imm(512), nil)},
	}
	var missing []string
	for _, tc := range cases {
		result := "none"
		if got, kept := meetIdx(tc.a, tc.b)[14]; kept {
			result = "some " + renderIdx(got)
		}
		line := fmt.Sprintf("example : meetFact %s %s %s %s = %s := by decide",
			renderConstMap(tc.a.consts), renderIdx(tc.a.idx[14]),
			renderConstMap(tc.b.consts), renderIdx(tc.b.idx[14]), result)
		if !strings.Contains(text, line) {
			missing = append(missing, tc.name+":\n  "+line)
		}
	}
	if len(missing) != 0 {
		t.Fatalf("%d meet decision(s) not stated in CheckerMeetRefinement.lean:\n%s",
			len(missing), strings.Join(missing, "\n"))
	}
}

func renderConstMap(constants map[int]int64) string {
	regs := make([]int, 0, len(constants))
	for reg := range constants {
		regs = append(regs, reg)
	}
	sort.Ints(regs)
	parts := make([]string, 0, len(regs))
	for _, reg := range regs {
		parts = append(parts, fmt.Sprintf("(%d, %d)", reg, constants[reg]))
	}
	return "[" + strings.Join(parts, ", ") + "]"
}
