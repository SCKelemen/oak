package asm

import "testing"

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
