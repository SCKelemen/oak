package borrowchecker

import "testing"

// Decision tables for the owner-state procedures, mirroring the theorems of
// Oak.BorrowStateRefinement: view admission fails only under a writer; the
// span core admits only from Free; recompute maps live-borrow facts to the
// unique represented state, flagging the impossible combination.
func TestBorrowStateDecisionProcedures(t *testing.T) {
	if !admitViewBorrow(Free) || !admitViewBorrow(SharedRead) || admitViewBorrow(UniqueWrite) {
		t.Fatal("admitViewBorrow decision table diverged from Oak.BorrowStateRefinement.admitView")
	}
	if !admitSpanBorrowCore(Free) || admitSpanBorrowCore(SharedRead) || admitSpanBorrowCore(UniqueWrite) {
		t.Fatal("admitSpanBorrowCore decision table diverged from Oak.BorrowStateRefinement.admitSpanCore")
	}

	cases := []struct {
		views, spans bool
		want         BorrowState
		ok           bool
	}{
		{false, false, Free, true},
		{true, false, SharedRead, true},
		{false, true, UniqueWrite, true},
		{true, true, Free, false},
	}
	for _, tc := range cases {
		state, ok := ownerStateFor(tc.views, tc.spans)
		if ok != tc.ok || (ok && state != tc.want) {
			t.Fatalf("ownerStateFor(%v, %v) = (%v, %v), want (%v, %v)",
				tc.views, tc.spans, state, ok, tc.want, tc.ok)
		}
	}
}
