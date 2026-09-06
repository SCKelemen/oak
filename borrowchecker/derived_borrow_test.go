package borrowchecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func TestDeriveRegionUsesAbsoluteOwnerCoordinates(t *testing.T) {
	got, ok := deriveRegion(&Region{Offset: 10, Length: 8}, &Region{Offset: 2, Length: 3})
	if !ok || got.Offset != 12 || got.Length != 3 {
		t.Fatalf("deriveRegion = %#v, %v; want [12..15)", got, ok)
	}
}

func TestDeriveRegionRejectsOutsideAndOverflow(t *testing.T) {
	cases := []struct {
		name     string
		parent   *Region
		relative *Region
	}{
		{"outside", &Region{Offset: 10, Length: 8}, &Region{Offset: 7, Length: 2}},
		{"negative", &Region{Offset: 0, Length: 8}, &Region{Offset: -1, Length: 1}},
		{"parent overflow", &Region{Offset: maxRegionInt64, Length: 1}, &Region{Offset: 0, Length: 0}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if got, ok := deriveRegion(tc.parent, tc.relative); ok || got != nil {
				t.Fatalf("deriveRegion = %#v, %v; want failure", got, ok)
			}
		})
	}
}

func TestExtractSliceRegionRejectsKnownOutOfBounds(t *testing.T) {
	bc := New()
	slice := &ast.SliceExpression{
		Low:  &ast.IntegerLiteral{Value: 0},
		High: &ast.IntegerLiteral{Value: 17},
	}
	if region, ok := bc.extractSliceRegion(slice, 16); ok || region != nil {
		t.Fatalf("extractSliceRegion = %#v, %v; want out-of-bounds rejection", region, ok)
	}
}

func TestWritableReborrowSuspendsAndRestoresParent(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = Free
	bc.createSpanBorrowWithRegion("buf", "parent", &Region{Offset: 0, Length: 16}, nil)

	bc.currentBlockDepth = 1
	bc.createSubsliceWithRegion("parent", "child", &Region{Offset: 4, Length: 4}, nil)
	parent := bc.activeBorrows["parent"]
	if len(parent.reborrows) != 1 || parent.reborrows[0] != "child" {
		t.Fatalf("parent reborrows = %#v, want [child]", parent.reborrows)
	}

	bc.checkIdentifierUse(&ast.Identifier{Value: "parent"}, "parent", nil, false)
	diagnostics := bc.Diagnostics()
	if len(diagnostics) == 0 || diagnostics[len(diagnostics)-1].Code != string(CodeBorrowSuspended) {
		t.Fatalf("expected %s diagnostic, got %#v", CodeBorrowSuspended, diagnostics)
	}

	bc.dropBorrowsInCurrentBlock()
	parent, ok := bc.activeBorrows["parent"]
	if !ok {
		t.Fatal("outer parent borrow was dropped with inner child")
	}
	if len(parent.reborrows) != 0 {
		t.Fatalf("parent remained suspended by %#v after child scope ended", parent.reborrows)
	}
}

func TestNestedWritableReborrowRestoresOneLevelAtATime(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = Free
	bc.createSpanBorrowWithRegion("buf", "parent", &Region{Offset: 0, Length: 16}, nil)

	bc.currentBlockDepth = 1
	bc.createSubsliceWithRegion("parent", "child", &Region{Offset: 4, Length: 8}, nil)
	bc.currentBlockDepth = 2
	bc.createSubsliceWithRegion("child", "grandchild", &Region{Offset: 6, Length: 2}, nil)

	if got := bc.activeBorrows["child"].reborrows; len(got) != 1 || got[0] != "grandchild" {
		t.Fatal("child should be suspended by grandchild")
	}
	if got := bc.activeBorrows["parent"].reborrows; len(got) != 1 || got[0] != "child" {
		t.Fatal("parent should remain suspended by child")
	}

	bc.dropBorrowsInCurrentBlock()
	if len(bc.activeBorrows["child"].reborrows) != 0 {
		t.Fatal("dropping grandchild should restore child")
	}
	if got := bc.activeBorrows["parent"].reborrows; len(got) != 1 || got[0] != "child" {
		t.Fatal("restoring child must not restore parent early")
	}

	bc.currentBlockDepth = 1
	bc.dropBorrowsInCurrentBlock()
	if len(bc.activeBorrows["parent"].reborrows) != 0 {
		t.Fatal("dropping child should restore parent")
	}
}

func TestDerivedViewDoesNotSuspendParentView(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = Free
	bc.createViewBorrowWithRegion("buf", "parent", &Region{Offset: 0, Length: 16}, nil)
	bc.currentBlockDepth = 1
	bc.createSubsliceWithRegion("parent", "child", &Region{Offset: 4, Length: 4}, nil)
	if len(bc.activeBorrows["parent"].reborrows) != 0 {
		t.Fatal("read-only derivation must not suspend its parent view")
	}
}

func TestFrontEndDerivedViewKeepsAbsoluteOwnerRegion(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest("buf: [16]u8\nv1: []u8 = buf[4:12]\nv2: []u8 = v1[2:4]")
	if program == nil {
		t.Fatal("failed to parse derived-view program")
	}
	bc.CheckProgram(program, tc.Env())
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("unexpected borrow diagnostics: %#v", bc.Diagnostics())
	}
	v2, ok := bc.activeBorrows["v2"]
	if !ok || v2.region == nil {
		t.Fatalf("derived view missing exact region: %#v", v2)
	}
	if v2.region.Offset != 6 || v2.region.Length != 2 {
		t.Fatalf("derived view region = %#v, want [6..8)", v2.region)
	}
	if v2.parent != "v1" || v2.owner != "buf" {
		t.Fatalf("derived view provenance = parent %q owner %q", v2.parent, v2.owner)
	}
}

func TestFrontEndSpanSliceSuspendsParentWithPreciseRegion(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest("buf: [16]u8\nparent: [*]u8 = span(&buf)\nchild: [*]u8 = parent[4:8]")
	if program == nil {
		t.Fatal("failed to parse writable-reborrow program")
	}
	bc.CheckProgram(program, tc.Env())
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("unexpected borrow diagnostics: %#v", bc.Diagnostics())
	}
	parent, ok := bc.activeBorrows["parent"]
	if !ok || len(parent.reborrows) != 1 || parent.reborrows[0] != "child" {
		t.Fatalf("parent reborrow state = %#v, want suspended by child", parent)
	}
	child, ok := bc.activeBorrows["child"]
	if !ok || child.region == nil {
		t.Fatalf("child missing exact region: %#v", child)
	}
	if child.region.Offset != 4 || child.region.Length != 4 {
		t.Fatalf("child region = %#v, want [4..8)", child.region)
	}
	if child.parent != "parent" || child.owner != "buf" {
		t.Fatalf("child provenance = parent %q owner %q", child.parent, child.owner)
	}
}

func countDiagnosticsWithCode(bc *BorrowChecker, code string) int {
	count := 0
	for _, d := range bc.Diagnostics() {
		if d.Code == code {
			count++
		}
	}
	return count
}

func TestDisjointWritableReborrowsCoexist(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = Free
	bc.createSpanBorrowWithRegion("buf", "parent", &Region{Offset: 0, Length: 16}, nil)

	bc.currentBlockDepth = 1
	bc.createSubsliceWithRegion("parent", "left", &Region{Offset: 0, Length: 8}, nil)
	bc.createSubsliceWithRegion("parent", "right", &Region{Offset: 8, Length: 8}, nil)
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("disjoint sibling reborrows must be accepted, got %#v", bc.Diagnostics())
	}
	parent := bc.activeBorrows["parent"]
	if len(parent.reborrows) != 2 || parent.reborrows[0] != "left" || parent.reborrows[1] != "right" {
		t.Fatalf("parent reborrows = %#v, want [left right]", parent.reborrows)
	}

	// Direct use of the suspended parent still reports exactly one diagnostic.
	bc.checkIdentifierUse(&ast.Identifier{Value: "parent"}, "parent", nil, false)
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowSuspended)); got != 1 {
		t.Fatalf("suspended-parent use produced %d %s diagnostics, want exactly 1", got, CodeBorrowSuspended)
	}

	bc.dropBorrowsInCurrentBlock()
	if len(bc.activeBorrows["parent"].reborrows) != 0 {
		t.Fatalf("parent remained suspended by %#v after both children dropped", bc.activeBorrows["parent"].reborrows)
	}
}

func TestOverlappingWritableReborrowRejected(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = Free
	bc.createSpanBorrowWithRegion("buf", "parent", &Region{Offset: 0, Length: 16}, nil)

	bc.currentBlockDepth = 1
	bc.createSubsliceWithRegion("parent", "left", &Region{Offset: 0, Length: 8}, nil)
	bc.createSubsliceWithRegion("parent", "mid", &Region{Offset: 4, Length: 8}, nil)

	if got := countDiagnosticsWithCode(bc, string(CodeReborrowOverlap)); got != 1 {
		t.Fatalf("overlapping sibling produced %d %s diagnostics, want exactly 1", got, CodeReborrowOverlap)
	}
	if _, exists := bc.activeBorrows["mid"]; exists {
		t.Fatal("overlapping reborrow must not be created")
	}
	if got := bc.activeBorrows["parent"].reborrows; len(got) != 1 || got[0] != "left" {
		t.Fatalf("parent reborrows = %#v, want [left]", got)
	}
}

func TestUnknownRegionReborrowAdmitsNoSiblings(t *testing.T) {
	// An unknown-region child fails closed in both directions: it cannot join
	// live known-region siblings, and no sibling can join it.
	bc := New()
	bc.ownerStates["buf"] = Free
	bc.createSpanBorrowWithRegion("buf", "parent", &Region{Offset: 0, Length: 16}, nil)
	bc.currentBlockDepth = 1
	bc.createSubsliceWithRegion("parent", "unknown", nil, nil)
	bc.createSubsliceWithRegion("parent", "known", &Region{Offset: 8, Length: 8}, nil)
	if got := countDiagnosticsWithCode(bc, string(CodeReborrowOverlap)); got != 1 {
		t.Fatalf("sibling of unknown-region reborrow produced %d %s diagnostics, want exactly 1", got, CodeReborrowOverlap)
	}

	bc = New()
	bc.ownerStates["buf"] = Free
	bc.createSpanBorrowWithRegion("buf", "parent", &Region{Offset: 0, Length: 16}, nil)
	bc.currentBlockDepth = 1
	bc.createSubsliceWithRegion("parent", "known", &Region{Offset: 8, Length: 8}, nil)
	bc.createSubsliceWithRegion("parent", "unknown", nil, nil)
	if got := countDiagnosticsWithCode(bc, string(CodeReborrowOverlap)); got != 1 {
		t.Fatalf("unknown-region sibling produced %d %s diagnostics, want exactly 1", got, CodeReborrowOverlap)
	}
}

func TestFrontEndDisjointSpanSplit(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest(
		"buf: [16]u8\nparent: [*]u8 = span(&buf)\nleft: [*]u8 = parent[0:8]\nright: [*]u8 = parent[8:16]")
	if program == nil {
		t.Fatal("failed to parse disjoint-split program")
	}
	bc.CheckProgram(program, tc.Env())
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("disjoint span split must check cleanly, got %#v", bc.Diagnostics())
	}
	parent := bc.activeBorrows["parent"]
	if len(parent.reborrows) != 2 || parent.reborrows[0] != "left" || parent.reborrows[1] != "right" {
		t.Fatalf("parent reborrows = %#v, want [left right]", parent.reborrows)
	}
	left := bc.activeBorrows["left"]
	right := bc.activeBorrows["right"]
	if left.region == nil || right.region == nil {
		t.Fatalf("split children missing exact regions: %#v / %#v", left.region, right.region)
	}
	if bc.regionsOverlap(left.region, right.region) {
		t.Fatalf("split children regions overlap: %#v / %#v", left.region, right.region)
	}
}

func TestFrontEndOverlappingReborrowReportsExactlyOneDiagnostic(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest(
		"buf: [16]u8\nparent: [*]u8 = span(&buf)\nleft: [*]u8 = parent[0:8]\nmid: [*]u8 = parent[4:12]")
	if program == nil {
		t.Fatal("failed to parse overlapping-reborrow program")
	}
	bc.CheckProgram(program, tc.Env())
	if got := len(bc.Diagnostics()); got != 1 {
		t.Fatalf("overlapping reborrow produced %d diagnostics, want exactly 1: %#v", got, bc.Diagnostics())
	}
	if code := bc.Diagnostics()[0].Code; code != string(CodeReborrowOverlap) {
		t.Fatalf("overlapping reborrow diagnostic code = %s, want %s", code, CodeReborrowOverlap)
	}
}

func TestFrontEndSuspendedParentUseReportsExactlyOneDiagnostic(t *testing.T) {
	// Pins the invariant that a suspended parent's direct use is diagnosed by
	// exactly one traversal path, regardless of walk order.
	bc, program, tc := setupBorrowCheckerForTest(
		"buf: [16]u8\nparent: [*]u8 = span(&buf)\nchild: [*]u8 = parent[4:8]\nparent")
	if program == nil {
		t.Fatal("failed to parse suspended-parent-use program")
	}
	bc.CheckProgram(program, tc.Env())
	if got := len(bc.Diagnostics()); got != 1 {
		t.Fatalf("suspended-parent use produced %d diagnostics, want exactly 1: %#v", got, bc.Diagnostics())
	}
	if code := bc.Diagnostics()[0].Code; code != string(CodeBorrowSuspended) {
		t.Fatalf("suspended-parent use diagnostic code = %s, want %s", code, CodeBorrowSuspended)
	}
}
