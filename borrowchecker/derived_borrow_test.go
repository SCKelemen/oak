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
	if parent.suspendedBy != "child" {
		t.Fatalf("parent suspendedBy = %q, want child", parent.suspendedBy)
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
	if parent.suspendedBy != "" {
		t.Fatalf("parent remained suspended by %q after child scope ended", parent.suspendedBy)
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

	if bc.activeBorrows["child"].suspendedBy != "grandchild" {
		t.Fatal("child should be suspended by grandchild")
	}
	if bc.activeBorrows["parent"].suspendedBy != "child" {
		t.Fatal("parent should remain suspended by child")
	}

	bc.dropBorrowsInCurrentBlock()
	if bc.activeBorrows["child"].suspendedBy != "" {
		t.Fatal("dropping grandchild should restore child")
	}
	if bc.activeBorrows["parent"].suspendedBy != "child" {
		t.Fatal("restoring child must not restore parent early")
	}

	bc.currentBlockDepth = 1
	bc.dropBorrowsInCurrentBlock()
	if bc.activeBorrows["parent"].suspendedBy != "" {
		t.Fatal("dropping child should restore parent")
	}
}

func TestDerivedViewDoesNotSuspendParentView(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = Free
	bc.createViewBorrowWithRegion("buf", "parent", &Region{Offset: 0, Length: 16}, nil)
	bc.currentBlockDepth = 1
	bc.createSubsliceWithRegion("parent", "child", &Region{Offset: 4, Length: 4}, nil)
	if bc.activeBorrows["parent"].suspendedBy != "" {
		t.Fatal("read-only derivation must not suspend its parent view")
	}
}
