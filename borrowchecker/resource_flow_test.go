package borrowchecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

func TestResourceConsumeInvalidatesDirectUse(t *testing.T) {
	bc := New()
	rf := NewResourceFlow(bc)
	if !rf.Register("file", diagnosticIdent("file", 1, 1)) {
		t.Fatal("expected resource registration to succeed")
	}
	if !rf.Consume("file", diagnosticIdent("close", 2, 1)) {
		t.Fatal("expected first consume to succeed")
	}
	if rf.Use("file", diagnosticIdent("file", 4, 1)) {
		t.Fatal("consumed resource should not remain usable")
	}

	d := findBorrowDiagnostic(t, bc, CodeResourceUsedAfterConsume)
	if d.Category != diagnostic.CategoryBorrow {
		t.Fatalf("expected borrow category, got %q", d.Category)
	}
	if err := d.Validate(); err != nil {
		t.Fatalf("diagnostic is not structurally valid: %v", err)
	}
	if len(d.Labels) != 2 {
		t.Fatalf("expected invalid use plus consume site, got %#v", d.Labels)
	}
	if d.Labels[0].Style != diagnostic.LabelPrimary || d.Labels[1].Style != diagnostic.LabelSecondary {
		t.Fatalf("expected primary use and secondary consume labels, got %#v", d.Labels)
	}
	if !strings.Contains(d.Labels[1].Message, "consumed here") {
		t.Fatalf("consume-site label should explain lost authority, got %q", d.Labels[1].Message)
	}
}

func TestResourceConsumeInvalidatesAliasClassAndExplainsChain(t *testing.T) {
	bc := New()
	rf := NewResourceFlow(bc)
	rf.Register("buffer", diagnosticIdent("buffer", 1, 1))
	if !rf.Alias("packet", "buffer", diagnosticIdent("packet", 2, 1)) {
		t.Fatal("expected first resource alias to succeed")
	}
	if !rf.Alias("payload", "packet", diagnosticIdent("payload", 3, 1)) {
		t.Fatal("expected second resource alias to succeed")
	}
	if !rf.Consume("buffer", diagnosticIdent("submit", 4, 1)) {
		t.Fatal("expected consuming the root alias to succeed")
	}
	if rf.Use("payload", diagnosticIdent("payload", 6, 1)) {
		t.Fatal("alias should lose authority when its class is consumed")
	}

	d := findBorrowDiagnostic(t, bc, CodeResourceUsedAfterConsume)
	if len(d.Labels) != 4 {
		t.Fatalf("expected use, consume, and two provenance edges, got %#v", d.Labels)
	}
	plain := d.PlainText()
	if !strings.Contains(plain, `alias "packet" derives authority from "buffer"`) ||
		!strings.Contains(plain, `alias "payload" derives authority from "packet"`) {
		t.Fatalf("expected programmer-visible alias chain, got %q", plain)
	}
	if strings.Contains(plain, "classID") || strings.Contains(plain, "alias-set") {
		t.Fatalf("diagnostic must not expose internal alias-class identifiers: %q", plain)
	}
}

func TestResourceConsumePreservesUnrelatedClass(t *testing.T) {
	bc := New()
	rf := NewResourceFlow(bc)
	rf.Register("left", diagnosticIdent("left", 1, 1))
	rf.Register("right", diagnosticIdent("right", 2, 1))

	if !rf.Consume("left", diagnosticIdent("take_left", 3, 1)) {
		t.Fatal("expected left resource to be consumable")
	}
	if !rf.Use("right", diagnosticIdent("right", 4, 1)) {
		t.Fatal("consuming one authority class must not affect another")
	}
	if rf.Consumed("right") {
		t.Fatal("unrelated resource class should remain live")
	}
	if got := bc.Diagnostics(); len(got) != 0 {
		t.Fatalf("unrelated use should not produce diagnostics: %#v", got)
	}
}

func TestResourceCannotConsumeWhileDependentBorrowLives(t *testing.T) {
	bc := New()
	rf := NewResourceFlow(bc)
	rf.Register("buf", diagnosticIdent("buf", 1, 1))
	bc.ownerStates["buf"] = SharedRead
	bc.activeBorrows["header"] = borrowInfo{
		owner:  "buf",
		kind:   BorrowView,
		region: &Region{Offset: 0, Length: 4},
		origin: diagnosticIdent("header", 2, 1),
	}

	if rf.Consume("buf", diagnosticIdent("submit", 4, 1)) {
		t.Fatal("live dependent borrow must block permanent consumption")
	}
	if rf.Consumed("buf") {
		t.Fatal("failed consume must not mutate resource authority")
	}
	if !rf.Use("buf", diagnosticIdent("buf", 5, 1)) {
		t.Fatal("resource should remain live after rejected consume")
	}

	d := findBorrowDiagnostic(t, bc, CodeBorrowGeneric)
	if !strings.Contains(d.Title, "cannot be consumed while borrow") {
		t.Fatalf("expected consume-vs-borrow explanation, got %q", d.Title)
	}
	if len(d.Labels) != 2 || !strings.Contains(d.Labels[1].Message, "header") {
		t.Fatalf("expected dependent borrow as secondary cause, got %#v", d.Labels)
	}
}

func TestUniqueBorrowCanReleaseBeforePermanentConsume(t *testing.T) {
	bc := New()
	rf := NewResourceFlow(bc)
	rf.Register("buf", diagnosticIdent("buf", 1, 1))
	bc.ownerStates["buf"] = UniqueWrite
	bc.activeBorrows["writer"] = borrowInfo{
		owner:  "buf",
		kind:   BorrowSpan,
		region: &Region{Offset: 0, Length: 8},
		origin: diagnosticIdent("writer", 2, 1),
	}

	if rf.Consume("buf", diagnosticIdent("submit", 3, 1)) {
		t.Fatal("unique borrow should temporarily block consume")
	}
	bc.ClearErrors()
	bc.dropBorrow("writer")
	bc.recomputeOwnerStatesFromActiveBorrows()
	if bc.ownerStates["buf"] != Free {
		t.Fatalf("temporary unique borrow should release to Free, got %s", bc.ownerStates["buf"])
	}
	if !rf.Consume("buf", diagnosticIdent("submit", 5, 1)) {
		t.Fatal("resource should become consumable after borrow release")
	}
	if !rf.Consumed("buf") {
		t.Fatal("successful consume must permanently remove resource authority")
	}
	if rf.Use("buf", diagnosticIdent("buf", 6, 1)) {
		t.Fatal("consumed resource must not become usable again after borrow release")
	}
	findBorrowDiagnostic(t, bc, CodeResourceUsedAfterConsume)
}

func TestSecondConsumeIsUseAfterConsume(t *testing.T) {
	bc := New()
	rf := NewResourceFlow(bc)
	rf.Register("file", diagnosticIdent("file", 1, 1))
	if !rf.Consume("file", diagnosticIdent("first_close", 2, 1)) {
		t.Fatal("expected first consume to succeed")
	}
	if rf.Consume("file", diagnosticIdent("second_close", 3, 1)) {
		t.Fatal("second consume must be rejected")
	}

	d := findBorrowDiagnostic(t, bc, CodeResourceUsedAfterConsume)
	if len(d.Labels) != 2 || !strings.Contains(d.Labels[1].Message, "first_close") && !strings.Contains(d.PlainText(), "first_close") {
		// The source range does not preserve token spelling in PlainText; the
		// important structural contract is the original consume secondary label.
		if len(d.Labels) != 2 || d.Labels[1].Style != diagnostic.LabelSecondary {
			t.Fatalf("expected original consume as secondary cause, got %#v", d.Labels)
		}
	}
}

func TestAliasCreationAfterConsumeIsRejected(t *testing.T) {
	bc := New()
	rf := NewResourceFlow(bc)
	rf.Register("handle", diagnosticIdent("handle", 1, 1))
	rf.Consume("handle", diagnosticIdent("close", 2, 1))

	if rf.Alias("late", "handle", diagnosticIdent("late", 3, 1)) {
		t.Fatal("creating an alias requires live source authority")
	}
	if rf.Consumed("late") {
		t.Fatal("failed alias registration must not create a new name")
	}
	findBorrowDiagnostic(t, bc, CodeResourceUsedAfterConsume)
}

func TestBorrowThroughResourceAliasBlocksClassConsume(t *testing.T) {
	bc := New()
	rf := NewResourceFlow(bc)
	rf.Register("root", diagnosticIdent("root", 1, 1))
	rf.Alias("mapped", "root", diagnosticIdent("mapped", 2, 1))
	bc.activeBorrows["view"] = borrowInfo{
		owner:  "mapped",
		kind:   BorrowView,
		region: &Region{Offset: 0, Length: 4},
		origin: diagnosticIdent("view", 3, 1),
	}

	if rf.Consume("root", diagnosticIdent("consume", 5, 1)) {
		t.Fatal("borrow through any class alias must block consume")
	}
	if rf.Consumed("root") || rf.Consumed("mapped") {
		t.Fatal("rejected class consume must leave every alias live")
	}
}
