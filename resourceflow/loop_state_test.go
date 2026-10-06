package resourceflow

import "testing"

func TestSameStateTracksJoinInputs(t *testing.T) {
	base := New()
	base.Register("owner", nil)
	base.Alias("alias", "owner", nil)
	if !base.SameState(base.Clone()) {
		t.Fatal("clone changed semantic state")
	}
	consumed := base.Clone()
	consumed.Consume("alias", nil)
	if base.SameState(consumed) {
		t.Fatal("consumption must change the loop state")
	}
	unknown := base.Clone()
	unknown.Forget("alias")
	if base.SameState(unknown) {
		t.Fatal("lost provenance must change the loop state")
	}
	fresh := base.Clone()
	fresh.RebindFresh("alias", nil)
	if base.SameState(fresh) {
		t.Fatal("fresh rebinding must change alias identity")
	}
	garbage := base.Clone()
	garbage.Register("temporary", nil)
	garbage.Forget("temporary")
	if !base.SameState(garbage) {
		t.Fatal("unreachable classes and allocation cursors are not loop facts")
	}
}

func TestLoopJoinNeedsMoreThanTwoPasses(t *testing.T) {
	head := New()
	head.Register("owner", nil)
	head.Alias("c", "owner", nil)
	head.Alias("b", "c", nil)
	head.Alias("a", "b", nil)
	passes := 0
	for {
		body := head.Clone()
		if !body.Rebind("a", "b", nil) {
			body.Forget("a")
		}
		if !body.Rebind("b", "c", nil) {
			body.Forget("b")
		}
		body.Forget("c")
		next := Join(head, body)
		passes++
		if next.SameState(head) {
			head = next
			break
		}
		head = next
		if passes > 8 {
			t.Fatal("finite descending alias domain did not converge")
		}
	}
	if passes <= 2 || head.Registered("a") || !head.CanUse("owner") {
		t.Fatalf("passes=%d a-known=%v owner-live=%v", passes, head.Registered("a"), head.CanUse("owner"))
	}
}
