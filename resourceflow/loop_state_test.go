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

// A component's height is not the height of the whole environment. This
// abstract monotone transfer advances one independent component per pass;
// it checks the convergence predicate, not an Oak source-level exploit.
func TestLoopJoinProductStateConvergence(t *testing.T) {
	head := New()
	for _, name := range []string{"a", "b", "c"} {
		head.Register(name, nil)
	}
	passes := 0
	for {
		body := head.Clone()
		body.Consume("a", nil)
		if !head.CanUse("a") {
			body.Consume("b", nil)
		}
		if !head.CanUse("b") {
			body.Consume("c", nil)
		}
		next := Join(head, body)
		passes++
		if next.SameState(head) {
			head = next
			break
		}
		head = next
		if passes > 8 {
			t.Fatal("finite authority domain did not converge")
		}
	}
	if passes <= 2 || head.CanUse("c") {
		t.Fatalf("passes=%d c-live=%v", passes, head.CanUse("c"))
	}
}
