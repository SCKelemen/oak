package resourceflow

import "testing"

func TestJoinAuthorityLaws(t *testing.T) {
	values := []Authority{AuthorityLive, AuthorityConsumed, AuthorityMaybeConsumed}
	for _, a := range values {
		if got := JoinAuthority(a, a); got != a {
			t.Fatalf("idempotence: join(%v, %v) = %v", a, a, got)
		}
		for _, b := range values {
			if left, right := JoinAuthority(a, b), JoinAuthority(b, a); left != right {
				t.Fatalf("commutativity: join(%v, %v)=%v, reverse=%v", a, b, left, right)
			}
			for _, c := range values {
				left := JoinAuthority(JoinAuthority(a, b), c)
				right := JoinAuthority(a, JoinAuthority(b, c))
				if left != right {
					t.Fatalf("associativity failed for %v, %v, %v: %v != %v", a, b, c, left, right)
				}
			}
		}
	}
}

func TestBranchCloneDoesNotMutateIncomingState(t *testing.T) {
	incoming := New()
	if !incoming.Register("socket", nil) {
		t.Fatal("registration failed")
	}
	branch := incoming.Clone()
	if !branch.Consume("socket", nil) {
		t.Fatal("branch consume failed")
	}
	if !incoming.CanUse("socket") {
		t.Fatal("mutating a branch must not mutate its predecessor")
	}
}

func TestJoinLiveAndConsumedBecomesMaybeConsumed(t *testing.T) {
	incoming := New()
	incoming.Register("socket", nil)
	live := incoming.Clone()
	consumed := incoming.Clone()
	consumed.Consume("socket", nil)

	joined := Join(live, consumed)
	got, ok := joined.AuthorityOf("socket")
	if !ok || got != AuthorityMaybeConsumed {
		t.Fatalf("expected maybe-consumed join, got %v, exists=%v", got, ok)
	}
	if joined.CanUse("socket") {
		t.Fatal("conditional authority must not be usable after a join")
	}
	if joined.Consume("socket", nil) {
		t.Fatal("conditional authority must not be consumable again")
	}
}

func TestJoinConsumedOnAllPathsIsDefinitelyConsumed(t *testing.T) {
	incoming := New()
	incoming.Register("socket", nil)
	left := incoming.Clone()
	right := incoming.Clone()
	left.Consume("socket", nil)
	right.Consume("socket", nil)

	joined := Join(left, right)
	got, ok := joined.AuthorityOf("socket")
	if !ok || got != AuthorityConsumed {
		t.Fatalf("expected definitely consumed, got %v, exists=%v", got, ok)
	}
}

func TestAliasClassSharesJoinedAuthority(t *testing.T) {
	incoming := New()
	incoming.Register("buffer", nil)
	if !incoming.Alias("payload", "buffer", nil) {
		t.Fatal("alias failed")
	}
	left := incoming.Clone()
	right := incoming.Clone()
	left.Consume("payload", nil)

	joined := Join(left, right)
	for _, name := range []string{"buffer", "payload"} {
		got, ok := joined.AuthorityOf(name)
		if !ok || got != AuthorityMaybeConsumed {
			t.Fatalf("%s: expected maybe-consumed alias class, got %v, exists=%v", name, got, ok)
		}
	}
}

func TestBranchLocalNamesDoNotEscapeJoin(t *testing.T) {
	incoming := New()
	incoming.Register("root", nil)
	left := incoming.Clone()
	right := incoming.Clone()
	left.Register("leftOnly", nil)

	joined := Join(left, right)
	if joined.Registered("leftOnly") {
		t.Fatal("name introduced on one branch must not escape the join")
	}
	if !joined.CanUse("root") {
		t.Fatal("common live authority should survive branch-local declarations")
	}
}
