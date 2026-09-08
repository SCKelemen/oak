package compiler

import (
	"strings"
	"testing"
)

func TestE2ECausalFrontier(t *testing.T) {
	src := `
import(std)
main: (): i32 {
  left: [4]u64
  right: [4]u64
  merged: [4]u64
  short_frontier: [3]u64

  true ? {
    l: [*]u64 = span(&left)
    r: [*]u64 = span(&right)
    l[0] = u64(2)
    l[1] = u64(7)
    l[2] = u64(1)
    l[3] = u64(9)
    r[0] = u64(5)
    r[1] = u64(3)
    r[2] = u64(1)
    r[3] = u64(11)
  }

  true ? {
    m: [*]u64 = span(&merged)
    joined: Result[u32, CausalFrontierError] = causal_frontier_join_into(m, view(&left), view(&right))
    joined_ok: Bool = joined ? | .Ok(n) => n == u32(4) | .Err(e) => false
    assert(joined_ok)
    assert(m[0] == u64(5) && m[1] == u64(7) && m[2] == u64(1) && m[3] == u64(11))
  }

  left_le: Result[Bool, CausalFrontierError] = causal_frontier_le(view(&left), view(&merged))
  left_le_ok: Bool = left_le ? | .Ok(v) => v | .Err(e) => false
  assert(left_le_ok)

  covered: Result[Bool, CausalFrontierError] = causal_frontier_covers(view(&merged), u32(1), u64(6))
  covered_ok: Bool = covered ? | .Ok(v) => v | .Err(e) => false
  assert(covered_ok)
  not_covered: Result[Bool, CausalFrontierError] = causal_frontier_covers(view(&merged), u32(1), u64(8))
  not_covered_ok: Bool = not_covered ? | .Ok(v) => !v | .Err(e) => false
  assert(not_covered_ok)

  true ? {
    m: [*]u64 = span(&merged)
    observed: Result[Bool, CausalFrontierError] = causal_frontier_observe(m, u32(1), u64(12))
    observed_ok: Bool = observed ? | .Ok(v) => v | .Err(e) => false
    assert(observed_ok)
    assert(m[1] == u64(12))
    duplicate: Result[Bool, CausalFrontierError] = causal_frontier_observe(m, u32(1), u64(10))
    duplicate_ok: Bool = duplicate ? | .Ok(v) => !v | .Err(e) => false
    assert(duplicate_ok)
    assert(m[1] == u64(12))
  }

  // Errors are checked before mutation.
  true ? {
    s: [*]u64 = span(&short_frontier)
    s[0] = u64(99)
    mismatch: Result[u32, CausalFrontierError] = causal_frontier_join_into(s, view(&left), view(&right))
    mismatch_ok: Bool = mismatch ? | .Ok(n) => false | .Err(e) => true
    assert(mismatch_ok && s[0] == u64(99))
  }

  before: u64 = merged[0]
  true ? {
    m: [*]u64 = span(&merged)
    bad_actor: Result[Bool, CausalFrontierError] = causal_frontier_observe(m, u32(4), u64(100))
    actor_ok: Bool = bad_actor ? | .Ok(v) => false | .Err(e) => true
    assert(actor_ok && m[0] == before)
  }
  42
}
`

	output, err := New().WithSource("causal_frontier.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "free(", "OAK_UNSUPPORTED"} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("causal frontier generated hidden runtime dependency %q:\n%s", forbidden, output)
		}
	}
	for _, want := range []string{"causal_frontier_join_into", "causal_frontier_le", "causal_frontier_covers", "causal_frontier_observe"} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks frontier operation %q:\n%s", want, output)
		}
	}

	code, abnormal := buildAndRun(t, "causalfrontier", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d, abnormal=%v), want 42", code, abnormal)
	}
}
