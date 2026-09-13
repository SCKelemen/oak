package compiler

import (
	"strings"
	"testing"
)

// Fallible typestate transitions (docs/spec/112-protocols.md section 5a,
// rule 5; the dbs pilot's round-five item 10): a via callable may return
// `Result[Segment[To], Segment[From]]` — the handle in the target state on
// success, the same handle in the source state on failure. No keyword: the
// return type is the declaration, the consumed argument's authority flows
// into whichever arm is matched, and a failed step is a step that did not
// take (the machine stutters).
const fallibleTypestateProgram = `import(std)
Segment[S]: type = struct { id: u32, generation: u32 }

Custody: protocol = {
  resource Segment
  initial Fresh
  publish: Fresh -> Published via try_publish(consumed s)
  evict: Published -> Evicted via evict(consumed s)
}

try_publish: (s: Segment[Fresh]): Result[Segment[Published], Segment[Fresh]] =
  s.id == u32(0) ? { .Err(s) } | { .Ok(Segment { id: s.id, generation: s.generation + u32(1) }) }
evict: (s: Segment[Published]): Segment[Evicted] = Segment { id: s.id, generation: s.generation + u32(1) }

// try re-raises the source-state handle; the Ok payload is the target.
publish_then_evict: (s: Segment[Fresh]): Result[Segment[Evicted], Segment[Fresh]] {
  p: Segment[Published] = try try_publish(s)
  .Ok(evict(p))
}

main: (): i32 {
  fresh: Segment[Fresh] = Segment { id: u32(ID), generation: u32(0) }
  r: Result[Segment[Published], Segment[Fresh]] = try_publish(fresh)
  direct: i32 = r ? | .Ok(p) => { gone: Segment[Evicted] = evict(p); gone.generation == u32(2) ? 40 | 1 } | .Err(f) => { f.generation == u32(0) ? 50 | 2 }
  again: Segment[Fresh] = Segment { id: u32(ID), generation: u32(0) }
  chained: i32 = publish_then_evict(again) ? | .Ok(g) => { g.generation == u32(2) ? 2 | 3 } | .Err(f) => { f.id == u32(0) ? 3 | 4 }
  direct + chained
}
`

func TestE2ETypestateFallibleTransition(t *testing.T) {
	for _, arm := range []struct {
		name string
		id   string
		want int64
	}{{"success arm", "7", 42}, {"failure arm", "0", 53}} {
		t.Run(arm.name, func(t *testing.T) {
			program := strings.ReplaceAll(fallibleTypestateProgram, "ID", arm.id)
			if got := interpretChecked(t, program); got != arm.want {
				t.Fatalf("interpreter: %d, want %d", got, arm.want)
			}
			code, abnormal := buildAndRun(t, "typestate_fallible_"+arm.id, program)
			if abnormal || int64(code) != arm.want {
				t.Fatalf("compiled: exit %d abnormal %v, want %d", code, abnormal, arm.want)
			}
		})
	}
}

// What the types refuse: arms in the wrong states are a protocol shape
// error, the consumed handle is dead on both paths, and a later failure
// cannot re-raise a handle in a state the function's failure type does not
// name — the failure type has to say which state the resource is left in.
func TestE2ETypestateFallibleRejections(t *testing.T) {
	program := strings.ReplaceAll(fallibleTypestateProgram, "ID", "7")
	cases := map[string][2]string{
		"wrong arm states": {strings.Replace(program, "Result[Segment[Published], Segment[Fresh]] =\n", "Result[Segment[Fresh], Segment[Published]] =\n", 1),
			"a fallible transition returns Result[Segment[Published], Segment[Fresh]]"},
		"consumed handle reused": {strings.Replace(program, "  direct: i32 = r ?", "  reuse: u32 = fresh.id\n  direct: i32 = r ?", 1),
			`resource "fresh" cannot be used after its authority was consumed`},
		"second try re-raises the wrong state": {`import(std)
Segment[S]: type = struct { id: u32, generation: u32 }
Custody: protocol = {
  resource Segment
  initial Fresh
  publish: Fresh -> Published via try_publish(consumed s)
  offload: Published -> Offloaded via try_offload(consumed s)
}
try_publish: (s: Segment[Fresh]): Result[Segment[Published], Segment[Fresh]] = .Ok(Segment { id: s.id, generation: s.generation + u32(1) })
try_offload: (s: Segment[Published]): Result[Segment[Offloaded], Segment[Published]] = .Err(s)
both: (s: Segment[Fresh]): Result[Segment[Offloaded], Segment[Fresh]] {
  p: Segment[Published] = try try_publish(s)
  o: Segment[Offloaded] = try try_offload(p)
  .Ok(o)
}
main: (): i32 = 0
`, "variant Err payload: expected Segment_Fresh, got Segment_Published"},
	}
	for name, c := range cases {
		_, err := New().WithSource("fallible.oak", c[0]).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c[1]) {
			t.Fatalf("%s: %v", name, err)
		}
	}
}
