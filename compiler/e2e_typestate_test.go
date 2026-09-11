package compiler

import (
	"strings"
	"testing"
)

// Typestate-indexed handles (docs/spec/112-protocols.md section 5a): a
// resource that is a record template with one type parameter carries its
// protocol state in the type. Each state projects a marker type, via
// callables take Segment[From] and return Segment[To], a transition's
// result is the same resource in its next state, and a handle may be
// constructed only in the initial state or inside the transition into it.
// Everything else is ordinary generics: an illegal transition is a type
// error, so the legality trap in custody_next is unreachable.
const typestateProgram = `
Segment[S]: type = struct { id: u32, generation: u32 }

Custody: protocol = {
  resource Segment
  initial Fresh
  publish: Fresh -> Published via publish(consumed s)
  offload: Published -> Offloaded via offload(consumed s)
  evict: Offloaded -> Evicted via evict(consumed s)
}

publish: (s: Segment[Fresh]): Segment[Published] = Segment { id: s.id, generation: s.generation + u32(1) }
offload: (s: Segment[Published]): Segment[Offloaded] = Segment { id: s.id, generation: s.generation + u32(1) }
evict: (s: Segment[Offloaded]): Segment[Evicted] = Segment { id: s.id, generation: s.generation + u32(1) }

main: (): i32 {
  fresh: Segment[Fresh] = Segment { id: u32(7), generation: u32(0) }
  gone: Segment[Evicted] = evict(offload(publish(fresh)))
  gone.generation == u32(3) && gone.id == u32(7) ? { 42 } | { 1 }
}
`

func TestE2ETypestateCompiled(t *testing.T) {
	// size_of is compile-time layout introspection: the two states share
	// one representation.
	sized := strings.Replace(typestateProgram, "  gone.generation == u32(3)", "  assert(size_of[Segment[Fresh]]() == size_of[Segment[Evicted]]())\n  gone.generation == u32(3)", 1)
	code, abnormal := buildAndRun(t, "typestate", sized)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ETypestateInterpreted(t *testing.T) {
	if got := interpretChecked(t, typestateProgram); got != 42 {
		t.Fatalf("interpreter returned %d, want 42", got)
	}
}

// The two instantiations lower to one representation: same fields, same
// size, distinct C names — the phantom does its work in the name.
func TestE2ETypestateErased(t *testing.T) {
	out, err := New().WithSource("erase.oak", typestateProgram).EmitC().Get()
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	bodies := map[string]string{}
	for _, name := range []string{"oak_Segment_Fresh", "oak_Segment_Evicted"} {
		open := strings.Index(out, "typedef struct "+name+" {")
		if open < 0 {
			t.Fatalf("emitted C lacks the typedef of %s:\n%s", name, out)
		}
		close := strings.Index(out[open:], "} "+name+";")
		if close < 0 {
			t.Fatalf("emitted C lacks the end of the typedef of %s:\n%s", name, out)
		}
		body := out[open+len("typedef struct "+name+" {") : open+close]
		bodies[name] = strings.Join(strings.Fields(body), " ")
	}
	if bodies["oak_Segment_Fresh"] != bodies["oak_Segment_Evicted"] {
		t.Fatalf("the two states must share one representation:\n%s\n%s", bodies["oak_Segment_Fresh"], bodies["oak_Segment_Evicted"])
	}
	// A marker is a type, never a value: no variable or parameter is
	// declared with a marker type.
	for _, marker := range []string{"oak_Fresh ", "oak_Published ", "oak_Offloaded ", "oak_Evicted "} {
		for _, line := range strings.Split(out, "\n") {
			trimmed := strings.TrimSpace(line)
			if strings.HasPrefix(trimmed, marker) && !strings.HasPrefix(trimmed, "typedef") {
				t.Fatalf("a state marker must never be instantiated as a value: %s", trimmed)
			}
		}
	}
}

func checkTypestate(t *testing.T, name, src string) error {
	t.Helper()
	_, err := New().WithSource(name+".oak", src).Check().Get()
	return err
}

func TestTypestateIllegalTransitionIsTypeError(t *testing.T) {
	src := strings.Replace(typestateProgram, "gone: Segment[Evicted] = evict(offload(publish(fresh)))", "p: Segment[Published] = publish(fresh)\n  gone: Segment[Evicted] = evict(p)", 1)
	err := checkTypestate(t, "illegal", src)
	if err == nil || !strings.Contains(err.Error(), "expected Segment_Offloaded, got Segment_Published") {
		t.Fatalf("evict on a Published handle must be a type error, got %v", err)
	}
	// The consumed handle is dead in its old state.
	src = strings.Replace(typestateProgram, "gone: Segment[Evicted] = evict(offload(publish(fresh)))", "gone: Segment[Evicted] = evict(offload(publish(fresh)))\n  again: Segment[Published] = publish(fresh)", 1)
	err = checkTypestate(t, "reuse", src)
	if err == nil || !strings.Contains(err.Error(), "OAK-B0111") {
		t.Fatalf("reusing the consumed Fresh handle must be use-after-consume, got %v", err)
	}
}

func TestTypestateViaSignatureChecked(t *testing.T) {
	for name, tc := range map[string]struct{ from, to, want string }{
		"wrong parameter state": {"offload: (s: Segment[Published]): Segment[Offloaded]", "offload: (s: Segment[Fresh]): Segment[Offloaded]", "requires Segment[Published]"},
		"wrong return state":    {"offload: (s: Segment[Published]): Segment[Offloaded]", "offload: (s: Segment[Published]): Segment[Evicted]", "requires Segment[Offloaded]"},
		"bare template":         {"offload: (s: Segment[Published]): Segment[Offloaded]", "offload: (s: Segment[Published]): Segment", "without its state"},
	} {
		t.Run(name, func(t *testing.T) {
			src := strings.Replace(typestateProgram, tc.from, tc.to, 1)
			err := checkTypestate(t, "sig", src)
			if err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("expected a protocol shape error mentioning %q, got %v", tc.want, err)
			}
		})
	}
	generic := strings.Replace(typestateProgram, "offload: (s: Segment[Published]): Segment[Offloaded]", "offload[S]: (s: Segment[S]): Segment[Offloaded]", 1)
	err := checkTypestate(t, "generic", generic)
	if err == nil || !strings.Contains(err.Error(), "type variable") {
		t.Fatalf("a type-variable index on a via callable must be rejected, got %v", err)
	}
}

func TestTypestateConstructionOnlyInTransition(t *testing.T) {
	forge := typestateProgram + `
forge: (): Segment[Evicted] = Segment { id: u32(0), generation: u32(0) }
`
	err := checkTypestate(t, "forge", forge)
	if err == nil || !strings.Contains(err.Error(), "OAK-B0121") {
		t.Fatalf("constructing an Evicted handle outside evict must be OAK-B0121, got %v", err)
	}
	// The initial state may be constructed anywhere; a literal without
	// context is an error asking for an annotation.
	anywhere := typestateProgram + `
mint: (id: u32): Segment[Fresh] = Segment { id: id, generation: u32(0) }
`
	if err := checkTypestate(t, "mint", anywhere); err != nil {
		t.Fatalf("constructing the initial state anywhere must be accepted: %v", err)
	}
	bare := typestateProgram + `
loose: (): u32 {
  _ = Segment { id: u32(1), generation: u32(0) }
  0
}
`
	err = checkTypestate(t, "bare", bare)
	if err == nil || !strings.Contains(err.Error(), "type arguments from context") {
		t.Fatalf("a template literal without context must ask for an annotation, got %v", err)
	}
}
