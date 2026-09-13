package compiler

import (
	"strings"
	"testing"
)

// Fact indices (docs/spec/112-protocols.md section 5a, rule 6; the dbs
// pilot's round-five item 13, generalized): a typestate resource may carry
// further phantom indices beyond its state, each declared by a `fact F =
// A | B` clause and drawn from that closed marker set, so "sealed" is a
// type the handle carries — `Segment[Published, Sealed]` — rather than a
// flag in data. A via callable may move a fact or leave it polymorphic;
// the state position still names a concrete state.
const factsProgram = `import(std)
Segment[S, F]: type = struct { id: u32, generation: u32 }

Custody: protocol = {
  resource Segment
  fact F = Open | Sealed
  initial Fresh
  publish: Fresh -> Published via publish(consumed s)
  seal: Published -> Published via seal(consumed s)
  evict: Published -> Evicted via evict(consumed s)
}

publish[F]: (s: Segment[Fresh, F]): Segment[Published, F] = Segment { id: s.id, generation: s.generation + u32(1) }
seal: (s: Segment[Published, Open]): Segment[Published, Sealed] = Segment { id: s.id, generation: s.generation + u32(1) }
evict: (s: Segment[Published, Sealed]): Segment[Evicted, Sealed] = Segment { id: s.id, generation: s.generation + u32(1) }

main: (): i32 {
  fresh: Segment[Fresh, Open] = Segment { id: u32(7), generation: u32(0) }
  p: Segment[Published, Open] = publish(fresh)
  sealed: Segment[Published, Sealed] = seal(p)
  gone: Segment[Evicted, Sealed] = evict(sealed)
  gone.generation == u32(3) && gone.id == u32(7) ? 42 | 1
}
`

func TestE2ETypestateFactIndices(t *testing.T) {
	if got := interpretChecked(t, factsProgram); got != 42 {
		t.Fatalf("interpreter: %d, want 42", got)
	}
	code, abnormal := buildAndRun(t, "typestate_facts", factsProgram)
	if abnormal || code != 42 {
		t.Fatalf("compiled: exit %d abnormal %v, want 42", code, abnormal)
	}
}

func TestE2ETypestateFactIndicesRejected(t *testing.T) {
	cases := map[string][2]string{
		"evicting an unsealed handle is a type error": {strings.Replace(factsProgram, "  gone: Segment[Evicted, Sealed] = evict(sealed)\n", "  gone: Segment[Evicted, Sealed] = evict(p)\n", 1), "Segment_Published_Sealed"},
		"a marker outside the fact's set":              {strings.Replace(factsProgram, "seal: (s: Segment[Published, Open]): Segment[Published, Sealed]", "seal: (s: Segment[Published, Open]): Segment[Published, Shut]", 1), "for fact F, which is one of Open | Sealed"},
		"a missing fact index":                         {strings.Replace(factsProgram, "evict: (s: Segment[Published, Sealed]): Segment[Evicted, Sealed]", "evict: (s: Segment[Published]): Segment[Evicted, Sealed]", 1), "with 0 fact indices; the protocol declares 1"},
		"a type-variable state":                        {strings.Replace(factsProgram, "seal: (s: Segment[Published, Open]): Segment[Published, Sealed]", "seal[S]: (s: Segment[S, Open]): Segment[Published, Sealed]", 1), "type variable"},
		"forging a state outside its transition":       {factsProgram + "\nforge: (): Segment[Evicted, Sealed] = Segment { id: u32(0), generation: u32(0) }\n", "OAK-B0121"},
	}
	for name, c := range cases {
		_, err := New().WithSource("facts.oak", c[0]).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c[1]) {
			t.Fatalf("%s: %v", name, err)
		}
	}
}
