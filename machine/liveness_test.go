package machine

import (
	"reflect"
	"slices"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// A path oracle, independent of the bitset fixpoint: a web is live at a
// block's entry if some path reads it before encountering its next definition.
func reachesWebRead(w *Web, start *Block) bool {
	reads, writes := map[*Instr]bool{}, map[*Instr]bool{}
	for _, u := range w.Uses {
		reads[u.Instr] = true
	}
	for _, d := range w.Defs {
		writes[d.Instr] = true
	}
	seen := map[*Block]bool{}
	pending := []*Block{start}
	for len(pending) > 0 {
		b := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		if seen[b] {
			continue
		}
		seen[b] = true
		killed := false
		for _, ins := range b.Instrs {
			if reads[ins] {
				return true // tied operands read before they write
			}
			if writes[ins] {
				killed = true
				break
			}
		}
		if !killed {
			pending = append(pending, b.Succs...)
		}
	}
	return false
}

func TestLivenessSetsAndRangeStorage(t *testing.T) {
	for _, test := range []struct {
		name string
		body *asm.Function
	}{
		{"return only", fn(ins("ret"))},
		{"diamond", fn(
			ins("cbz", w(0), sym("right")), ins("add", w(9), w(1), imm(1)), ins("b", sym("join")),
			label("right"), ins("add", w(9), w(2), imm(2)), label("join"),
			ins("add", w(0), w(9), w(1)), ins("ret"),
		)},
		{"entry loop", fn(label("loop"), ins("add", w(9), w(9), imm(1)),
			ins("cbnz", w(1), sym("loop")), ins("mov", w(0), w(9)), ins("ret"))},
		{"unreachable root", fn(ins("b", sym("done")), label("dead"),
			ins("add", w(9), w(0), w(1)), ins("str", w(9), mem(x(2), 0)),
			label("done"), ins("ret"))},
		{"pair and call", fn(ins("ldp", x(9), x(10), mem(sp(), 16)),
			ins("add", x(0), x(9), x(10)), ins("bl", sym("g")),
			ins("add", x(0), x(0), x(1)), ins("ret"))},
		{"tied vector", fn(ins("movi", v(16, "4s"), imm(0)),
			ins("mla", v(16, "4s"), v(17, "4s"), v(18, "4s")),
			ins("str", q(16), mem(x(0), 0)), ins("ret"))},
		{"multiple bitset words", websBenchmarkBody(8, 12, false)},
		{"multiple bitset words with loop", websBenchmarkBody(8, 12, true)},
		{"rv64 call", rvfn(ins("add", rx(5), rx(10), rx(11)),
			ins("sd", rx(5), mem(sp(), 16)), ins("call", sym("g")),
			ins("ld", rx(5), mem(sp(), 16)), ins("add", rx(10), rx(10), rx(5)), ins("ret"))},
	} {
		t.Run(test.name, func(t *testing.T) {
			original := cloneFunction(test.body)
			f, err := Lift(test.body)
			if err != nil {
				t.Fatal(err)
			}
			webs, err := f.Webs()
			if err != nil {
				t.Fatal(err)
			}
			for permutation := 0; permutation < 2; permutation++ {
				if permutation != 0 {
					slices.Reverse(webs) // positions must not be confused with Web.Index
				}
				in, out := f.Liveness(webs)
				if len(in) != len(f.Blocks) || len(out) != len(f.Blocks) {
					t.Fatal("missing block sets")
				}
				for i, b := range f.Blocks {
					wantIn, wantOut := map[*Web]bool{}, map[*Web]bool{}
					for _, w := range webs {
						if reachesWebRead(w, b) {
							wantIn[w] = true
						}
						for _, next := range b.Succs {
							if reachesWebRead(w, next) {
								wantOut[w] = true
							}
						}
					}
					if !reflect.DeepEqual(in[i], wantIn) || !reflect.DeepEqual(out[i], wantOut) {
						t.Fatalf("block %d sets disagree with path reachability", i)
					}
				}
				checkRangeStorage(t, f, webs)
			}
			if !reflect.DeepEqual(original, test.body) {
				t.Fatal("liveness changed the input assembly")
			}
		})
	}
}

func checkRangeStorage(t *testing.T, f *Function, webs []*Web) {
	t.Helper()
	type saved struct {
		from, to int
		segments []seg
	}
	want := make([]saved, len(webs))
	borrowed := make([][]seg, len(webs))
	for i, w := range webs {
		want[i] = saved{w.From, w.To, slices.Clone(w.Segs)}
		borrowed[i] = w.Segs
	}
	f.liveRanges(webs)
	for i, w := range webs {
		if w.From != want[i].from || w.To != want[i].to || !slices.Equal(w.Segs, want[i].segments) {
			t.Fatalf("web %d ranges changed when inspection maps were omitted", i)
		}
		if !slices.Equal(borrowed[i], want[i].segments) {
			t.Fatalf("web %d's earlier range storage was overwritten", i)
		}
	}
	for i, w := range webs {
		// Both writing an existing segment and appending beyond the current
		// length must leave every other web's segments alone.
		grown := append(w.Segs, seg{-9, -8})
		grown[0] = seg{-7, -6}
		for j, other := range webs {
			if i != j && !slices.Equal(other.Segs, want[j].segments) {
				t.Fatalf("changing web %d's segments overwrote web %d", i, j)
			}
		}
		copy(w.Segs, want[i].segments)
	}
}
