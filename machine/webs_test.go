package machine

import (
	"fmt"
	"reflect"
	"slices"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func TestMergeReachingSites(t *testing.T) {
	// Exhaust all pairs of subsets of five sites against a bitset union.
	// Keep a sentinel and spare capacity behind each input: a merge that
	// appends into shared input storage must fail even if its values look right.
	set := func(mask int) []int {
		backing := make([]int, 8)
		n := 0
		for site := 0; site < 5; site++ {
			if mask&(1<<site) != 0 {
				backing[n] = site
				n++
			}
		}
		backing[n] = 999
		return backing[:n]
	}
	for left := 0; left < 32; left++ {
		for right := 0; right < 32; right++ {
			t.Run(fmt.Sprintf("%02x/%02x", left, right), func(t *testing.T) {
				a, b := set(left), set(right)
				beforeA, beforeB := slices.Clone(a[:cap(a)]), slices.Clone(b[:cap(b)])
				got, want := mergeReachingSites(a, b), set(left|right)
				if !slices.Equal(got, want) {
					t.Fatalf("union=%v, want %v", got, want)
				}
				if !slices.Equal(a[:cap(a)], beforeA) || !slices.Equal(b[:cap(b)], beforeB) {
					t.Fatal("union changed shared input storage")
				}
			})
		}
	}
}

func TestWebsReachingDefinitions(t *testing.T) {
	for _, test := range []struct {
		name   string
		body   *asm.Function
		read   int
		reg    Reg
		defs   []int // -1 denotes the entry pseudo-definition
		pinned bool
	}{
		{"diamond", fn(
			ins("cbz", w(0), sym("right")), ins("mov", w(9), w(1)), ins("b", sym("join")),
			label("right"), ins("mov", w(9), w(2)),
			label("join"), ins("str", w(9), mem(x(3), 0)), ins("ret"),
		), 4, Reg{GPR, 9}, []int{1, 3}, false},
		{"successor states stay independent", fn(
			ins("mov", w(9), w(0)), ins("cbz", w(1), sym("right")),
			ins("mov", w(9), w(2)), ins("str", w(9), mem(x(3), 0)), ins("b", sym("done")),
			label("right"), ins("str", w(9), mem(x(3), 0)),
			label("done"), ins("ret"),
		), 5, Reg{GPR, 9}, []int{0}, false},
		{"loop", fn(
			ins("mov", w(9), w(0)), label("loop"), ins("cmp", w(9), w(1)), bcond("hs", "done"),
			ins("add", w(9), w(9), imm(1)), ins("b", sym("loop")),
			label("done"), ins("mov", w(0), w(9)), ins("ret"),
		), 1, Reg{GPR, 9}, []int{0, 3}, false},
		{"entry loop", fn(
			label("loop"), ins("add", w(9), w(9), imm(1)), ins("cbnz", w(1), sym("loop")),
			ins("mov", w(0), w(9)), ins("ret"),
		), 0, Reg{GPR, 9}, []int{-1, 0}, true},
		{"unreachable definition stays separate", fn(
			ins("b", sym("done")), label("dead"), ins("mov", w(9), w(2)),
			ins("add", w(10), w(9), w(1)), ins("ret"),
			label("done"), ins("mov", w(0), w(9)), ins("ret"),
		), 4, Reg{GPR, 9}, []int{-1}, true},
		{"unreachable root has local definitions", fn(
			ins("b", sym("done")), label("dead"), ins("mov", w(9), w(2)),
			ins("add", w(10), w(9), w(1)), ins("ret"),
			label("done"), ins("mov", w(0), w(9)), ins("ret"),
		), 2, Reg{GPR, 9}, []int{1}, false},
		{"call clobber", fn(
			ins("mov", w(9), w(0)), ins("str", w(9), mem(x(20), 0)), ins("bl", sym("g")),
			ins("str", w(9), mem(x(20), 0)), ins("ret"),
		), 3, Reg{GPR, 9}, []int{2}, true},
		{"tied vector operand", fn(
			ins("movi", v(16, "4s"), imm(0)), ins("mla", v(16, "4s"), v(17, "4s"), v(18, "4s")),
			ins("str", q(16), mem(x(0), 0)), ins("ret"),
		), 1, Reg{VEC, 16}, []int{0, 1}, false},
	} {
		t.Run(test.name, func(t *testing.T) {
			before := cloneFunction(test.body)
			f, err := Lift(test.body)
			if err != nil {
				t.Fatal(err)
			}
			webs, err := f.Webs()
			if err != nil {
				t.Fatal(err)
			}
			found := false
			for _, web := range webs {
				if web.Reg != test.reg {
					continue
				}
				for _, use := range web.Uses {
					if use.Instr.Index != test.read {
						continue
					}
					found = true
					var defs []int
					for _, def := range web.Defs {
						index := -1
						if def.Instr != nil {
							index = def.Instr.Index
						}
						defs = append(defs, index)
					}
					slices.Sort(defs)
					if !slices.Equal(defs, test.defs) || web.Pinned != test.pinned {
						t.Fatalf("definitions=%v pinned=%v; want %v, %v", defs, web.Pinned, test.defs, test.pinned)
					}
				}
			}
			if !found {
				t.Fatalf("missing use of %s at instruction %d", test.reg, test.read)
			}
			repeated, err := f.Webs()
			if err != nil || !reflect.DeepEqual(webs, repeated) {
				t.Fatalf("webs changed on repeated analysis: %v", err)
			}
			if !reflect.DeepEqual(before, test.body) {
				t.Fatal("web analysis changed the assembly input")
			}
		})
	}
}
