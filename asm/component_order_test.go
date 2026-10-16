package asm

import (
	"fmt"
	"math/rand"
	"reflect"
	"sort"
	"testing"
)

// Keep the old explicit-clique algorithm as an independent ordering oracle.
// Strong-component representatives and the input block order are held fixed:
// componentBlaster already has map-order-dependent union/read insertion, and
// this performance change must not replace that separate ordering policy.
func referenceComponentBlockOrder(blocks []string, weak [][]string, sideBlock string, find func(string) string) []string {
	adjacent := map[string][]string{}
	for _, members := range weak {
		for i := range members {
			for j := range members {
				bi, bj := find(members[i]), find(members[j])
				if bi != bj {
					adjacent[bi] = append(adjacent[bi], bj)
				}
			}
		}
	}
	var order []string
	queued := map[string]bool{}
	if sideBlock != "" {
		queue := []string{sideBlock}
		queued[sideBlock] = true
		for len(queue) > 0 {
			block := queue[0]
			queue = queue[1:]
			order = append(order, block)
			next := append([]string(nil), adjacent[block]...)
			sort.Strings(next)
			for _, n := range next {
				if !queued[n] {
					queued[n] = true
					queue = append(queue, n)
				}
			}
		}
	}
	for _, block := range blocks {
		if !queued[block] {
			queued[block] = true
			order = append(order, block)
		}
	}
	for i, j := 0, len(order)-1; i < j; i, j = i+1, j-1 {
		order[i], order[j] = order[j], order[i]
	}
	return order
}

func TestComponentBlockOrderMatchesCliques(t *testing.T) {
	rng := rand.New(rand.NewSource(737))
	for trial := 0; trial < 500; trial++ {
		n := 1 + rng.Intn(20)
		blocks := make([]string, n)
		parent := map[string]string{}
		var atoms []string
		for i := range blocks {
			blocks[i] = fmt.Sprintf("block%02d", i)
			// Fixed forests include multiple atoms and multi-hop paths per block.
			previous := blocks[i]
			depth := 1 + rng.Intn(4)
			for j := 0; j < depth; j++ {
				atom := fmt.Sprintf("atom%02d_%d", i, j)
				parent[atom] = previous
				atoms = append(atoms, atom)
				previous = atom
			}
		}
		find := func(x string) string {
			for parent[x] != "" {
				x = parent[x]
			}
			return x
		}
		rng.Shuffle(n, func(i, j int) { blocks[i], blocks[j] = blocks[j], blocks[i] })
		weak := make([][]string, rng.Intn(30))
		for i := range weak {
			for j := rng.Intn(30); j > 0; j-- {
				weak[i] = append(weak[i], atoms[rng.Intn(len(atoms))])
			}
		}
		side := ""
		if trial%3 != 0 {
			side = blocks[rng.Intn(n)]
		}
		want := referenceComponentBlockOrder(blocks, weak, side, find)
		got := componentBlockOrder(blocks, weak, side, find)
		if !reflect.DeepEqual(got, want) {
			t.Fatalf("trial %d: order %v, want %v", trial, got, want)
		}
	}
}

func TestComponentBlockOrderRepeatedMemberships(t *testing.T) {
	// Nested Boolean subterms can repeatedly mention hundreds of atoms even
	// when strong links collapse them into only a handful of components.
	// Count representative lookups, rather than asserting a host-dependent
	// runtime: each atom membership is resolved once, never once per pair.
	const atoms = 256
	const edges = 512
	blocks := []string{"b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7", "disconnected"}
	parent := map[string]string{}
	members := make([]string, atoms)
	for i := range members {
		members[i] = fmt.Sprintf("a%03d", i)
		parent[members[i]] = blocks[i%8]
	}
	weak := make([][]string, edges)
	for i := range weak {
		weak[i] = members
	}
	calls := 0
	find := func(x string) string { calls++; return parent[x] }
	got := componentBlockOrder(blocks, weak, "b0", find)
	want := []string{"disconnected", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("order %v, want %v", got, want)
	}
	if calls != atoms*edges {
		t.Fatalf("%d representative lookups, want %d", calls, atoms*edges)
	}
}

func TestComponentBlasterRepeatedBooleanDAG(t *testing.T) {
	x, y := paramTerm("x", 4), paramTerm("y", 4)
	names := []string{"x", "y"}
	widths := map[string]int{"x": 4, "y": 4}
	condition := constTerm(0, 1)
	for i := 0; i < 128; i++ {
		name := fmt.Sprintf("p%03d", i)
		names = append(names, name)
		widths[name] = 1
		condition = binaryTerm("or", condition, paramTerm(name, 1))
	}
	sort.Strings(names)
	premise := binaryTerm("and", cmpTerm("eq", x, y), condition)
	for _, wrong := range []bool{false, true} {
		b := y
		if wrong {
			b = binaryTerm("xor", y, constTerm(1, 4))
		}
		bl := componentBlaster(names, widths, premise, x, b)
		if bl == nil {
			t.Fatal("missing component order")
		}
		if bl.blockOf["x"] != bl.blockOf["y"] {
			t.Fatal("equality operands no longer interleave")
		}
		holds, decided := impliesEqualUnder(bl, premise, x, b, 4)
		if !decided || holds == wrong {
			t.Fatalf("wrong=%v: holds=%v decided=%v", wrong, holds, decided)
		}
	}
}

func BenchmarkComponentBlockOrderRepeatedMemberships(b *testing.B) {
	members := make([]string, 256)
	for i := range members {
		members[i] = fmt.Sprintf("b%d", i%8)
	}
	weak := make([][]string, 512)
	for i := range weak {
		weak[i] = members
	}
	blocks := []string{"b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7"}
	find := func(x string) string { return x }
	b.ReportAllocs()
	for b.Loop() {
		componentBlockOrder(blocks, weak, "b0", find)
	}
}

func BenchmarkComponentBlockOrderReference(b *testing.B) {
	members := make([]string, 256)
	for i := range members {
		members[i] = fmt.Sprintf("b%d", i%8)
	}
	weak := make([][]string, 512)
	for i := range weak {
		weak[i] = members
	}
	blocks := []string{"b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7"}
	find := func(x string) string { return x }
	b.ReportAllocs()
	for b.Loop() {
		referenceComponentBlockOrder(blocks, weak, "b0", find)
	}
}
