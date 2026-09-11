package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)

type chainCase struct {
	selfHostedRUPCase
	Name string `json:"name"`
}

func chainCorpus(t *testing.T) []chainCase {
	t.Helper()
	cases := []chainCase{}
	add := func(name string, c selfHostedRUPCase) {
		clauses := [][]int{}
		for _, clause := range c.Clauses {
			clauses = append(clauses, append([]int{}, clause...))
		}
		c.Clauses = clauses
		c.Target = append([]int{}, c.Target...)
		c.Hints = append([]int{}, c.Hints...)
		c.Accepted = c.Variables > 0 && c.Variables <= 64 && lrat.CheckRUPDecoded(c.Variables, c.Clauses, c.Target, c.Hints) == nil
		cases = append(cases, chainCase{c, name})
	}
	for i, c := range propagationCorpus(t) {
		add(fmt.Sprintf("scratch-%d", i), c.selfHostedRUPCase)
	}
	for n := 1; n <= 64; n++ {
		clauses := [][]int{{1}}
		for v := 1; v < n; v++ {
			clauses = append(clauses, []int{-v, v + 1})
		}
		clauses = append(clauses, []int{-n})
		hints := []int{}
		for id := 1; id <= len(clauses); id++ {
			hints = append(hints, id)
		}
		c := selfHostedRUPCase{Variables: n, Clauses: clauses, Hints: hints}
		add(fmt.Sprintf("chain-%d", n), c)
		if !cases[len(cases)-1].Accepted {
			t.Fatal("ordered chain must refute", n)
		}
		repeated := [][]int{}
		for _, clause := range clauses {
			xs := []int{}
			for _, lit := range clause {
				xs = append(xs, lit, lit, lit)
			}
			repeated = append(repeated, xs)
		}
		c.Clauses = repeated
		add(fmt.Sprintf("duplicates-%d", n), c)
		if !cases[len(cases)-1].Accepted {
			t.Fatal("duplicate literals changed chain", n)
		}
		c.Clauses = clauses
		c.Hints = hints[:len(hints)-1]
		add(fmt.Sprintf("missing-conflict-%d", n), c)
		if cases[len(cases)-1].Accepted {
			t.Fatal("unfinished chain accepted", n)
		}
		c.Hints = append(append([]int{}, hints...), 1)
		add(fmt.Sprintf("nonfinal-conflict-%d", n), c)
		if cases[len(cases)-1].Accepted {
			t.Fatal("nonfinal conflict accepted", n)
		}
		c.Hints = append([]int{}, hints...)
		c.Hints[0], c.Hints[1] = c.Hints[1], c.Hints[0]
		add(fmt.Sprintf("swapped-hints-%d", n), c)
		if cases[len(cases)-1].Accepted != (n == 1) {
			t.Fatal("unexpected swapped chain result", n)
		}
	}
	return cases
}
func TestSelfHostedPropagationChain(t *testing.T) {
	cases := chainCorpus(t)
	accepted := 0
	kernel, err := os.ReadFile("self_hosted_rup.oak")
	if err != nil {
		t.Fatal(err)
	}
	var source, main strings.Builder
	source.Write(kernel)
	source.WriteByte('\n')
	main.WriteString("main: (): i32 {\n")
	for i, c := range cases {
		fmt.Fprintf(&source, "chain_case_%d: (): Bool {\n", i)
		pool, starts, sizes, target, hints := []uint32{}, []uint32{}, []uint32{}, []uint32{}, []uint32{}
		for _, clause := range c.Clauses {
			starts = append(starts, uint32(len(pool)))
			sizes = append(sizes, uint32(len(clause)))
			for _, lit := range clause {
				pool = append(pool, oakLiteral(lit))
			}
		}
		for _, lit := range c.Target {
			target = append(target, oakLiteral(lit))
		}
		for _, id := range c.Hints {
			n := uint32(4294967295)
			if id > 0 {
				n = uint32(id - 1)
			}
			hints = append(hints, n)
		}
		for _, a := range []struct {
			name  string
			items []uint32
		}{{"pool", pool}, {"starts", starts}, {"sizes", sizes}, {"target", target}, {"hints", hints}} {
			emitBufferArray(&source, a.name, "u32", a.items)
		}
		source.WriteString("assignments: [64]u8\n")
		fmt.Fprintf(&source, "rup_check(pool_view, starts_view, sizes_view, u32(%d), target_view, u32(%d), hints_view, u32(%d), span(&assignments), u32(%d)) == %t\n}\n", len(starts), len(target), len(hints), c.Variables, c.Accepted)
		fmt.Fprintf(&main, "assert(chain_case_%d())\n", i)
		if c.Accepted {
			accepted++
		}
	}
	main.WriteString("42\n}\n")
	source.WriteString(main.String())
	runOakStream(t, source.String())
	if path := os.Getenv("OAK_CHAIN_CORPUS_OUT"); path != "" {
		data, err := json.MarshalIndent(cases, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, append(data, '\n'), 0644); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("Oak/Go propagation chain: %d cases (%d accepted, %d rejected), up to 64 unit writes", len(cases), accepted, len(cases)-accepted)
}
