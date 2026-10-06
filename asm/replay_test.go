package asm

import (
	"bufio"
	"fmt"
	"os"
	"sort"
	"strconv"
	"strings"
	"testing"
	"time"
)

// readTermDAG rebuilds the terms writeTermDAG wrote: the roots in order
// and the parameters' declared widths. A developer's own dump is the only
// input; the loader still checks every reference so a damaged file fails
// the test rather than the process.
func readTermDAG(path string) (roots []*term, widths map[string]int, err error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, nil, err
	}
	defer f.Close()
	var nodes []*term
	widths = map[string]int{}
	node := func(field string) (*term, error) {
		id, err := strconv.Atoi(field)
		if err != nil {
			return nil, err
		}
		if id == -1 {
			return nil, nil
		}
		if id < 0 || id >= len(nodes) {
			return nil, fmt.Errorf("node #%d referenced before it was written", id)
		}
		return nodes[id], nil
	}
	scanner := bufio.NewScanner(f)
	scanner.Buffer(make([]byte, 1<<20), 1<<26)
	line := 0
	for scanner.Scan() {
		line++
		fields := strings.Split(scanner.Text(), "\t")
		switch {
		case strings.HasPrefix(fields[0], "#"):
			if len(fields) < 10 {
				return nil, nil, fmt.Errorf("line %d: %d fields", line, len(fields))
			}
			id, err := strconv.Atoi(fields[0][1:])
			if err != nil || id != len(nodes) {
				return nil, nil, fmt.Errorf("line %d: node %q out of order", line, fields[0])
			}
			kind, _ := strconv.Atoi(fields[1])
			width, _ := strconv.Atoi(fields[2])
			declared, _ := strconv.Atoi(fields[3])
			value, _ := strconv.ParseUint(fields[6], 10, 64)
			t := &term{kind: termKind(kind), width: width, declared: declared, op: fields[4], name: fields[5], value: value}
			if t.cond, err = node(fields[7]); err != nil {
				return nil, nil, fmt.Errorf("line %d: %v", line, err)
			}
			if t.left, err = node(fields[8]); err != nil {
				return nil, nil, fmt.Errorf("line %d: %v", line, err)
			}
			if t.right, err = node(fields[9]); err != nil {
				return nil, nil, fmt.Errorf("line %d: %v", line, err)
			}
			for _, field := range fields[10:] {
				if field == "" {
					continue
				}
				arg, err := node(field)
				if err != nil {
					return nil, nil, fmt.Errorf("line %d: %v", line, err)
				}
				t.args = append(t.args, arg)
			}
			nodes = append(nodes, t)
		case fields[0] == "width" && len(fields) == 3:
			widths[fields[1]], _ = strconv.Atoi(fields[2])
		case fields[0] == "root" && len(fields) == 2:
			root, err := node(strings.TrimPrefix(fields[1], "#"))
			if err != nil {
				return nil, nil, fmt.Errorf("line %d: %v", line, err)
			}
			roots = append(roots, root)
		default:
			return nil, nil, fmt.Errorf("line %d: unrecognized", line)
		}
	}
	return roots, widths, scanner.Err()
}

// TestReplayObligation decides one dumped loop obligation
// (OAK_VERIFY_OBLIGATION_DUMP=<path> writes <path>.dag; OAK_VERIFY_REPLAY
// names it) under a loop proof's budget and reports the cost: the study of
// a coupling failure without rebuilding the package it came from.
func TestReplayObligation(t *testing.T) {
	path := os.Getenv("OAK_VERIFY_REPLAY")
	if path == "" {
		t.Skip("OAK_VERIFY_REPLAY names no dump")
	}
	roots, widths, err := readTermDAG(path)
	if err != nil {
		t.Fatal(err)
	}
	if len(roots) != 3 {
		t.Fatalf("%d roots, want premise, a, b", len(roots))
	}
	premise, a, b := roots[0], roots[1], roots[2]
	widthOf := func(name string) int {
		if w, known := widths[name]; known {
			return w
		}
		return 32
	}
	t.Logf("premise %d nodes, a %d nodes, b %d nodes", termSize(premise, map[*term]int{}), termSize(a, map[*term]int{}), termSize(b, map[*term]int{}))
	budget := &nodeBudget{remaining: loopProofNodeBudget, loop: true}
	start := time.Now()
	holds, decided := impliesEqualWithin(premise, a, b, widthOf, budget)
	t.Logf("holds=%v decided=%v in %s, budget remaining %d, %d implications", holds, decided, time.Since(start).Round(time.Millisecond), budget.remaining, budget.calls)
	if !decided {
		t.Fatalf("the obligation was not decided")
	}
	if !holds {
		t.Fatalf("the obligation was refuted")
	}
}

// TestReplayBlast blasts one dumped term (OAK_VERIFY_REPLAY_BLAST names a
// DAG with one root) under the default order and reports, along the path
// of the largest subterm, the diagram each subterm needs on its own.
func TestReplayBlast(t *testing.T) {
	path := os.Getenv("OAK_VERIFY_REPLAY_BLAST")
	if path == "" {
		t.Skip("OAK_VERIFY_REPLAY_BLAST names no dump")
	}
	roots, widths, err := readTermDAG(path)
	if err != nil {
		t.Fatal(err)
	}
	if len(roots) != 1 {
		t.Fatalf("%d roots, want one", len(roots))
	}
	root := roots[0]
	mentioned := map[string]bool{}
	collectParams(root, mentioned)
	var names []string
	for name := range mentioned {
		names = append(names, name)
		if _, known := widths[name]; !known {
			widths[name] = 32
		}
	}
	sort.Strings(names)
	t.Logf("%d term nodes over %v", termSize(root, map[*term]int{}), names)
	bl := newBlaster(names, widths)
	bl.bdd = newBDD(blastNodeBudget)
	diagnoseBlast(bl, constTerm(1, 1), root)
}
