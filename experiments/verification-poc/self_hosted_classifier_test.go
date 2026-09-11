package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
	"testing"
)

type classifierCase struct {
	Clause   []uint32 `json:"clause"`
	Cells    []uint32 `json:"cells"`
	Expected []uint32 `json:"expected"`
}

func classifierReference(c classifierCase) []uint32 {
	unknown := map[uint32]bool{}
	satisfied := false
	for _, n := range c.Clause {
		value := c.Cells[n/2]
		if value == 0 {
			unknown[n] = true
		} else if (value == 2) == (n%2 == 1) {
			satisfied = true
		}
	}
	if satisfied {
		return []uint32{2, 0}
	}
	if len(unknown) == 0 {
		return []uint32{0, 0}
	}
	if len(unknown) == 1 {
		for n := range unknown {
			return []uint32{1, n}
		}
	}
	return []uint32{3, 0}
}
func classifierCorpus() []classifierCase {
	cases := []classifierCase{}
	add := func(clause, cells []uint32) {
		c := classifierCase{append([]uint32{}, clause...), append([]uint32{}, cells...), nil}
		c.Expected = classifierReference(c)
		cases = append(cases, c)
	}
	// All 9 assignments and 85 ordered clauses of length 0..3 on two variables.
	for a := uint32(0); a < 3; a++ {
		for b := uint32(0); b < 3; b++ {
			var visit func([]uint32, int)
			visit = func(clause []uint32, left int) {
				add(clause, []uint32{a, b})
				if left > 0 {
					for n := uint32(0); n < 4; n++ {
						visit(append(append([]uint32{}, clause...), n), left-1)
					}
				}
			}
			visit(nil, 3)
		}
	}
	// Both polarities, every variable boundary, all assignment states. Repeated
	// units must count once even when their encoding is zero or at the upper limit.
	for v := 0; v < 64; v++ {
		for polarity := uint32(0); polarity < 2; polarity++ {
			for value := uint32(0); value < 3; value++ {
				cells := make([]uint32, v+1)
				cells[v] = value
				n := uint32(v*2) + polarity
				add([]uint32{n, n, n, n}, cells)
			}
		}
	}
	return cases
}
func classifierLoop(t *testing.T, source string) string {
	t.Helper()
	begin := "    satisfied: Bool = false\n"
	end := "    valid && !satisfied ? {\n"
	if strings.Count(source, begin) != 1 || strings.Count(source, end) != 1 {
		t.Fatal("classifier extraction seam changed")
	}
	start := strings.Index(source, begin)
	stop := strings.Index(source, end)
	if stop <= start {
		t.Fatal("classifier extraction order changed")
	}
	// Preserve the actual duplicate-aware scan byte-for-byte, including its early
	// stop. The wrapper supplies a single valid clause and a complete assignment.
	return `classifier_observed: (clause_literals: []u32, assignments: []u8, expected: []u32): Bool {
  variables: u32 = len(assignments)
  start: u32 = 0
  count: u32 = len(clause_literals)
  valid: Bool = variables > u32(0) && variables <= u32(64)
` + source[start:stop] + `
  kind: u32 = 3
  unit: u32 = 0
  satisfied ? { kind = u32(2) } | {
    remaining == u32(0) ? { kind = u32(0) } | {
      remaining == u32(1) ? { kind = u32(1); unit = unit_literal }
    }
  }
  valid && len(expected) == u32(2) && expected[0] == kind && expected[1] == unit
}
`
}
func TestSelfHostedClauseClassifier(t *testing.T) {
	cases := classifierCorpus()
	counts := [4]int{}
	kernel, err := os.ReadFile("self_hosted_rup.oak")
	if err != nil {
		t.Fatal(err)
	}
	var source, main strings.Builder
	for _, line := range strings.Split(string(kernel), "\n") {
		if strings.HasPrefix(line, "literal_value:") {
			source.WriteString(line)
			source.WriteByte('\n')
		}
	}
	source.WriteString(classifierLoop(t, string(kernel)))
	main.WriteString("main: (): i32 {\n")
	emit := func(i int, c classifierCase, want bool) {
		fmt.Fprintf(&source, "classifier_case_%d: (): Bool {\n", i)
		emitBufferArray(&source, "clause", "u32", c.Clause)
		emitBufferArray(&source, "cells", "u8", c.Cells)
		emitBufferArray(&source, "expected", "u32", c.Expected)
		fmt.Fprintf(&source, "classifier_observed(clause_view, cells_view, expected_view) == %t\n}\n", want)
		fmt.Fprintf(&main, "assert(classifier_case_%d())\n", i)
	}
	for i, c := range cases {
		counts[c.Expected[0]]++
		emit(i, c, true)
	}
	unitCase := cases[0]
	for _, c := range cases {
		if c.Expected[0] == 1 {
			unitCase = c
			break
		}
	}
	for i := 0; i < 3; i++ {
		c := unitCase
		c.Expected = append([]uint32{}, c.Expected...)
		switch i {
		case 0:
			c.Expected[0] = 0
		case 1:
			c.Expected[1] ^= 1
		case 2:
			c.Expected = c.Expected[:1]
		}
		emit(len(cases)+i, c, false)
	}
	main.WriteString("42\n}\n")
	source.WriteString(main.String())
	runOakStream(t, source.String())
	if path := os.Getenv("OAK_CLASSIFIER_CORPUS_OUT"); path != "" {
		data, err := json.MarshalIndent(cases, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, append(data, '\n'), 0644); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("Oak/Go clause classifier: %d cases (%d conflict, %d unit, %d satisfied, %d unresolved), 3 corruptions rejected", len(cases), counts[0], counts[1], counts[2], counts[3])
}
