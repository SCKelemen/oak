package asm

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"
)

// Clauses retain their exact signed literals and ordering. In particular, this
// projection must not repair the producer's clauses or normalize duplicates.
func renderCNFTraceClauses(clauses [][]int) string {
	rendered := make([]string, len(clauses))
	for index, clause := range clauses {
		literals := make([]string, len(clause))
		for index, literal := range clause {
			literals[index] = strconv.Itoa(literal)
		}
		rendered[index] = "[" + strings.Join(literals, ", ") + "]"
	}
	return "[" + strings.Join(rendered, ", ") + "]"
}

func renderCNFTraceSnapshot(builder *cnfBuilder, obligation []int, emitted [][]int) (string, error) {
	allocation, err := renderCNFAllocationSnapshot(builder)
	if err != nil {
		return "", err
	}
	roots := make([]string, len(obligation))
	for index, edge := range obligation {
		if edge < 0 {
			return "", fmt.Errorf("obligation edge %d is outside the Nat projection", index)
		}
		roots[index] = strconv.Itoa(edge)
	}
	return fmt.Sprintf("⟨%s, %s, [%s], %s⟩", allocation,
		renderCNFTraceClauses(builder.clauses), strings.Join(roots, ", "),
		renderCNFTraceClauses(emitted)), nil
}

// Fixed expectations constrain the production decision independently of Lean.
// The kernel then replays the actual allocation, clauses and roots from the Go
// fixture, without a second Go implementation of the clause checker.
func TestValidateCNFTraceMatchesLean(t *testing.T) {
	type traceCase struct {
		name           string
		builder        *cnfBuilder
		obligation     []int
		emitted        [][]int
		wantAccepted   bool
		wantProjection bool
	}
	var cases []traceCase
	addValid := func(name string, builder *cnfBuilder, obligation []int) {
		cases = append(cases, traceCase{
			name: name, builder: builder, obligation: obligation,
			emitted:      emittedCNFTraceClauses(builder, obligation),
			wantAccepted: true, wantProjection: true,
		})
	}
	for _, operation := range []struct {
		name string
		tag  int
	}{{"and", opAnd}, {"or", opOr}, {"xor", opXor}} {
		for polarity := 0; polarity < 4; polarity++ {
			for finalPolarity := 0; finalPolarity < 2; finalPolarity++ {
				builder := newCNFBuilder()
				left := builder.variable(0) ^ (polarity & 1)
				right := builder.variable(1) ^ ((polarity >> 1) & 1)
				output := builder.apply(operation.tag, left, right)
				addValid(fmt.Sprintf("%s inputs %02b final %d", operation.name, polarity, finalPolarity),
					builder, []int{output ^ finalPolarity})
			}
		}
	}
	for polarity := 0; polarity < 8; polarity++ {
		for finalPolarity := 0; finalPolarity < 2; finalPolarity++ {
			builder := newCNFBuilder()
			condition := builder.variable(0) ^ (polarity & 1)
			thenValue := builder.variable(1) ^ ((polarity >> 1) & 1)
			elseValue := builder.variable(2) ^ ((polarity >> 2) & 1)
			output := builder.ite(condition, thenValue, elseValue)
			addValid(fmt.Sprintf("ite inputs %03b final %d", polarity, finalPolarity),
				builder, []int{output ^ finalPolarity})
		}
	}
	builder, obligation, _ := validCNFTraceFixture()
	addValid("interleaved allocation", builder, obligation)
	inputOnly := newCNFBuilder()
	input := inputOnly.variable(7)
	addValid("input only", inputOnly, []int{input})
	addValid("duplicate and complementary final roots", inputOnly, []int{input, input, input ^ 1})

	for _, mutation := range []struct {
		name            string
		mutate          func(*cnfBuilder, *[]int, *[][]int)
		projectionFails bool
	}{
		{"missing builder clause", func(builder *cnfBuilder, _ *[]int, _ *[][]int) {
			builder.clauses = builder.clauses[1:]
		}, false},
		{"extra builder clause", func(builder *cnfBuilder, _ *[]int, _ *[][]int) {
			builder.clauses = append(builder.clauses, []int{1})
		}, false},
		{"reordered builder clauses", func(builder *cnfBuilder, _ *[]int, _ *[][]int) {
			builder.clauses[0], builder.clauses[1] = builder.clauses[1], builder.clauses[0]
		}, false},
		{"reordered builder literals", func(builder *cnfBuilder, _ *[]int, _ *[][]int) {
			clause := builder.clauses[0]
			clause[0], clause[1] = clause[1], clause[0]
		}, false},
		{"missing builder literal", func(builder *cnfBuilder, _ *[]int, _ *[][]int) {
			builder.clauses[0] = builder.clauses[0][:1]
		}, false},
		{"extra builder literal", func(builder *cnfBuilder, _ *[]int, _ *[][]int) {
			builder.clauses[0] = append(builder.clauses[0], 1)
		}, false},
		{"missing clause shared by builder and emitted", func(builder *cnfBuilder, obligation *[]int, emitted *[][]int) {
			builder.clauses = builder.clauses[1:]
			*emitted = emittedCNFTraceClauses(builder, *obligation)
		}, false},
		{"extra clause shared by builder and emitted", func(builder *cnfBuilder, obligation *[]int, emitted *[][]int) {
			builder.clauses = append(builder.clauses, []int{1})
			*emitted = emittedCNFTraceClauses(builder, *obligation)
		}, false},
		{"reordered clauses shared by builder and emitted", func(builder *cnfBuilder, obligation *[]int, emitted *[][]int) {
			builder.clauses[0], builder.clauses[1] = builder.clauses[1], builder.clauses[0]
			*emitted = emittedCNFTraceClauses(builder, *obligation)
		}, false},
		{"wrong polarity shared by builder and emitted", func(builder *cnfBuilder, obligation *[]int, emitted *[][]int) {
			builder.clauses[0][0] = -builder.clauses[0][0]
			*emitted = emittedCNFTraceClauses(builder, *obligation)
		}, false},
		{"zero literal shared by builder and emitted", func(builder *cnfBuilder, obligation *[]int, emitted *[][]int) {
			builder.clauses[0][0] = 0
			*emitted = emittedCNFTraceClauses(builder, *obligation)
		}, false},
		{"missing emitted clause", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			*emitted = (*emitted)[1:]
		}, false},
		{"extra emitted clause", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			*emitted = append(*emitted, []int{1})
		}, false},
		{"reordered emitted clauses", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			(*emitted)[0], (*emitted)[1] = (*emitted)[1], (*emitted)[0]
		}, false},
		{"reordered emitted literals", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			clause := (*emitted)[0]
			clause[0], clause[1] = clause[1], clause[0]
		}, false},
		{"missing emitted literal", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			(*emitted)[0] = (*emitted)[0][:1]
		}, false},
		{"extra emitted literal", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			(*emitted)[0] = append((*emitted)[0], 1)
		}, false},
		{"unsupported gate tag", func(builder *cnfBuilder, _ *[]int, _ *[][]int) {
			gate := &builder.gates[0]
			delete(builder.memo, cnfKey{op: gate.op, x: gate.x, y: gate.y, z: -1})
			gate.op = 99
			builder.memo[cnfKey{op: gate.op, x: gate.x, y: gate.y, z: -1}] = gate.out
		}, false},
		{"empty obligation", func(_ *cnfBuilder, obligation *[]int, emitted *[][]int) {
			*obligation = nil
			(*emitted)[len(*emitted)-1] = nil
		}, false},
		{"false constant root", func(builder *cnfBuilder, obligation *[]int, emitted *[][]int) {
			(*obligation)[0] = bddFalse
			*emitted = emittedCNFTraceClauses(builder, *obligation)
		}, false},
		{"true constant root", func(builder *cnfBuilder, obligation *[]int, emitted *[][]int) {
			(*obligation)[0] = bddTrue
			*emitted = emittedCNFTraceClauses(builder, *obligation)
		}, false},
		{"unallocated root", func(builder *cnfBuilder, obligation *[]int, emitted *[][]int) {
			(*obligation)[0] = 2 * (builder.variables + 1)
			*emitted = emittedCNFTraceClauses(builder, *obligation)
		}, false},
		{"negative root projection refused", func(_ *cnfBuilder, obligation *[]int, _ *[][]int) {
			(*obligation)[0] = -2
		}, true},
		{"missing final clause", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			*emitted = (*emitted)[:len(*emitted)-1]
		}, false},
		{"empty emitted trace", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			*emitted = nil
		}, false},
		{"missing final literal", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			final := (*emitted)[len(*emitted)-1]
			(*emitted)[len(*emitted)-1] = final[:len(final)-1]
		}, false},
		{"extra final literal", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			final := (*emitted)[len(*emitted)-1]
			(*emitted)[len(*emitted)-1] = append(final, final[0])
		}, false},
		{"wrong final polarity", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			final := (*emitted)[len(*emitted)-1]
			final[0] = -final[0]
		}, false},
		{"wrong final order", func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
			final := (*emitted)[len(*emitted)-1]
			final[0], final[1] = final[1], final[0]
		}, false},
	} {
		builder, obligation, emitted := validCNFTraceFixture()
		mutation.mutate(builder, &obligation, &emitted)
		cases = append(cases, traceCase{
			name: mutation.name, builder: builder, obligation: obligation, emitted: emitted,
			wantAccepted: false, wantProjection: !mutation.projectionFails,
		})
	}

	var leanExamples []string
	t.Run("decisions", func(t *testing.T) {
		for index, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				validationErr := validateCNFTrace(test.builder, test.obligation, test.emitted)
				accepted := validationErr == nil
				if accepted != test.wantAccepted {
					t.Fatalf("accepted = %t, want %t: %v", accepted, test.wantAccepted, validationErr)
				}
				snapshot, err := renderCNFTraceSnapshot(test.builder, test.obligation, test.emitted)
				if (err == nil) != test.wantProjection {
					t.Fatalf("projectable = %t, want %t: %v", err == nil, test.wantProjection, err)
				}
				if err != nil {
					return
				}
				leanExamples = append(leanExamples, fmt.Sprintf(
					"def snapshot%d : Snapshot := %s\nexample : (check snapshot%d).isSome = %t := by decide",
					index, snapshot, index, accepted))
			})
		}
	})
	if t.Failed() {
		return
	}
	t.Run("kernel", func(t *testing.T) {
		lake, err := exec.LookPath("lake")
		if err != nil {
			t.Skip("lake not on PATH; the formal workflow runs this kernel oracle")
		}
		if len(leanExamples) == 0 {
			t.Fatal("no production snapshots were checked; run the decisions subtest too")
		}
		leanPath := filepath.Join(t.TempDir(), "CNFClauseTraceProductionPins.lean")
		leanSource := "import Oak.CNFClauseTrace\n\nnamespace Oak.CNFClauseTrace\n\n" +
			strings.Join(leanExamples, "\n\n") + "\n\nend Oak.CNFClauseTrace\n"
		if err := os.WriteFile(leanPath, []byte(leanSource), 0o600); err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
		defer cancel()
		command := exec.CommandContext(ctx, lake, "env", "lean", leanPath)
		command.Dir = filepath.Join("..", "spec", "lean")
		if output, err := command.CombinedOutput(); err != nil {
			t.Fatalf("kernel-checking production clause trace pins: %v (context: %v)\n%s\n--- source ---\n%s",
				err, ctx.Err(), output, leanSource)
		}
	})
}
