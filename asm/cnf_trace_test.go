package asm

import (
	"reflect"
	"testing"
)

func cloneCNFTraceClauses(clauses [][]int) [][]int {
	cloned := make([][]int, len(clauses))
	for i, clause := range clauses {
		cloned[i] = append([]int(nil), clause...)
	}
	return cloned
}

func cloneCNFTraceBuilder(builder *cnfBuilder) *cnfBuilder {
	cloned := *builder
	cloned.clauses = cloneCNFTraceClauses(builder.clauses)
	cloned.inputs = make(map[int]int, len(builder.inputs))
	for source, variable := range builder.inputs {
		cloned.inputs[source] = variable
	}
	cloned.memo = make(map[cnfKey]int, len(builder.memo))
	for key, variable := range builder.memo {
		cloned.memo[key] = variable
	}
	cloned.gates = append([]cnfGate(nil), builder.gates...)
	return &cloned
}

func emittedCNFTraceClauses(builder *cnfBuilder, obligation []int) [][]int {
	emitted := cloneCNFTraceClauses(builder.clauses)
	final := make([]int, len(obligation))
	for i, edge := range obligation {
		final[i] = cnfLit(edge)
	}
	return append(emitted, final)
}

// The fixture deliberately allocates an input between two gates. Inputs and
// outputs share one allocation sequence, so a validator must not require all
// input variables to form a prefix.
func validCNFTraceFixture() (*cnfBuilder, []int, [][]int) {
	builder := newCNFBuilder()
	left := builder.variable(0)
	right := builder.variable(1)
	conjunction := builder.apply(opAnd, left, right)
	lateInput := builder.variable(2)
	selection := builder.ite(lateInput, conjunction, left^1)
	obligation := []int{conjunction, selection ^ 1, lateInput}
	return builder, obligation, emittedCNFTraceClauses(builder, obligation)
}

func TestValidateCNFTraceAcceptsProductionShapes(t *testing.T) {
	builder, obligation, emitted := validCNFTraceFixture()
	if err := validateCNFTrace(builder, obligation, emitted); err != nil {
		t.Fatalf("valid interleaved trace refused: %v", err)
	}

	inputOnly := newCNFBuilder()
	input := inputOnly.variable(7)
	inputObligation := []int{input, input, input ^ 1}
	if err := validateCNFTrace(inputOnly, inputObligation,
		emittedCNFTraceClauses(inputOnly, inputObligation)); err != nil {
		t.Fatalf("valid duplicate/complementary final literals refused: %v", err)
	}
}

func TestValidateCNFTraceAcceptsEveryGateKind(t *testing.T) {
	tests := []struct {
		name  string
		build func(*cnfBuilder) int
	}{
		{
			name: "and",
			build: func(builder *cnfBuilder) int {
				return builder.apply(opAnd, builder.variable(0), builder.variable(1))
			},
		},
		{
			name: "or",
			build: func(builder *cnfBuilder) int {
				return builder.apply(opOr, builder.variable(0), builder.variable(1))
			},
		},
		{
			name: "xor",
			build: func(builder *cnfBuilder) int {
				return builder.apply(opXor, builder.variable(0), builder.variable(1))
			},
		},
		{
			name: "ite",
			build: func(builder *cnfBuilder) int {
				return builder.ite(
					builder.variable(0), builder.variable(1), builder.variable(2))
			},
		},
		{
			name: "dependent and then xor",
			build: func(builder *cnfBuilder) int {
				left := builder.variable(0)
				right := builder.variable(1)
				conjunction := builder.apply(opAnd, left, right)
				return builder.apply(opXor, conjunction, left^1)
			},
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			builder := newCNFBuilder()
			output := test.build(builder)
			obligation := []int{output}
			if err := validateCNFTrace(builder, obligation,
				emittedCNFTraceClauses(builder, obligation)); err != nil {
				t.Fatalf("valid %s trace refused: %v", test.name, err)
			}
		})
	}
}

func TestValidateCNFTraceRefusesMalformedAllocationAndGates(t *testing.T) {
	tests := []struct {
		name   string
		mutate func(*cnfBuilder, []int, *[][]int)
	}{
		{
			name: "nil input allocation",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.inputs = nil
			},
		},
		{
			name: "negative input source key",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				variable := builder.inputs[0]
				delete(builder.inputs, 0)
				builder.inputs[-1] = variable
			},
		},
		{
			name: "zero input variable",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.inputs[0] = 0
			},
		},
		{
			name: "duplicate input variable",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.inputs[1] = builder.inputs[0]
			},
		},
		{
			name: "unaccounted allocation",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.variables++
			},
		},
		{
			name: "negative allocation count",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.variables = -1
			},
		},
		{
			name: "overflowing allocation count",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.variables = int(^uint(0) >> 1)
			},
		},
		{
			name: "clause budget exceeded",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.exceeded = true
			},
		},
		{
			name: "unknown gate operation",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[0].op = 99
			},
		},
		{
			name: "binary gate carries an else edge",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[0].z = 2
			},
		},
		{
			name: "commutative operands are not canonical",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[0].x, builder.gates[0].y =
					builder.gates[0].y, builder.gates[0].x
			},
		},
		{
			name: "false constant gate operand",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[0].x = bddFalse
			},
		},
		{
			name: "true constant gate operand",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[0].x = bddTrue
			},
		},
		{
			name: "negative gate operand",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[0].x = -2
			},
		},
		{
			name: "forward gate operand",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[0].y = 2 * builder.gates[0].out
			},
		},
		{
			name: "gate output collides with input",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[0].out = builder.inputs[1]
			},
		},
		{
			name: "gate outputs do not increase",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[1].out = builder.gates[0].out
			},
		},
		{
			name: "gate output outside allocation",
			mutate: func(builder *cnfBuilder, _ []int, _ *[][]int) {
				builder.gates[1].out = builder.variables + 1
			},
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			base, obligation, emitted := validCNFTraceFixture()
			builder := cloneCNFTraceBuilder(base)
			test.mutate(builder, obligation, &emitted)
			if err := validateCNFTrace(builder, obligation, emitted); err == nil {
				t.Fatal("malformed trace accepted")
			}
		})
	}
}

func TestValidateCNFTraceRefusesClauseDrift(t *testing.T) {
	tests := []struct {
		name   string
		mutate func(*cnfBuilder, []int, *[][]int)
	}{
		{
			name: "builder clause missing",
			mutate: func(builder *cnfBuilder, obligation []int, emitted *[][]int) {
				builder.clauses = builder.clauses[1:]
				*emitted = emittedCNFTraceClauses(builder, obligation)
			},
		},
		{
			name: "builder clause added",
			mutate: func(builder *cnfBuilder, obligation []int, emitted *[][]int) {
				builder.clauses = append(builder.clauses, []int{1})
				*emitted = emittedCNFTraceClauses(builder, obligation)
			},
		},
		{
			name: "builder clauses reordered",
			mutate: func(builder *cnfBuilder, obligation []int, emitted *[][]int) {
				builder.clauses[0], builder.clauses[1] =
					builder.clauses[1], builder.clauses[0]
				*emitted = emittedCNFTraceClauses(builder, obligation)
			},
		},
		{
			name: "builder literal polarity changed",
			mutate: func(builder *cnfBuilder, obligation []int, emitted *[][]int) {
				builder.clauses[0][0] = -builder.clauses[0][0]
				*emitted = emittedCNFTraceClauses(builder, obligation)
			},
		},
		{
			name: "builder zero literal",
			mutate: func(builder *cnfBuilder, obligation []int, emitted *[][]int) {
				builder.clauses[0][0] = 0
				*emitted = emittedCNFTraceClauses(builder, obligation)
			},
		},
		{
			name: "emitted gate clause missing",
			mutate: func(_ *cnfBuilder, _ []int, emitted *[][]int) {
				*emitted = append((*emitted)[:1], (*emitted)[2:]...)
			},
		},
		{
			name: "emitted gate clauses reordered",
			mutate: func(_ *cnfBuilder, _ []int, emitted *[][]int) {
				(*emitted)[0], (*emitted)[1] = (*emitted)[1], (*emitted)[0]
			},
		},
		{
			name: "emitted gate literal changed",
			mutate: func(_ *cnfBuilder, _ []int, emitted *[][]int) {
				(*emitted)[0][0] = -(*emitted)[0][0]
			},
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			base, obligation, emitted := validCNFTraceFixture()
			builder := cloneCNFTraceBuilder(base)
			test.mutate(builder, obligation, &emitted)
			if err := validateCNFTrace(builder, obligation, emitted); err == nil {
				t.Fatal("clause drift accepted")
			}
		})
	}
}

func TestValidateCNFTraceRefusesFinalObligationDrift(t *testing.T) {
	tests := []struct {
		name   string
		mutate func(*cnfBuilder, *[]int, *[][]int)
	}{
		{
			name: "empty obligation",
			mutate: func(_ *cnfBuilder, obligation *[]int, _ *[][]int) {
				*obligation = nil
			},
		},
		{
			name: "false constant obligation edge",
			mutate: func(_ *cnfBuilder, obligation *[]int, _ *[][]int) {
				(*obligation)[0] = bddFalse
			},
		},
		{
			name: "true constant obligation edge",
			mutate: func(_ *cnfBuilder, obligation *[]int, _ *[][]int) {
				(*obligation)[0] = bddTrue
			},
		},
		{
			name: "negative obligation edge",
			mutate: func(_ *cnfBuilder, obligation *[]int, _ *[][]int) {
				(*obligation)[0] = -2
			},
		},
		{
			name: "obligation edge outside allocation",
			mutate: func(builder *cnfBuilder, obligation *[]int, _ *[][]int) {
				(*obligation)[0] = 2 * (builder.variables + 1)
			},
		},
		{
			name: "final emitted clause missing",
			mutate: func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
				*emitted = (*emitted)[:len(*emitted)-1]
			},
		},
		{
			name: "extra emitted clause after final",
			mutate: func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
				*emitted = append(*emitted, []int{1})
			},
		},
		{
			name: "final emitted clause empty",
			mutate: func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
				(*emitted)[len(*emitted)-1] = nil
			},
		},
		{
			name: "final emitted literals reordered",
			mutate: func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
				final := (*emitted)[len(*emitted)-1]
				final[0], final[1] = final[1], final[0]
			},
		},
		{
			name: "final emitted polarity changed",
			mutate: func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
				final := (*emitted)[len(*emitted)-1]
				final[0] = -final[0]
			},
		},
		{
			name: "final emitted zero literal",
			mutate: func(_ *cnfBuilder, _ *[]int, emitted *[][]int) {
				(*emitted)[len(*emitted)-1][0] = 0
			},
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			base, baseObligation, emitted := validCNFTraceFixture()
			builder := cloneCNFTraceBuilder(base)
			obligation := append([]int(nil), baseObligation...)
			test.mutate(builder, &obligation, &emitted)
			if err := validateCNFTrace(builder, obligation, emitted); err == nil {
				t.Fatal("final-obligation drift accepted")
			}
		})
	}
}

func TestValidateCNFTraceInputErrorIsDeterministic(t *testing.T) {
	base, obligation, emitted := validCNFTraceFixture()
	builder := cloneCNFTraceBuilder(base)
	builder.inputs = map[int]int{-1: 1, -2: 2, -3: 4}

	var first string
	for i := 0; i < 64; i++ {
		err := validateCNFTrace(builder, obligation, emitted)
		if err == nil {
			t.Fatal("negative input source keys accepted")
		}
		if i == 0 {
			first = err.Error()
		} else if err.Error() != first {
			t.Fatalf("nondeterministic error: first %q, then %q", first, err)
		}
	}
}

func TestCNFTraceFixturePinsExpectedAllocation(t *testing.T) {
	builder, obligation, emitted := validCNFTraceFixture()
	if builder.variables != 5 {
		t.Fatalf("variables = %d, want 5", builder.variables)
	}
	if got, want := builder.inputs, map[int]int{0: 1, 1: 2, 2: 4}; !reflect.DeepEqual(got, want) {
		t.Fatalf("inputs = %v, want %v", got, want)
	}
	if got, want := []int{builder.gates[0].out, builder.gates[1].out}, []int{3, 5}; !reflect.DeepEqual(got, want) {
		t.Fatalf("gate outputs = %v, want %v", got, want)
	}
	if got, want := emitted[len(emitted)-1], []int{3, -5, 4}; !reflect.DeepEqual(got, want) {
		t.Fatalf("final clause = %v, want %v (obligation edges %v)", got, want, obligation)
	}
}
