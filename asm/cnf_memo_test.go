package asm

import "testing"

func cnfMemoAuditFixture() (*cnfBuilder, cnfKey, cnfKey) {
	builder := newCNFBuilder()
	left := builder.variable(0)
	right := builder.variable(1)
	andEdge := builder.apply(opAnd, left, right)
	condition := builder.variable(2)
	builder.ite(condition, andEdge, left^1)
	return builder,
		cnfKey{op: opAnd, x: left, y: right, z: -1},
		cnfKey{op: cnfIte, x: condition, y: andEdge, z: left ^ 1}
}

func TestValidateCNFGateMemoAcceptsExactProductionKeys(t *testing.T) {
	builder, andKey, iteKey := cnfMemoAuditFixture()
	if got, want := builder.memo[andKey], 3; got != want {
		t.Fatalf("binary memo output = %d, want %d for z=-1 key", got, want)
	}
	if got, want := builder.memo[iteKey], 5; got != want {
		t.Fatalf("ITE memo output = %d, want %d in condition/then/else order", got, want)
	}
	if err := validateCNFGateMemo(builder); err != nil {
		t.Fatalf("valid gate memo refused: %v", err)
	}

	// Repeated requests are memo hits, not additional gate records.
	if got := builder.apply(opAnd, andKey.x, andKey.y); got != 2*builder.memo[andKey] {
		t.Fatalf("repeated AND = edge %d, want %d", got, 2*builder.memo[andKey])
	}
	if got := builder.ite(iteKey.x, iteKey.y, iteKey.z); got != 2*builder.memo[iteKey] {
		t.Fatalf("repeated ITE = edge %d, want %d", got, 2*builder.memo[iteKey])
	}
	if err := validateCNFGateMemo(builder); err != nil {
		t.Fatalf("valid memo hits changed the audit: %v", err)
	}

	inputOnly := newCNFBuilder()
	inputOnly.variable(7)
	if err := validateCNFGateMemo(inputOnly); err != nil {
		t.Fatalf("input-only builder refused: %v", err)
	}
}

func TestValidateCNFGateMemoAcceptsEveryGateKindAndFolds(t *testing.T) {
	builder := newCNFBuilder()
	left := builder.variable(0)
	right := builder.variable(1)
	third := builder.variable(2)
	builder.apply(opAnd, left, right)
	builder.apply(opOr, left, right)
	builder.apply(opXor, left, right)
	builder.ite(left, right, third)

	gates, memo := len(builder.gates), len(builder.memo)
	builder.apply(opAnd, left, left)
	builder.apply(opXor, left, left)
	builder.apply(opOr, left, left^1)
	builder.ite(bddTrue, left, right)
	builder.ite(left, right, right)
	if len(builder.gates) != gates || len(builder.memo) != memo {
		t.Fatalf("folds recorded gates/memo entries: gates %d->%d memo %d->%d",
			gates, len(builder.gates), memo, len(builder.memo))
	}
	// A constant ITE arm lowers to a binary gate; it must not leave a
	// foldable ITE record or use the ITE memo-key shape.
	builder.ite(left, bddFalse, right)
	if len(builder.gates) != gates+1 || len(builder.memo) != memo+1 ||
		builder.gates[len(builder.gates)-1].op != opAnd {
		t.Fatalf("constant-arm ITE did not lower to one AND gate: %#v", builder.gates)
	}
	if err := validateCNFGateMemo(builder); err != nil {
		t.Fatalf("valid gate family refused: %v", err)
	}
}

func TestValidateCNFGateMemoRefusesTableCorruption(t *testing.T) {
	tests := []struct {
		name   string
		mutate func(*cnfBuilder, cnfKey, cnfKey)
	}{
		{
			name: "missing entry",
			mutate: func(builder *cnfBuilder, andKey, _ cnfKey) {
				delete(builder.memo, andKey)
			},
		},
		{
			name: "extra entry",
			mutate: func(builder *cnfBuilder, _, _ cnfKey) {
				builder.memo[cnfKey{op: 99, x: 2, y: 4, z: -1}] = 99
			},
		},
		{
			name: "binary key uses recorded z",
			mutate: func(builder *cnfBuilder, andKey, _ cnfKey) {
				output := builder.memo[andKey]
				delete(builder.memo, andKey)
				andKey.z = 0
				builder.memo[andKey] = output
			},
		},
		{
			name: "binary operation substituted",
			mutate: func(builder *cnfBuilder, andKey, _ cnfKey) {
				output := builder.memo[andKey]
				delete(builder.memo, andKey)
				andKey.op = opOr
				builder.memo[andKey] = output
			},
		},
		{
			name: "binary operand polarity substituted",
			mutate: func(builder *cnfBuilder, andKey, _ cnfKey) {
				output := builder.memo[andKey]
				delete(builder.memo, andKey)
				andKey.x ^= 1
				builder.memo[andKey] = output
			},
		},
		{
			name: "memo output retargeted",
			mutate: func(builder *cnfBuilder, andKey, _ cnfKey) {
				builder.memo[andKey]++
			},
		},
		{
			name: "ITE arms reordered",
			mutate: func(builder *cnfBuilder, _, iteKey cnfKey) {
				output := builder.memo[iteKey]
				delete(builder.memo, iteKey)
				iteKey.y, iteKey.z = iteKey.z, iteKey.y
				builder.memo[iteKey] = output
			},
		},
		{
			name: "gate record operation drifted",
			mutate: func(builder *cnfBuilder, _, _ cnfKey) {
				builder.gates[0].op = opOr
			},
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			base, andKey, iteKey := cnfMemoAuditFixture()
			builder := cloneCNFTraceBuilder(base)
			test.mutate(builder, andKey, iteKey)
			if err := validateCNFGateMemo(builder); err == nil {
				t.Fatal("corrupt gate memo accepted")
			}
		})
	}
}

func cnfBuilderWithGateRecords(variables int, gates ...cnfGate) *cnfBuilder {
	builder := newCNFBuilder()
	builder.variables = variables
	builder.gates = append(builder.gates, gates...)
	for _, gate := range gates {
		key := cnfKey{op: gate.op, x: gate.x, y: gate.y, z: gate.z}
		if gate.op == opAnd || gate.op == opOr || gate.op == opXor {
			key.z = -1
		}
		builder.memo[key] = gate.out
	}
	return builder
}

func TestValidateCNFGateMemoRefusesNonFreshShapes(t *testing.T) {
	tests := []struct {
		name      string
		variables int
		gates     []cnfGate
	}{
		{"unknown operation", 3, []cnfGate{{op: 99, x: 2, y: 4, out: 3}}},
		{"binary recorded z", 3, []cnfGate{{op: opAnd, x: 2, y: 4, z: 6, out: 3}}},
		{"binary noncanonical operands", 3, []cnfGate{{op: opAnd, x: 4, y: 2, out: 3}}},
		{"binary false operand", 2, []cnfGate{{op: opAnd, x: 0, y: 2, out: 2}}},
		{"binary true operand", 2, []cnfGate{{op: opOr, x: 1, y: 2, out: 2}}},
		{"binary identical operands", 2, []cnfGate{{op: opXor, x: 2, y: 2, out: 2}}},
		{"binary complementary operands", 2, []cnfGate{{op: opAnd, x: 2, y: 3, out: 2}}},
		{"ITE constant condition", 3, []cnfGate{{op: cnfIte, x: 1, y: 2, z: 4, out: 3}}},
		{"ITE constant then arm", 3, []cnfGate{{op: cnfIte, x: 2, y: 1, z: 4, out: 3}}},
		{"ITE constant else arm", 3, []cnfGate{{op: cnfIte, x: 2, y: 4, z: 0, out: 3}}},
		{"ITE equal arms", 3, []cnfGate{{op: cnfIte, x: 2, y: 4, z: 4, out: 3}}},
		{"forward operand", 3, []cnfGate{{op: opAnd, x: 2, y: 6, out: 3}}},
		{"zero output", 3, []cnfGate{{op: opAnd, x: 2, y: 4, out: 0}}},
		{"output outside allocation", 3, []cnfGate{{op: opAnd, x: 2, y: 4, out: 4}}},
		{"duplicate output", 3, []cnfGate{
			{op: opAnd, x: 2, y: 4, out: 3},
			{op: opOr, x: 2, y: 4, out: 3},
		}},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			builder := cnfBuilderWithGateRecords(test.variables, test.gates...)
			if err := validateCNFGateMemo(builder); err == nil {
				t.Fatal("non-fresh gate shape accepted")
			}
		})
	}
}

func TestValidateCNFAllocationRunsOnEverySettledOutcome(t *testing.T) {
	tests := []struct {
		name    string
		traps   []*term
		claim   *term
		outcome cnfObligationOutcome
	}{
		{"trap always", []*term{constTerm(1, 1)}, constTerm(1, 1), cnfObligationTrapAlways},
		{"claim false", []*term{constTerm(0, 1)}, constTerm(0, 1), cnfObligationClaimFalse},
		{"constant proven", []*term{constTerm(0, 1)}, constTerm(1, 1), cnfObligationConstantProven},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			bl := preparedCNFObligationBlaster(t, nil, test.traps, test.claim)
			left := bl.cnf.variable(100)
			right := bl.cnf.variable(101)
			bl.cnf.apply(opAnd, left, right)
			key := cnfKey{op: opAnd, x: left, y: right, z: -1}
			if err := validateSettledCNFObligation(bl, test.traps, test.claim,
				test.outcome, nil); err != nil {
				t.Fatalf("valid settled audit refused: %v", err)
			}

			rightInput := bl.cnf.inputs[101]
			bl.cnf.inputs[101] = bl.cnf.inputs[100]
			if err := validateSettledCNFObligation(bl, test.traps, test.claim,
				test.outcome, nil); err == nil {
				t.Fatal("settled outcome accepted aliased input allocations")
			}
			bl.cnf.inputs[101] = rightInput

			bl.cnf.memo[key]++
			if err := validateSettledCNFObligation(bl, test.traps, test.claim,
				test.outcome, nil); err == nil {
				t.Fatal("settled outcome accepted a corrupt gate memo")
			}
		})
	}
}

func TestValidateCNFTraceIncludesGateMemoAudit(t *testing.T) {
	builder, obligation, emitted := validCNFTraceFixture()
	builder.memo[cnfKey{op: opAnd, x: 2, y: 4, z: -1}]++
	if err := validateCNFTrace(builder, obligation, emitted); err == nil {
		t.Fatal("pending trace accepted a corrupt gate memo")
	}
}

func BenchmarkValidateCNFGateMemo(b *testing.B) {
	builder := newCNFBuilder()
	left := builder.variable(0)
	right := builder.variable(1)
	for i := 0; i < 4096; i++ {
		left, right = right, builder.apply(i%3, left, right)
	}
	if err := validateCNFGateMemo(builder); err != nil {
		b.Fatalf("benchmark fixture refused: %v", err)
	}
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if err := validateCNFGateMemo(builder); err != nil {
			b.Fatal(err)
		}
	}
}
