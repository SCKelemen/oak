package asm

import "fmt"

type cnfTraceClause struct {
	literals [3]int
	length   int
}

type cnfTraceGateClauses struct {
	clauses [6]cnfTraceClause
	length  int
}

// validateCNFAllocation checks that inputs and gates form one injective,
// disjoint, dense allocation of 1..variables.  It is separate from clause
// replay because settled obligations emit no final clause trace but still
// depend on the producer's input and gate roots being distinct.
func validateCNFAllocation(builder *cnfBuilder) ([]byte, error) {
	if err := validateCNFGateMemoHeader(builder); err != nil {
		return nil, err
	}
	// Check the allocation count before adding lengths or allocating storage.
	// Once this equality holds, occupied is proportional to collections the
	// completed builder already owns.
	if len(builder.inputs) > builder.variables ||
		len(builder.gates) != builder.variables-len(builder.inputs) {
		return nil, fmt.Errorf("allocator records %d inputs and %d gates for %d variables",
			len(builder.inputs), len(builder.gates), builder.variables)
	}
	for source := range builder.inputs {
		if source < 0 {
			return nil, fmt.Errorf("an input source index is negative")
		}
	}
	for _, variable := range builder.inputs {
		if variable < 1 || variable > builder.variables {
			return nil, fmt.Errorf("an input variable is outside the allocated range")
		}
	}

	occupied := make([]byte, builder.variables)
	for _, variable := range builder.inputs {
		if occupied[variable-1] != 0 {
			return nil, fmt.Errorf("two input sources share one allocated variable")
		}
		occupied[variable-1] = 1
	}
	lastOutput := 0
	for index, gate := range builder.gates {
		if err := validateCNFGateMemoEntry(builder, index, gate, lastOutput); err != nil {
			return nil, err
		}
		if occupied[gate.out-1] != 0 {
			return nil, fmt.Errorf("gate %d output %d is already allocated", index, gate.out)
		}
		occupied[gate.out-1] = 2
		lastOutput = gate.out
	}
	for variable, kind := range occupied {
		if kind == 0 {
			return nil, fmt.Errorf("allocated variable %d is unaccounted for", variable+1)
		}
	}
	return occupied, nil
}

// validateCNFTrace independently reconstructs the concrete clauses described
// by a completed builder trace. It deliberately does not call the builder's
// gate or clause helpers: a drift between the recorded gates and emitted CNF
// must refuse the export before any counts or DIMACS text become authoritative.
func validateCNFTrace(builder *cnfBuilder, obligation []int, emitted [][]int) error {
	if err := validateCNFGateMemoHeader(builder); err != nil {
		return err
	}
	if len(builder.clauses) > cnfClauseBudget {
		return fmt.Errorf("builder has %d clauses above its budget of %d",
			len(builder.clauses), cnfClauseBudget)
	}
	if len(emitted) == 0 || len(emitted)-1 != len(builder.clauses) {
		return fmt.Errorf("emitted clauses do not contain exactly the gate clauses and one final clause")
	}
	occupied, err := validateCNFAllocation(builder)
	if err != nil {
		return err
	}

	// Compare each fixed-size reconstruction as it is produced. This keeps the
	// validator's additional memory independent of the number of clauses.
	cursor := 0
	for index, gate := range builder.gates {
		expected, err := traceGateClauses(index, gate, occupied)
		if err != nil {
			return err
		}
		for clause := 0; clause < expected.length; clause++ {
			if cursor >= len(builder.clauses) {
				return fmt.Errorf("builder gate clauses end before gate %d clause %d", index, clause)
			}
			if err := sameTraceClause("builder gate", cursor,
				builder.clauses[cursor], expected.clauses[clause]); err != nil {
				return err
			}
			if err := sameTraceClause("emitted gate", cursor,
				emitted[cursor], expected.clauses[clause]); err != nil {
				return err
			}
			cursor++
		}
	}
	if cursor != len(builder.clauses) {
		return fmt.Errorf("builder has %d trailing gate clauses", len(builder.clauses)-cursor)
	}

	if len(obligation) == 0 {
		return fmt.Errorf("final obligation is empty")
	}
	final := emitted[len(emitted)-1]
	if len(final) != len(obligation) {
		return fmt.Errorf("final clause has %d literals, want %d", len(final), len(obligation))
	}
	for index, edge := range obligation {
		literal, err := traceLiteral(edge, occupied)
		if err != nil {
			return fmt.Errorf("final obligation edge %d: %w", index, err)
		}
		if final[index] != literal {
			return fmt.Errorf("final clause literal %d is %d, want %d",
				index, final[index], literal)
		}
	}
	return nil
}

func traceGateClauses(index int, gate cnfGate, occupied []byte) (cnfTraceGateClauses, error) {
	var result cnfTraceGateClauses
	switch gate.op {
	case opAnd, opOr, opXor:
		if gate.z != 0 {
			return result, fmt.Errorf("binary gate %d has nonzero unused edge z=%d", index, gate.z)
		}
		if gate.x > gate.y {
			return result, fmt.Errorf("binary gate %d operands are not in canonical edge order: %d > %d",
				index, gate.x, gate.y)
		}
		left, err := traceGateOperand(index, "left operand", gate.x, gate.out, occupied)
		if err != nil {
			return result, err
		}
		right, err := traceGateOperand(index, "right operand", gate.y, gate.out, occupied)
		if err != nil {
			return result, err
		}
		switch gate.op {
		case opAnd:
			result.length = 3
			result.clauses[0] = traceClause2(-gate.out, left)
			result.clauses[1] = traceClause2(-gate.out, right)
			result.clauses[2] = traceClause3(gate.out, -left, -right)
		case opOr:
			result.length = 3
			result.clauses[0] = traceClause2(gate.out, -left)
			result.clauses[1] = traceClause2(gate.out, -right)
			result.clauses[2] = traceClause3(-gate.out, left, right)
		case opXor:
			result.length = 4
			result.clauses[0] = traceClause3(-gate.out, left, right)
			result.clauses[1] = traceClause3(-gate.out, -left, -right)
			result.clauses[2] = traceClause3(gate.out, -left, right)
			result.clauses[3] = traceClause3(gate.out, left, -right)
		}
	case cnfIte:
		condition, err := traceGateOperand(index, "condition", gate.x, gate.out, occupied)
		if err != nil {
			return result, err
		}
		thenValue, err := traceGateOperand(index, "then operand", gate.y, gate.out, occupied)
		if err != nil {
			return result, err
		}
		elseValue, err := traceGateOperand(index, "else operand", gate.z, gate.out, occupied)
		if err != nil {
			return result, err
		}
		result.length = 6
		result.clauses[0] = traceClause3(-gate.out, -condition, thenValue)
		result.clauses[1] = traceClause3(-gate.out, condition, elseValue)
		result.clauses[2] = traceClause3(gate.out, -condition, -thenValue)
		result.clauses[3] = traceClause3(gate.out, condition, -elseValue)
		result.clauses[4] = traceClause3(-gate.out, thenValue, elseValue)
		result.clauses[5] = traceClause3(gate.out, -thenValue, -elseValue)
	default:
		return result, fmt.Errorf("gate %d has unknown operation %d", index, gate.op)
	}
	return result, nil
}

func traceGateOperand(index int, name string, edge, output int, occupied []byte) (int, error) {
	literal, err := traceLiteral(edge, occupied)
	if err != nil {
		return 0, fmt.Errorf("gate %d %s: %w", index, name, err)
	}
	if edge>>1 >= output {
		return 0, fmt.Errorf("gate %d %s variable %d does not precede output %d",
			index, name, edge>>1, output)
	}
	return literal, nil
}

// traceLiteral is intentionally separate from cnfLit, whose output this
// validator checks. Constants are not DIMACS literals at this boundary.
func traceLiteral(edge int, occupied []byte) (int, error) {
	if edge < 2 {
		return 0, fmt.Errorf("edge %d is a Boolean constant, not a DIMACS literal", edge)
	}
	variable := edge >> 1
	if variable < 1 || variable > len(occupied) || occupied[variable-1] == 0 {
		return 0, fmt.Errorf("edge %d names an unallocated variable", edge)
	}
	if edge&1 != 0 {
		return -variable, nil
	}
	return variable, nil
}

func traceClause2(first, second int) cnfTraceClause {
	return cnfTraceClause{literals: [3]int{first, second}, length: 2}
}

func traceClause3(first, second, third int) cnfTraceClause {
	return cnfTraceClause{literals: [3]int{first, second, third}, length: 3}
}

func sameTraceClause(label string, index int, got []int, want cnfTraceClause) error {
	if len(got) != want.length {
		return fmt.Errorf("%s clause %d has %d literals, want %d",
			label, index, len(got), want.length)
	}
	for literal := 0; literal < want.length; literal++ {
		if got[literal] != want.literals[literal] {
			return fmt.Errorf("%s clause %d literal %d is %d, want %d",
				label, index, literal, got[literal], want.literals[literal])
		}
	}
	return nil
}
