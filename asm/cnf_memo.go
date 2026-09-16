package asm

import "fmt"

// validateCNFGateMemoHeader checks the fixed-size part of the builder's
// unique-table invariant. Exact coverage is checked by looking up every gate
// in stable creation order; no map traversal or proportional allocation is
// needed.
func validateCNFGateMemoHeader(builder *cnfBuilder) error {
	if builder == nil {
		return fmt.Errorf("builder is nil")
	}
	if builder.exceeded {
		return fmt.Errorf("builder exceeded its clause budget")
	}
	if builder.variables < 0 {
		return fmt.Errorf("negative variable count %d", builder.variables)
	}
	if len(builder.memo) != len(builder.gates) {
		return fmt.Errorf("gate memo has %d entries for %d recorded gates",
			len(builder.memo), len(builder.gates))
	}
	return nil
}

// validateCNFGateMemoEntry checks that one fresh-gate record is in the exact
// unique-table slot whose later lookup can return it. previousOutput makes the
// stable gate walk establish unique outputs as well as unique keys.
func validateCNFGateMemoEntry(builder *cnfBuilder, index int, gate cnfGate, previousOutput int) error {
	if gate.out < 1 || gate.out > builder.variables {
		return fmt.Errorf("gate %d output %d is outside 1..%d",
			index, gate.out, builder.variables)
	}
	if gate.out <= previousOutput {
		return fmt.Errorf("gate %d output %d does not follow output %d",
			index, gate.out, previousOutput)
	}
	key, err := cnfGateMemoKey(index, gate)
	if err != nil {
		return err
	}
	output, present := builder.memo[key]
	if !present {
		return fmt.Errorf("gate %d has no exact unique-table entry", index)
	}
	if output != gate.out {
		return fmt.Errorf("gate %d unique-table output is %d, want %d",
			index, output, gate.out)
	}
	return nil
}

// cnfGateMemoKey derives the key used by cnfBuilder.apply/ite and rejects
// shapes those functions must have folded instead of recording. Binary gate
// records leave z at zero, while their memo key deliberately uses z=-1.
func cnfGateMemoKey(index int, gate cnfGate) (cnfKey, error) {
	operand := func(name string, edge int) error {
		if edge < 2 {
			return fmt.Errorf("gate %d %s edge %d should have been folded",
				index, name, edge)
		}
		if edge>>1 >= gate.out {
			return fmt.Errorf("gate %d %s variable %d does not precede output %d",
				index, name, edge>>1, gate.out)
		}
		return nil
	}

	switch gate.op {
	case opAnd, opOr, opXor:
		if gate.z != 0 {
			return cnfKey{}, fmt.Errorf("binary gate %d has nonzero unused edge z=%d",
				index, gate.z)
		}
		if gate.x > gate.y {
			return cnfKey{}, fmt.Errorf("binary gate %d operands are not in canonical edge order: %d > %d",
				index, gate.x, gate.y)
		}
		if err := operand("left operand", gate.x); err != nil {
			return cnfKey{}, err
		}
		if err := operand("right operand", gate.y); err != nil {
			return cnfKey{}, err
		}
		if gate.x == gate.y {
			return cnfKey{}, fmt.Errorf("binary gate %d has identical operands that should have been folded", index)
		}
		if gate.x^1 == gate.y {
			return cnfKey{}, fmt.Errorf("binary gate %d has complementary operands that should have been folded", index)
		}
		return cnfKey{op: gate.op, x: gate.x, y: gate.y, z: -1}, nil
	case cnfIte:
		if err := operand("condition", gate.x); err != nil {
			return cnfKey{}, err
		}
		if err := operand("then operand", gate.y); err != nil {
			return cnfKey{}, err
		}
		if err := operand("else operand", gate.z); err != nil {
			return cnfKey{}, err
		}
		if gate.y == gate.z {
			return cnfKey{}, fmt.Errorf("ITE gate %d has equal arms that should have been folded", index)
		}
		return cnfKey{op: cnfIte, x: gate.x, y: gate.y, z: gate.z}, nil
	default:
		return cnfKey{}, fmt.Errorf("gate %d has unknown operation %d", index, gate.op)
	}
}

func validateCNFGateMemo(builder *cnfBuilder) error {
	if err := validateCNFGateMemoHeader(builder); err != nil {
		return err
	}
	lastOutput := 0
	for index, gate := range builder.gates {
		if err := validateCNFGateMemoEntry(builder, index, gate, lastOutput); err != nil {
			return err
		}
		lastOutput = gate.out
	}
	return nil
}

// validateSettledCNFObligation runs both audits needed by a path with no
// emitted clause trace. Pending paths check the gate memo inside their
// existing validateCNFTrace gate walk instead.
func validateSettledCNFObligation(bl *blaster, traps []*term, claim *term,
	outcome cnfObligationOutcome, obligation []int) error {
	if outcome == cnfObligationFormula {
		return fmt.Errorf("pending outcome passed to the settled CNF audit")
	}
	if err := validateCNFObligation(bl, traps, claim, outcome, obligation); err != nil {
		return err
	}
	if err := validateCNFGateMemo(bl.cnf); err != nil {
		return fmt.Errorf("gate memo: %w", err)
	}
	return nil
}
