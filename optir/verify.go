package optir

import (
	"fmt"
	"sort"
)

type structuredChecker struct {
	types   map[ValueID]Type
	maximum ValueID
}

func validateStructured(function Function) (ValueID, error) {
	if function.Name == "" {
		return 0, fmt.Errorf("optir: function name is empty")
	}
	if len(function.Body.Arguments) != 0 {
		return 0, fmt.Errorf("optir: function body cannot declare region arguments")
	}
	checker := &structuredChecker{types: map[ValueID]Type{}}
	for _, parameter := range function.Parameters {
		if err := checker.define(parameter, "function parameter"); err != nil {
			return 0, err
		}
	}
	if err := checker.region(function.Body); err != nil {
		return 0, err
	}
	if err := checker.matchValues(function.Body.Yield, function.Results, "function return"); err != nil {
		return 0, err
	}
	return checker.maximum, nil
}

func (checker *structuredChecker) define(value Value, subject string) error {
	if value.ID == 0 {
		return fmt.Errorf("optir: %s has invalid value id 0", subject)
	}
	if value.Type == "" {
		return fmt.Errorf("optir: %s %d has no type", subject, value.ID)
	}
	if _, exists := checker.types[value.ID]; exists {
		return fmt.Errorf("optir: value %d is defined more than once", value.ID)
	}
	checker.types[value.ID] = value.Type
	if value.ID > checker.maximum {
		checker.maximum = value.ID
	}
	return nil
}

func (checker *structuredChecker) region(region Region) error {
	for _, argument := range region.Arguments {
		if err := checker.define(argument, "region argument"); err != nil {
			return err
		}
	}
	for _, node := range region.Nodes {
		members := 0
		if node.Operation != nil {
			members++
		}
		if node.If != nil {
			members++
		}
		if node.While != nil {
			members++
		}
		if members != 1 {
			return fmt.Errorf("optir: structured node must contain exactly one operation, if, or while")
		}
		switch {
		case node.Operation != nil:
			if node.Operation.Code == "" {
				return fmt.Errorf("optir: operation code is empty")
			}
			for _, result := range node.Operation.Results {
				if err := checker.define(result, "operation result"); err != nil {
					return err
				}
			}
		case node.If != nil:
			branch := node.If
			if checker.types[branch.Condition] != TypeBool {
				return fmt.Errorf("optir: if condition %d is not Bool", branch.Condition)
			}
			if len(branch.Then.Arguments) != 0 || len(branch.Else.Arguments) != 0 {
				return fmt.Errorf("optir: if regions capture dominating values and cannot declare arguments")
			}
			for _, result := range branch.Results {
				if err := checker.define(result, "if result"); err != nil {
					return err
				}
			}
			if err := checker.region(branch.Then); err != nil {
				return err
			}
			if err := checker.matchValues(branch.Then.Yield, valueTypes(branch.Results), "then yield"); err != nil {
				return err
			}
			if err := checker.region(branch.Else); err != nil {
				return err
			}
			if err := checker.matchValues(branch.Else.Yield, valueTypes(branch.Results), "else yield"); err != nil {
				return err
			}
		case node.While != nil:
			loop := node.While
			if len(loop.Initial) != len(loop.Results) || len(loop.Condition.Arguments) != len(loop.Results) || len(loop.Body.Arguments) != len(loop.Results) {
				return fmt.Errorf("optir: while initial, result, condition-argument, and body-argument arities differ")
			}
			for _, result := range loop.Results {
				if err := checker.define(result, "while result"); err != nil {
					return err
				}
			}
			resultTypes := valueTypes(loop.Results)
			if err := checker.matchValues(loop.Initial, resultTypes, "while initial values"); err != nil {
				return err
			}
			if err := checker.region(loop.Condition); err != nil {
				return err
			}
			if !sameTypes(valueTypes(loop.Condition.Arguments), resultTypes) {
				return fmt.Errorf("optir: while condition argument types differ from result types")
			}
			if err := checker.matchValues(loop.Condition.Yield, []Type{TypeBool}, "while condition yield"); err != nil {
				return err
			}
			if err := checker.region(loop.Body); err != nil {
				return err
			}
			if !sameTypes(valueTypes(loop.Body.Arguments), resultTypes) {
				return fmt.Errorf("optir: while body argument types differ from result types")
			}
			if err := checker.matchValues(loop.Body.Yield, resultTypes, "while body yield"); err != nil {
				return err
			}
		}
	}
	return nil
}

func (checker *structuredChecker) matchValues(values []ValueID, types []Type, subject string) error {
	if len(values) != len(types) {
		return fmt.Errorf("optir: %s has arity %d, want %d", subject, len(values), len(types))
	}
	for i, value := range values {
		actual, exists := checker.types[value]
		if !exists {
			return fmt.Errorf("optir: %s uses undefined value %d", subject, value)
		}
		if actual != types[i] {
			return fmt.Errorf("optir: %s value %d has type %s, want %s", subject, value, actual, types[i])
		}
	}
	return nil
}

func valueTypes(values []Value) []Type {
	out := make([]Type, len(values))
	for i, value := range values {
		out[i] = value.Type
	}
	return out
}

func sameTypes(left, right []Type) bool {
	if len(left) != len(right) {
		return false
	}
	for i := range left {
		if left[i] != right[i] {
			return false
		}
	}
	return true
}

type definition struct {
	typeOf Type
	block  BlockID
	index  int
}

// Verify checks the canonical CFG independently of the structured projector.
// Analyses and future transforms must fail closed when it refuses a graph.
func Verify(cfg CFG) error {
	if cfg.Name == "" {
		return fmt.Errorf("optir: CFG function name is empty")
	}
	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	definitions := map[ValueID]definition{}
	for i := range cfg.Blocks {
		block := &cfg.Blocks[i]
		if _, exists := blocks[block.ID]; exists {
			return fmt.Errorf("optir: block %d is defined more than once", block.ID)
		}
		blocks[block.ID] = block
		for _, parameter := range block.Parameters {
			if err := defineCFGValue(definitions, parameter, block.ID, -1); err != nil {
				return err
			}
		}
		for index, operation := range block.Operations {
			if operation.Code == "" {
				return fmt.Errorf("optir: block %d contains an operation with no code", block.ID)
			}
			for _, result := range operation.Results {
				if err := defineCFGValue(definitions, result, block.ID, index); err != nil {
					return err
				}
			}
		}
	}
	if _, exists := blocks[cfg.Entry]; !exists {
		return fmt.Errorf("optir: entry block %d does not exist", cfg.Entry)
	}

	predecessors := make(map[BlockID][]BlockID, len(blocks))
	for _, block := range cfg.Blocks {
		edges, err := terminatorEdges(block.Terminator)
		if err != nil {
			return fmt.Errorf("optir: block %d: %w", block.ID, err)
		}
		for _, edge := range edges {
			target, exists := blocks[edge.Target]
			if !exists {
				return fmt.Errorf("optir: block %d branches to missing block %d", block.ID, edge.Target)
			}
			if len(edge.Arguments) != len(target.Parameters) {
				return fmt.Errorf("optir: edge %d -> %d has %d arguments, want %d", block.ID, edge.Target, len(edge.Arguments), len(target.Parameters))
			}
			for i, argument := range edge.Arguments {
				defined, exists := definitions[argument]
				if !exists {
					return fmt.Errorf("optir: edge %d -> %d uses undefined value %d", block.ID, edge.Target, argument)
				}
				if defined.typeOf != target.Parameters[i].Type {
					return fmt.Errorf("optir: edge %d -> %d argument %d has type %s, want %s", block.ID, edge.Target, argument, defined.typeOf, target.Parameters[i].Type)
				}
			}
			predecessors[edge.Target] = append(predecessors[edge.Target], block.ID)
		}
	}

	reachable := reachableBlocks(cfg.Entry, blocks)
	if len(reachable) != len(blocks) {
		return fmt.Errorf("optir: CFG contains unreachable blocks")
	}
	dominators := computeDominators(cfg.Entry, reachable, predecessors)
	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			for _, operand := range operation.Operands {
				if err := verifyUse(operand, block.ID, index, definitions, dominators); err != nil {
					return fmt.Errorf("optir: operation %s: %w", operation.Code, err)
				}
			}
			for _, fact := range operation.Facts {
				for _, value := range fact.Values {
					if err := verifyUse(value, block.ID, index+1, definitions, dominators); err != nil {
						return fmt.Errorf("optir: operation fact %s: %w", fact.Name, err)
					}
				}
			}
		}
		terminatorIndex := len(block.Operations)
		switch block.Terminator.Kind {
		case TerminatorReturn:
			if len(block.Terminator.Values) != len(cfg.Results) {
				return fmt.Errorf("optir: block %d returns %d values, want %d", block.ID, len(block.Terminator.Values), len(cfg.Results))
			}
			for i, value := range block.Terminator.Values {
				if err := verifyUse(value, block.ID, terminatorIndex, definitions, dominators); err != nil {
					return err
				}
				if definitions[value].typeOf != cfg.Results[i] {
					return fmt.Errorf("optir: return value %d has type %s, want %s", value, definitions[value].typeOf, cfg.Results[i])
				}
			}
		case TerminatorBranch:
			for _, value := range block.Terminator.True.Arguments {
				if err := verifyUse(value, block.ID, terminatorIndex, definitions, dominators); err != nil {
					return err
				}
			}
		case TerminatorCondBranch:
			if err := verifyUse(block.Terminator.Condition, block.ID, terminatorIndex, definitions, dominators); err != nil {
				return err
			}
			if definitions[block.Terminator.Condition].typeOf != TypeBool {
				return fmt.Errorf("optir: block %d condition %d is not Bool", block.ID, block.Terminator.Condition)
			}
			for _, edge := range []Edge{block.Terminator.True, block.Terminator.False} {
				for _, value := range edge.Arguments {
					if err := verifyUse(value, block.ID, terminatorIndex, definitions, dominators); err != nil {
						return err
					}
				}
			}
		}
	}
	for _, fact := range cfg.Facts {
		for _, value := range fact.Values {
			if _, exists := definitions[value]; !exists {
				return fmt.Errorf("optir: function fact %s uses undefined value %d", fact.Name, value)
			}
		}
	}
	return nil
}

func defineCFGValue(definitions map[ValueID]definition, value Value, block BlockID, index int) error {
	if value.ID == 0 || value.Type == "" {
		return fmt.Errorf("optir: invalid value definition in block %d", block)
	}
	if _, exists := definitions[value.ID]; exists {
		return fmt.Errorf("optir: value %d is defined more than once", value.ID)
	}
	definitions[value.ID] = definition{typeOf: value.Type, block: block, index: index}
	return nil
}

func terminatorEdges(terminator Terminator) ([]Edge, error) {
	switch terminator.Kind {
	case TerminatorReturn:
		return nil, nil
	case TerminatorBranch:
		return []Edge{terminator.True}, nil
	case TerminatorCondBranch:
		return []Edge{terminator.True, terminator.False}, nil
	default:
		return nil, fmt.Errorf("missing or invalid terminator")
	}
}

func reachableBlocks(entry BlockID, blocks map[BlockID]*Block) map[BlockID]bool {
	reachable := map[BlockID]bool{}
	work := []BlockID{entry}
	for len(work) > 0 {
		id := work[len(work)-1]
		work = work[:len(work)-1]
		if reachable[id] {
			continue
		}
		reachable[id] = true
		edges, _ := terminatorEdges(blocks[id].Terminator)
		for _, edge := range edges {
			if _, exists := blocks[edge.Target]; exists {
				work = append(work, edge.Target)
			}
		}
	}
	return reachable
}

func computeDominators(entry BlockID, reachable map[BlockID]bool, predecessors map[BlockID][]BlockID) map[BlockID]map[BlockID]bool {
	ids := make([]int, 0, len(reachable))
	for id := range reachable {
		ids = append(ids, int(id))
	}
	sort.Ints(ids)
	dominators := make(map[BlockID]map[BlockID]bool, len(ids))
	for _, raw := range ids {
		id := BlockID(raw)
		dominators[id] = map[BlockID]bool{}
		if id == entry {
			dominators[id][id] = true
			continue
		}
		for _, all := range ids {
			dominators[id][BlockID(all)] = true
		}
	}
	changed := true
	for changed {
		changed = false
		for _, raw := range ids {
			id := BlockID(raw)
			if id == entry {
				continue
			}
			next := map[BlockID]bool{id: true}
			if len(predecessors[id]) > 0 {
				for candidate := range dominators[predecessors[id][0]] {
					present := true
					for _, predecessor := range predecessors[id][1:] {
						present = present && dominators[predecessor][candidate]
					}
					if present {
						next[candidate] = true
					}
				}
			}
			if !sameBlockSet(next, dominators[id]) {
				dominators[id] = next
				changed = true
			}
		}
	}
	return dominators
}

func sameBlockSet(left, right map[BlockID]bool) bool {
	if len(left) != len(right) {
		return false
	}
	for id := range left {
		if !right[id] {
			return false
		}
	}
	return true
}

func verifyUse(value ValueID, block BlockID, index int, definitions map[ValueID]definition, dominators map[BlockID]map[BlockID]bool) error {
	defined, exists := definitions[value]
	if !exists {
		return fmt.Errorf("value %d is undefined", value)
	}
	if defined.block == block {
		if defined.index >= index {
			return fmt.Errorf("value %d is used before its definition in block %d", value, block)
		}
		return nil
	}
	if !dominators[block][defined.block] {
		return fmt.Errorf("value %d from block %d does not dominate block %d", value, defined.block, block)
	}
	return nil
}
