package optir

import (
	"fmt"
	"sort"
)

// RegisterColoring is a target-neutral assignment of live SSA values to a
// finite set of integer colors. A target gives the colors physical meaning;
// OptIR only proves that interfering values never share one.
type RegisterColoring struct {
	Colors       map[ValueID]int
	Interference map[ValueID][]ValueID
	LiveIn       map[BlockID][]ValueID
	LiveOut      map[BlockID][]ValueID
}

const (
	maxColoringBlocks = 1 << 14
	maxColoringValues = 1 << 16
)

// ColorRegisters computes SSA liveness, constructs the interference graph,
// and deterministically colors it from pool. Fixed precolors ABI values such
// as entry parameters. Unit values consume no color. Failure is ordinary
// target-pressure refusal; the caller keeps another implementation candidate.
func ColorRegisters(cfg CFG, pool []int, fixed map[ValueID]int) (RegisterColoring, error) {
	if err := Verify(cfg); err != nil {
		return RegisterColoring{}, err
	}
	if len(cfg.Blocks) > maxColoringBlocks {
		return RegisterColoring{}, fmt.Errorf("optir: register coloring refuses %d blocks (limit %d)", len(cfg.Blocks), maxColoringBlocks)
	}
	types := cfgValueTypes(cfg)
	if len(types) > maxColoringValues {
		return RegisterColoring{}, fmt.Errorf("optir: register coloring refuses %d values (limit %d)", len(types), maxColoringValues)
	}
	colors := normalizedColors(pool)
	if len(colors) == 0 {
		return RegisterColoring{}, fmt.Errorf("optir: register coloring has no colors")
	}
	allowed := map[int]bool{}
	for _, color := range colors {
		allowed[color] = true
	}
	for value, color := range fixed {
		typ, exists := types[value]
		if !exists {
			return RegisterColoring{}, fmt.Errorf("optir: fixed color names undefined value %d", value)
		}
		if typ == Type("()") {
			return RegisterColoring{}, fmt.Errorf("optir: unit value %d cannot be precolored", value)
		}
		if !allowed[color] {
			return RegisterColoring{}, fmt.Errorf("optir: fixed color %d of value %d is outside the pool", color, value)
		}
	}

	blockIndex := make(map[BlockID]int, len(cfg.Blocks))
	for index, block := range cfg.Blocks {
		blockIndex[block.ID] = index
	}
	uses := make([]map[ValueID]bool, len(cfg.Blocks))
	defs := make([]map[ValueID]bool, len(cfg.Blocks))
	liveIn := make([]map[ValueID]bool, len(cfg.Blocks))
	liveOut := make([]map[ValueID]bool, len(cfg.Blocks))
	for index, block := range cfg.Blocks {
		uses[index], defs[index] = map[ValueID]bool{}, map[ValueID]bool{}
		liveIn[index], liveOut[index] = map[ValueID]bool{}, map[ValueID]bool{}
		define := func(value ValueID) {
			if types[value] != Type("()") {
				defs[index][value] = true
			}
		}
		use := func(value ValueID) {
			if types[value] != Type("()") && !defs[index][value] {
				uses[index][value] = true
			}
		}
		for _, parameter := range block.Parameters {
			define(parameter.ID)
		}
		for _, operation := range block.Operations {
			for _, operand := range operation.Operands {
				use(operand)
			}
			for _, result := range operation.Results {
				define(result.ID)
			}
		}
		for _, value := range terminatorUses(block.Terminator) {
			use(value)
		}
	}

	// The equations are monotone over a finite block×value domain. The
	// iteration cap is defensive; a valid implementation reaches a fixed
	// point before one bit can be added twice.
	limit := max(1, len(cfg.Blocks)*max(1, len(types))+1)
	for iteration := 0; ; iteration++ {
		if iteration > limit {
			return RegisterColoring{}, fmt.Errorf("optir: register liveness did not converge")
		}
		changed := false
		for index := len(cfg.Blocks) - 1; index >= 0; index-- {
			block := cfg.Blocks[index]
			out := map[ValueID]bool{}
			for _, edge := range coloringEdges(block.Terminator) {
				for value := range liveIn[blockIndex[edge.Target]] {
					out[value] = true
				}
				// Edge arguments are simultaneous uses immediately before the
				// successor's parameter definitions.
				for _, value := range edge.Arguments {
					if types[value] != Type("()") {
						out[value] = true
					}
				}
			}
			in := cloneValueSet(uses[index])
			for value := range out {
				if !defs[index][value] {
					in[value] = true
				}
			}
			if !equalValueSet(in, liveIn[index]) || !equalValueSet(out, liveOut[index]) {
				liveIn[index], liveOut[index] = in, out
				changed = true
			}
		}
		if !changed {
			break
		}
	}

	graph := map[ValueID]map[ValueID]bool{}
	for value, typ := range types {
		if typ != Type("()") {
			graph[value] = map[ValueID]bool{}
		}
	}
	interfere := func(left, right ValueID) {
		if left == right || graph[left] == nil || graph[right] == nil {
			return
		}
		graph[left][right] = true
		graph[right][left] = true
	}
	defineAgainst := func(values []ValueID, live map[ValueID]bool) {
		for _, value := range values {
			delete(live, value)
		}
		for left, value := range values {
			for other := range live {
				interfere(value, other)
			}
			for _, other := range values[left+1:] {
				interfere(value, other)
			}
		}
	}
	for index, block := range cfg.Blocks {
		live := cloneValueSet(liveOut[index])
		for _, value := range terminatorUses(block.Terminator) {
			if graph[value] != nil {
				live[value] = true
			}
		}
		for operation := len(block.Operations) - 1; operation >= 0; operation-- {
			current := block.Operations[operation]
			results := make([]ValueID, 0, len(current.Results))
			for _, result := range current.Results {
				if graph[result.ID] != nil {
					results = append(results, result.ID)
				}
			}
			defineAgainst(results, live)
			for _, operand := range current.Operands {
				if graph[operand] != nil {
					live[operand] = true
				}
			}
		}
		parameters := make([]ValueID, 0, len(block.Parameters))
		for _, parameter := range block.Parameters {
			if graph[parameter.ID] != nil {
				parameters = append(parameters, parameter.ID)
			}
		}
		defineAgainst(parameters, live)
	}

	assignment := map[ValueID]int{}
	for value, color := range fixed {
		assignment[value] = color
	}
	for value, neighbors := range graph {
		for neighbor := range neighbors {
			left, leftFixed := assignment[value]
			right, rightFixed := assignment[neighbor]
			if value < neighbor && leftFixed && rightFixed && left == right {
				return RegisterColoring{}, fmt.Errorf("optir: fixed values %d and %d interfere in color %d", value, neighbor, left)
			}
		}
	}
	var open []ValueID
	for value := range graph {
		if _, fixed := assignment[value]; !fixed {
			open = append(open, value)
		}
	}
	sort.Slice(open, func(i, j int) bool {
		if len(graph[open[i]]) != len(graph[open[j]]) {
			return len(graph[open[i]]) > len(graph[open[j]])
		}
		return open[i] < open[j]
	})
	for _, value := range open {
		used := map[int]bool{}
		for neighbor := range graph[value] {
			if color, colored := assignment[neighbor]; colored {
				used[color] = true
			}
		}
		chosen, found := 0, false
		for _, color := range colors {
			if !used[color] {
				chosen, found = color, true
				break
			}
		}
		if !found {
			return RegisterColoring{}, fmt.Errorf("optir: no register color for value %d (%d live neighbors, %d colors)", value, len(graph[value]), len(colors))
		}
		assignment[value] = chosen
	}

	result := RegisterColoring{Colors: assignment, Interference: map[ValueID][]ValueID{}, LiveIn: map[BlockID][]ValueID{}, LiveOut: map[BlockID][]ValueID{}}
	for value, neighbors := range graph {
		for neighbor := range neighbors {
			result.Interference[value] = append(result.Interference[value], neighbor)
		}
		sort.Slice(result.Interference[value], func(i, j int) bool { return result.Interference[value][i] < result.Interference[value][j] })
	}
	for index, block := range cfg.Blocks {
		result.LiveIn[block.ID] = sortedValueSet(liveIn[index])
		result.LiveOut[block.ID] = sortedValueSet(liveOut[index])
	}
	return result, nil
}

func cfgValueTypes(cfg CFG) map[ValueID]Type {
	out := map[ValueID]Type{}
	for _, block := range cfg.Blocks {
		for _, parameter := range block.Parameters {
			out[parameter.ID] = parameter.Type
		}
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				out[result.ID] = result.Type
			}
		}
	}
	return out
}

func terminatorUses(terminator Terminator) []ValueID {
	var out []ValueID
	switch terminator.Kind {
	case TerminatorReturn:
		out = append(out, terminator.Values...)
	case TerminatorBranch:
		out = append(out, terminator.True.Arguments...)
	case TerminatorCondBranch:
		out = append(out, terminator.Condition)
		out = append(out, terminator.True.Arguments...)
		out = append(out, terminator.False.Arguments...)
	}
	return out
}

func coloringEdges(terminator Terminator) []Edge {
	switch terminator.Kind {
	case TerminatorBranch:
		return []Edge{terminator.True}
	case TerminatorCondBranch:
		return []Edge{terminator.True, terminator.False}
	}
	return nil
}

func normalizedColors(pool []int) []int {
	seen := map[int]bool{}
	var out []int
	for _, color := range pool {
		if color >= 0 && !seen[color] {
			seen[color] = true
			out = append(out, color)
		}
	}
	sort.Ints(out)
	return out
}

func cloneValueSet(input map[ValueID]bool) map[ValueID]bool {
	out := make(map[ValueID]bool, len(input))
	for value := range input {
		out[value] = true
	}
	return out
}

func equalValueSet(left, right map[ValueID]bool) bool {
	if len(left) != len(right) {
		return false
	}
	for value := range left {
		if !right[value] {
			return false
		}
	}
	return true
}

func sortedValueSet(values map[ValueID]bool) []ValueID {
	out := make([]ValueID, 0, len(values))
	for value := range values {
		out = append(out, value)
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}
