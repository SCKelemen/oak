package optir

import (
	"fmt"
	"sort"
)

// BlockParameterCongruenceReport records phi-like block parameters whose
// incoming values all denote one dominating SSA definition. Replacements are
// sorted by eliminated ValueID and resolve transitively to definitions that
// remain in the returned CFG.
type BlockParameterCongruenceReport struct {
	EliminatedParameters int
	Replacements         []ValueReplacement
}

// EliminateCongruentBlockParameters removes only trivial phi-like block
// parameters. Every incoming edge must supply either one identical dominating
// definition or the parameter itself on a loop backedge. Ignoring the latter
// is the standard loop-invariant phi rule: at least one non-self incoming value
// is required, so an ungrounded self-cycle is never removed.
//
// One parameter is removed per bounded iteration. This keeps positional edge
// edits simple and makes chained loop parameters converge without trusting a
// stale index. The caller's CFG is unchanged, and both input and output are
// independently verified.
func EliminateCongruentBlockParameters(cfg CFG) (CFG, BlockParameterCongruenceReport, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return CFG{}, BlockParameterCongruenceReport{}, err
	}

	result := cloneCFG(cfg)
	maximumEliminations := 0
	maximumInt := int(^uint(0) >> 1)
	for _, block := range result.Blocks {
		if len(block.Parameters) > maximumInt-maximumEliminations {
			return CFG{}, BlockParameterCongruenceReport{}, fmt.Errorf("optir: block parameter count overflows iteration bound")
		}
		maximumEliminations += len(block.Parameters)
	}

	replacements := make(map[ValueID]ValueID, maximumEliminations)
	report := BlockParameterCongruenceReport{}
	for iteration := 0; iteration < maximumEliminations; iteration++ {
		definitions, predecessors := transformGraphInfo(result)
		reachable := make(map[BlockID]bool, len(result.Blocks))
		blocks := make(map[BlockID]*Block, len(result.Blocks))
		for index := range result.Blocks {
			block := &result.Blocks[index]
			reachable[block.ID] = true
			blocks[block.ID] = block
		}
		dominators := computeDominators(result.Entry, reachable, predecessors)

		removed := false
		for _, blockID := range sortedBlockIDs(blocks) {
			// Entry parameters also have conceptual incoming values from the
			// function ABI. CFG predecessor edges describe only backedges, so
			// they are not a complete phi input set and cannot justify replacing
			// an entry parameter.
			if blockID == result.Entry {
				continue
			}
			block := blocks[blockID]
			for parameterIndex, parameter := range block.Parameters {
				candidate, ok, err := congruentBlockParameterCandidate(
					result, block.ID, parameterIndex, parameter, definitions, dominators, replacements,
				)
				if err != nil {
					return CFG{}, BlockParameterCongruenceReport{}, err
				}
				if !ok {
					continue
				}
				if err := removeCongruentBlockParameter(&result, block.ID, parameterIndex, parameter.ID, candidate); err != nil {
					return CFG{}, BlockParameterCongruenceReport{}, err
				}
				replacements[parameter.ID] = candidate
				report.Replacements = append(report.Replacements, ValueReplacement{From: parameter.ID, To: candidate})
				report.EliminatedParameters++
				removed = true
				break
			}
			if removed {
				break
			}
		}
		if !removed {
			break
		}
	}

	for index := range report.Replacements {
		resolved, ok := resolveReplacementBounded(report.Replacements[index].To, replacements, maximumEliminations)
		if !ok {
			return CFG{}, BlockParameterCongruenceReport{}, fmt.Errorf("optir: block parameter replacement cycle")
		}
		report.Replacements[index].To = resolved
	}
	sort.Slice(report.Replacements, func(i, j int) bool {
		return report.Replacements[i].From < report.Replacements[j].From
	})
	if err := validateAnalysisCFG(result); err != nil {
		return CFG{}, BlockParameterCongruenceReport{}, fmt.Errorf("optir: block parameter congruence produced invalid CFG: %w", err)
	}
	return result, report, nil
}

func congruentBlockParameterCandidate(
	cfg CFG,
	blockID BlockID,
	parameterIndex int,
	parameter Value,
	definitions map[ValueID]definition,
	dominators map[BlockID]map[BlockID]bool,
	replacements map[ValueID]ValueID,
) (ValueID, bool, error) {
	if parameterIndex < 0 {
		return 0, false, fmt.Errorf("optir: negative block parameter index")
	}
	incoming, err := incomingBlockParameterValues(cfg, blockID, parameterIndex)
	if err != nil {
		return 0, false, err
	}
	var candidate ValueID
	resolutionLimit := len(replacements)
	if resolutionLimit == int(^uint(0)>>1) {
		return 0, false, fmt.Errorf("optir: block parameter replacement count overflows resolution bound")
	}
	resolutionLimit++
	for _, value := range incoming {
		resolved, ok := resolveReplacementBounded(value, replacements, resolutionLimit)
		if !ok {
			return 0, false, fmt.Errorf("optir: block parameter replacement cycle")
		}
		if resolved == parameter.ID {
			continue
		}
		if candidate == 0 {
			candidate = resolved
			continue
		}
		if candidate != resolved {
			return 0, false, nil
		}
	}
	if candidate == 0 {
		return 0, false, nil
	}
	definition, exists := definitions[candidate]
	if !exists || definition.typeOf != parameter.Type || !definitionDominatesBlockEntry(definition, blockID, dominators) {
		return 0, false, nil
	}
	return candidate, true, nil
}

func incomingBlockParameterValues(cfg CFG, target BlockID, parameterIndex int) ([]ValueID, error) {
	values := make([]ValueID, 0)
	for blockIndex := range cfg.Blocks {
		terminator := &cfg.Blocks[blockIndex].Terminator
		switch terminator.Kind {
		case TerminatorBranch:
			if terminator.True.Target == target {
				if parameterIndex >= len(terminator.True.Arguments) {
					return nil, fmt.Errorf("optir: edge %d -> %d has no block parameter argument %d", cfg.Blocks[blockIndex].ID, target, parameterIndex)
				}
				values = append(values, terminator.True.Arguments[parameterIndex])
			}
		case TerminatorCondBranch:
			for _, edge := range []Edge{terminator.True, terminator.False} {
				if edge.Target != target {
					continue
				}
				if parameterIndex >= len(edge.Arguments) {
					return nil, fmt.Errorf("optir: edge %d -> %d has no block parameter argument %d", cfg.Blocks[blockIndex].ID, target, parameterIndex)
				}
				values = append(values, edge.Arguments[parameterIndex])
			}
		}
	}
	return values, nil
}

func definitionDominatesBlockEntry(definition definition, block BlockID, dominators map[BlockID]map[BlockID]bool) bool {
	if definition.block == block {
		return definition.index == -1
	}
	return dominators[block][definition.block]
}

func removeCongruentBlockParameter(cfg *CFG, target BlockID, parameterIndex int, parameter, candidate ValueID) error {
	if parameter == 0 || candidate == 0 || parameter == candidate {
		return fmt.Errorf("optir: invalid congruent block parameter replacement %d -> %d", parameter, candidate)
	}
	targetIndex := -1
	for index := range cfg.Blocks {
		if cfg.Blocks[index].ID == target {
			targetIndex = index
			break
		}
	}
	if targetIndex < 0 || parameterIndex < 0 || parameterIndex >= len(cfg.Blocks[targetIndex].Parameters) || cfg.Blocks[targetIndex].Parameters[parameterIndex].ID != parameter {
		return fmt.Errorf("optir: stale block parameter %d at block %d position %d", parameter, target, parameterIndex)
	}

	remapCFGUses(cfg, map[ValueID]ValueID{parameter: candidate})
	parameters := cfg.Blocks[targetIndex].Parameters
	cfg.Blocks[targetIndex].Parameters = append(parameters[:parameterIndex:parameterIndex], parameters[parameterIndex+1:]...)
	for blockIndex := range cfg.Blocks {
		terminator := &cfg.Blocks[blockIndex].Terminator
		switch terminator.Kind {
		case TerminatorBranch:
			if terminator.True.Target == target {
				if err := removeEdgeArgument(&terminator.True, parameterIndex, cfg.Blocks[blockIndex].ID); err != nil {
					return err
				}
			}
		case TerminatorCondBranch:
			if terminator.True.Target == target {
				if err := removeEdgeArgument(&terminator.True, parameterIndex, cfg.Blocks[blockIndex].ID); err != nil {
					return err
				}
			}
			if terminator.False.Target == target {
				if err := removeEdgeArgument(&terminator.False, parameterIndex, cfg.Blocks[blockIndex].ID); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

func removeEdgeArgument(edge *Edge, index int, from BlockID) error {
	if index < 0 || index >= len(edge.Arguments) {
		return fmt.Errorf("optir: stale edge %d -> %d block parameter argument %d", from, edge.Target, index)
	}
	edge.Arguments = append(edge.Arguments[:index:index], edge.Arguments[index+1:]...)
	return nil
}

func resolveReplacementBounded(value ValueID, replacements map[ValueID]ValueID, maximumSteps int) (ValueID, bool) {
	if maximumSteps <= 0 {
		return 0, false
	}
	for step := 0; step < maximumSteps; step++ {
		replacement, exists := replacements[value]
		if !exists || replacement == value {
			return value, true
		}
		value = replacement
	}
	return 0, false
}
