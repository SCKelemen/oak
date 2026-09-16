package optir

import (
	"fmt"
	"sort"
)

// DeadBlockParameterReport records non-entry phi-like definitions removed
// because no operation, proof fact, terminator, or remaining edge argument
// observes them.
type DeadBlockParameterReport struct {
	EliminatedParameters int
	EliminatedValues     []ValueID
}

// EliminateDeadBlockParameters removes unused non-entry block parameters and
// their exact positional incoming arguments. Entry parameters are part of the
// function ABI even when the CFG body does not use them, so they are never
// candidates.
//
// One parameter is removed per bounded iteration. Removing a dead downstream
// argument may expose an otherwise-unused forwarding parameter upstream; the
// bound is the original parameter count, so this fixed point cannot diverge.
// Facts conservatively count as uses and are never discarded by this pass.
func EliminateDeadBlockParameters(cfg CFG) (CFG, DeadBlockParameterReport, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return CFG{}, DeadBlockParameterReport{}, err
	}
	result := cloneCFG(cfg)
	maximumEliminations := 0
	maximumInt := int(^uint(0) >> 1)
	for _, block := range result.Blocks {
		if len(block.Parameters) > maximumInt-maximumEliminations {
			return CFG{}, DeadBlockParameterReport{}, fmt.Errorf("optir: block parameter count overflows dead-parameter bound")
		}
		maximumEliminations += len(block.Parameters)
	}

	report := DeadBlockParameterReport{}
	for iteration := 0; iteration < maximumEliminations; iteration++ {
		uses := blockParameterUses(result)
		blocks := make(map[BlockID]*Block, len(result.Blocks))
		for index := range result.Blocks {
			blocks[result.Blocks[index].ID] = &result.Blocks[index]
		}
		removed := false
		for _, blockID := range sortedBlockIDs(blocks) {
			if blockID == result.Entry {
				continue
			}
			block := blocks[blockID]
			for parameterIndex, parameter := range block.Parameters {
				if uses[parameter.ID] {
					continue
				}
				if err := removeDeadBlockParameter(&result, block.ID, parameterIndex, parameter.ID); err != nil {
					return CFG{}, DeadBlockParameterReport{}, err
				}
				report.EliminatedParameters++
				report.EliminatedValues = append(report.EliminatedValues, parameter.ID)
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

	sort.Slice(report.EliminatedValues, func(i, j int) bool {
		return report.EliminatedValues[i] < report.EliminatedValues[j]
	})
	if err := validateAnalysisCFG(result); err != nil {
		return CFG{}, DeadBlockParameterReport{}, fmt.Errorf("optir: dead block-parameter cleanup produced invalid CFG: %w", err)
	}
	return result, report, nil
}

func blockParameterUses(cfg CFG) map[ValueID]bool {
	uses := map[ValueID]bool{}
	addFacts := func(facts []Fact) {
		for _, fact := range facts {
			for _, value := range fact.Values {
				uses[value] = true
			}
		}
	}
	addFacts(cfg.Facts)
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			for _, value := range operation.Operands {
				uses[value] = true
			}
			addFacts(operation.Facts)
		}
		for _, value := range terminatorUses(block.Terminator) {
			uses[value] = true
		}
	}
	return uses
}

func removeDeadBlockParameter(cfg *CFG, target BlockID, parameterIndex int, parameter ValueID) error {
	if cfg == nil || parameter == 0 {
		return fmt.Errorf("optir: invalid dead block parameter %d", parameter)
	}
	targetIndex := -1
	for index := range cfg.Blocks {
		if cfg.Blocks[index].ID == target {
			targetIndex = index
			break
		}
	}
	if targetIndex < 0 || target == cfg.Entry || parameterIndex < 0 || parameterIndex >= len(cfg.Blocks[targetIndex].Parameters) || cfg.Blocks[targetIndex].Parameters[parameterIndex].ID != parameter {
		return fmt.Errorf("optir: stale dead block parameter %d at block %d position %d", parameter, target, parameterIndex)
	}

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
