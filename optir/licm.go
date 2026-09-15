package optir

import "fmt"

// LICMMove records one operation moved from a natural loop to its canonical
// preheader. Results retain their SSA identities across the move.
type LICMMove struct {
	From    BlockID
	To      BlockID
	Code    string
	Results []ValueID
}

// LICMReport is deterministic evidence about loop-invariant operations moved
// in a verified CFG.
type LICMReport struct {
	LoopsAnalyzed         int
	LoopsWithoutPreheader int
	HoistedOperations     int
	Moves                 []LICMMove
}

// HoistLoopInvariants returns a new CFG with total, pure loop-invariant scalar
// operations moved to canonical preheaders. It never moves operations with
// effects, potentially trapping or unknown semantics, or facts beyond the
// result-local checked type fact, and it never mutates the caller's CFG.
func HoistLoopInvariants(cfg CFG) (CFG, LICMReport, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return CFG{}, LICMReport{}, err
	}
	analysis, err := AnalyzeLoops(cfg)
	if err != nil {
		return CFG{}, LICMReport{}, err
	}
	result := cloneCFG(cfg)
	blocks := make(map[BlockID]*Block, len(result.Blocks))
	reachable := make(map[BlockID]bool, len(result.Blocks))
	for index := range result.Blocks {
		block := &result.Blocks[index]
		blocks[block.ID] = block
		reachable[block.ID] = true
	}
	definitions, predecessors := transformGraphInfo(result)
	dominators := computeDominators(result.Entry, reachable, predecessors)
	definitionBlocks := make(map[ValueID]BlockID, len(definitions))
	for value, definition := range definitions {
		definitionBlocks[value] = definition.block
	}

	report := LICMReport{LoopsAnalyzed: len(analysis.Loops)}
	for _, loop := range analysis.Loops {
		if !loop.HasPreheader {
			report.LoopsWithoutPreheader++
			continue
		}
		members := make(map[BlockID]bool, len(loop.Blocks))
		for _, block := range loop.Blocks {
			members[block] = true
		}
		preheader := blocks[loop.Preheader]
		changed := true
		for changed {
			changed = false
			for _, blockID := range loop.Blocks {
				block := blocks[blockID]
				kept := make([]Operation, 0, len(block.Operations))
				for _, operation := range block.Operations {
					if !canHoistLoopOperation(operation, loop.Preheader, members, definitionBlocks, dominators) {
						kept = append(kept, operation)
						continue
					}
					preheader.Operations = append(preheader.Operations, operation)
					results := valueIDs(operation.Results)
					for _, result := range results {
						definitionBlocks[result] = loop.Preheader
					}
					report.HoistedOperations++
					report.Moves = append(report.Moves, LICMMove{From: blockID, To: loop.Preheader, Code: operation.Code, Results: results})
					changed = true
				}
				block.Operations = kept
			}
		}
	}
	if err := validateAnalysisCFG(result); err != nil {
		return CFG{}, LICMReport{}, fmt.Errorf("optir: LICM produced invalid CFG: %w", err)
	}
	return result, report, nil
}

func canHoistLoopOperation(operation Operation, preheader BlockID, members map[BlockID]bool, definitions map[ValueID]BlockID, dominators map[BlockID]map[BlockID]bool) bool {
	if !isClosedPureOperation(operation) || !locationIndependentOperationFacts(operation) {
		return false
	}
	for _, operand := range operation.Operands {
		definition, exists := definitions[operand]
		if !exists {
			return false
		}
		if definition == preheader {
			continue
		}
		if members[definition] || !dominators[preheader][definition] {
			return false
		}
	}
	return true
}

// The checked type fact merely restates the typed SSA result and is therefore
// valid wherever that definition moves. Every other fact remains pinned until
// a proof-domain-specific motion rule licenses it.
func locationIndependentOperationFacts(operation Operation) bool {
	results := make(map[ValueID]Type, len(operation.Results))
	for _, result := range operation.Results {
		results[result.ID] = result.Type
	}
	for _, fact := range operation.Facts {
		if fact.Name != "checked.type" || fact.Provenance != "checked" || len(fact.Values) != 1 {
			return false
		}
		resultType, exists := results[fact.Values[0]]
		if !exists || fact.Witness != string(resultType) {
			return false
		}
	}
	return true
}
