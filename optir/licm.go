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
	analysis, err := AnalyzeLoops(cfg)
	if err != nil {
		return CFG{}, LICMReport{}, err
	}
	return HoistLoopInvariantsWithAnalysis(cfg, analysis)
}

// HoistLoopInvariantsWithAnalysis is the artifact-oriented LICM entry point.
// It consumes loop and dominance facts previously produced for this exact CFG,
// rejecting stale or mutated evidence instead of silently recomputing it.
func HoistLoopInvariantsWithAnalysis(cfg CFG, analysis LoopAnalysis) (CFG, LICMReport, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return CFG{}, LICMReport{}, err
	}
	if analysis.inputFingerprint == "" || analysis.inputFingerprint != fingerprintCFG(cfg) {
		return CFG{}, LICMReport{}, fmt.Errorf("optir: LICM loop analysis belongs to a different CFG")
	}
	if analysis.integrity == "" || analysis.integrity != fingerprintLoopAnalysis(analysis) {
		return CFG{}, LICMReport{}, fmt.Errorf("optir: LICM loop analysis was mutated")
	}
	result := cloneCFG(cfg)
	blocks := make(map[BlockID]*Block, len(result.Blocks))
	for index := range result.Blocks {
		block := &result.Blocks[index]
		blocks[block.ID] = block
	}
	definitions, _ := transformGraphInfo(result)
	dominators, err := dominatorSetsFromLoopAnalysis(result, analysis)
	if err != nil {
		return CFG{}, LICMReport{}, err
	}
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

func dominatorSetsFromLoopAnalysis(cfg CFG, analysis LoopAnalysis) (map[BlockID]map[BlockID]bool, error) {
	blocks := make(map[BlockID]bool, len(cfg.Blocks))
	for _, block := range cfg.Blocks {
		blocks[block.ID] = true
	}
	records := make(map[BlockID]Dominator, len(analysis.Dominators))
	for _, record := range analysis.Dominators {
		if !blocks[record.Block] {
			return nil, fmt.Errorf("optir: LICM loop analysis names missing dominator block %d", record.Block)
		}
		if _, exists := records[record.Block]; exists {
			return nil, fmt.Errorf("optir: LICM loop analysis repeats dominator block %d", record.Block)
		}
		records[record.Block] = record
	}
	if len(records) != len(blocks) {
		return nil, fmt.Errorf("optir: LICM loop analysis has %d dominators for %d blocks", len(records), len(blocks))
	}

	sets := make(map[BlockID]map[BlockID]bool, len(records))
	for block, record := range records {
		set := map[BlockID]bool{block: true}
		seen := map[BlockID]bool{block: true}
		current := record
		depth := 0
		for current.HasImmediate {
			parent, exists := records[current.Immediate]
			if !exists {
				return nil, fmt.Errorf("optir: LICM dominator %d has missing parent %d", current.Block, current.Immediate)
			}
			if seen[parent.Block] {
				return nil, fmt.Errorf("optir: LICM dominator chain for block %d contains a cycle", block)
			}
			seen[parent.Block] = true
			set[parent.Block] = true
			current = parent
			depth++
		}
		if current.Block != cfg.Entry || depth != record.Depth {
			return nil, fmt.Errorf("optir: LICM dominator chain for block %d is inconsistent", block)
		}
		sets[block] = set
	}
	return sets, nil
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
