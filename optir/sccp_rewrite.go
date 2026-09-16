package optir

import (
	"fmt"
	"reflect"
	"sort"
	"strconv"
)

// BlockMerge records a straight-line block folded into its sole predecessor.
// Into and Removed are stable CFG block identities, not slice positions.
type BlockMerge struct {
	Into    BlockID
	Removed BlockID
}

// SCCPRewriteReport is deterministic evidence about transformations driven by
// one exact SCCP result. It is descriptive only: callers must still put the
// resulting CFG through their normal semantic admission gate before emission.
type SCCPRewriteReport struct {
	RewrittenValues      []ValueID
	SimplifiedBranches   []BlockID
	RemovedUnreachable   []BlockID
	MergedBlocks         []BlockMerge
	RemovedTrampolines   []BlockID
	DroppedFunctionFacts int
}

// Changes reports the number of independently recorded scalar and CFG
// changes. It is intended for diagnostics and candidate availability, not as
// an estimate of target cost.
func (report SCCPRewriteReport) Changes() int {
	return len(report.RewrittenValues) + len(report.SimplifiedBranches) +
		len(report.RemovedUnreachable) + len(report.MergedBlocks) +
		len(report.RemovedTrampolines)
}

// SimplifyWithSCCP consumes SCCP evidence for the exact supplied CFG. It
// rewrites only closed total scalar operations, selects exact conditional
// edges, removes the resulting unreachable blocks, and performs bounded
// SSA-aware straight-line/trampoline cleanup. Both input and output pass the
// independent CFG verifier. Stale or noncanonical evidence is refused.
func SimplifyWithSCCP(cfg CFG, evidence SCCPResult) (CFG, SCCPRewriteReport, error) {
	if err := Verify(cfg); err != nil {
		return CFG{}, SCCPRewriteReport{}, err
	}
	canonical, err := AnalyzeSCCP(cfg)
	if err != nil {
		return CFG{}, SCCPRewriteReport{}, err
	}
	if !reflect.DeepEqual(canonical, evidence) {
		return CFG{}, SCCPRewriteReport{}, fmt.Errorf("optir: SCCP rewrite evidence does not match the exact CFG analysis")
	}

	result := cloneCFG(cfg)
	report := SCCPRewriteReport{}
	executable := make(map[BlockID]bool, len(evidence.ExecutableBlocks))
	for _, block := range evidence.ExecutableBlocks {
		executable[block] = true
	}
	constants := make(map[ValueID]Constant, len(evidence.Values))
	for _, value := range evidence.Values {
		if value.State == LatticeConstant {
			constants[value.Value] = value.Constant
		}
	}
	branches := make(map[BlockID]SCCPBranch, len(evidence.Branches))
	for _, branch := range evidence.Branches {
		branches[branch.Block] = branch
	}

	for blockIndex := range result.Blocks {
		block := &result.Blocks[blockIndex]
		if !executable[block.ID] {
			continue
		}
		for operationIndex := range block.Operations {
			operation := &block.Operations[operationIndex]
			if len(operation.Results) != 1 {
				continue
			}
			constant, known := constants[operation.Results[0].ID]
			if !known || !canRewriteSCCPConstant(*operation) || operationIsConstant(*operation, constant) {
				continue
			}
			replacement, err := operationForSCCPConstant(*operation, constant)
			if err != nil {
				return CFG{}, SCCPRewriteReport{}, err
			}
			*operation = replacement
			report.RewrittenValues = append(report.RewrittenValues, operation.Results[0].ID)
		}

		if block.Terminator.Kind == TerminatorCondBranch {
			branch, known := branches[block.ID]
			if known {
				selected := block.Terminator.False
				if branch.Taken {
					selected = block.Terminator.True
				}
				if branch.Condition != block.Terminator.Condition || branch.Target != selected.Target ||
					!hasSCCPExecutableEdge(evidence.ExecutableEdges, block.ID, selected.Target, branch.Taken) {
					return CFG{}, SCCPRewriteReport{}, fmt.Errorf("optir: SCCP branch evidence for block %d is inconsistent", block.ID)
				}
				block.Terminator = Terminator{Kind: TerminatorBranch, True: selected}
				report.SimplifiedBranches = append(report.SimplifiedBranches, block.ID)
			} else if reflect.DeepEqual(block.Terminator.True, block.Terminator.False) {
				block.Terminator = Terminator{Kind: TerminatorBranch, True: block.Terminator.True}
				report.SimplifiedBranches = append(report.SimplifiedBranches, block.ID)
			}
		}
	}

	if err := removeSCCPUnreachable(&result, executable, &report); err != nil {
		return CFG{}, SCCPRewriteReport{}, err
	}
	maximumCleanupSteps := len(result.Blocks)
	for step := 0; step < maximumCleanupSteps; step++ {
		changed, err := mergeOneStraightLineBlock(&result, &report)
		if err != nil {
			return CFG{}, SCCPRewriteReport{}, err
		}
		if changed {
			continue
		}
		changed, err = bypassOneTrampoline(&result, &report)
		if err != nil {
			return CFG{}, SCCPRewriteReport{}, err
		}
		if !changed {
			break
		}
	}

	sort.Slice(report.RewrittenValues, func(i, j int) bool { return report.RewrittenValues[i] < report.RewrittenValues[j] })
	sort.Slice(report.SimplifiedBranches, func(i, j int) bool { return report.SimplifiedBranches[i] < report.SimplifiedBranches[j] })
	sort.Slice(report.RemovedUnreachable, func(i, j int) bool { return report.RemovedUnreachable[i] < report.RemovedUnreachable[j] })
	sort.Slice(report.MergedBlocks, func(i, j int) bool {
		if report.MergedBlocks[i].Removed != report.MergedBlocks[j].Removed {
			return report.MergedBlocks[i].Removed < report.MergedBlocks[j].Removed
		}
		return report.MergedBlocks[i].Into < report.MergedBlocks[j].Into
	})
	sort.Slice(report.RemovedTrampolines, func(i, j int) bool { return report.RemovedTrampolines[i] < report.RemovedTrampolines[j] })
	if err := Verify(result); err != nil {
		return CFG{}, SCCPRewriteReport{}, fmt.Errorf("optir: SCCP rewrite produced invalid CFG: %w", err)
	}
	return result, report, nil
}

func canRewriteSCCPConstant(operation Operation) bool {
	if !isClosedPureOperation(operation) || len(operation.Effects) != 0 {
		return false
	}
	switch operation.Code {
	case OpConstBool, OpConstInt, OpConstUnit:
		// Existing constants already carry the exact value. Leaving them
		// untouched also preserves any extension attribute rather than
		// silently interpreting it as irrelevant.
		return false
	default:
		// Unknown attributes may refine an extension's semantics. Do not erase
		// them merely because the base opcode is in the closed vocabulary.
		return len(operation.Attributes) == 0
	}
}

func operationIsConstant(operation Operation, constant Constant) bool {
	if len(operation.Results) != 1 || operation.Results[0].Type != constant.Type || len(operation.Effects) != 0 {
		return false
	}
	switch constant.Kind {
	case ConstantBool:
		return operation.Code == OpConstBool && len(operation.Attributes) == 1 &&
			operation.Attributes[0] == (Attribute{Name: AttributeValue, Value: strconv.FormatBool(constant.Bool)})
	case ConstantInteger:
		return operation.Code == OpConstInt && len(operation.Attributes) == 1 &&
			operation.Attributes[0] == (Attribute{Name: AttributeValue, Value: constant.Integer})
	case ConstantUnit:
		return operation.Code == OpConstUnit && len(operation.Attributes) == 0
	default:
		return false
	}
}

func operationForSCCPConstant(original Operation, constant Constant) (Operation, error) {
	if len(original.Results) != 1 || original.Results[0].Type != constant.Type {
		return Operation{}, fmt.Errorf("optir: SCCP constant type disagrees with value %d", original.Results[0].ID)
	}
	replacement := Operation{
		Results: cloneValues(original.Results),
		Facts:   cloneFacts(original.Facts),
		Source:  original.Source,
	}
	switch constant.Kind {
	case ConstantBool:
		if constant.Type != TypeBool {
			return Operation{}, fmt.Errorf("optir: SCCP Bool constant has type %s", constant.Type)
		}
		replacement.Code = OpConstBool
		replacement.Attributes = []Attribute{{Name: AttributeValue, Value: strconv.FormatBool(constant.Bool)}}
	case ConstantInteger:
		normalized, err := normalizeInteger(constant.Integer, constant.Type)
		if err != nil || normalized != constant.Integer {
			return Operation{}, fmt.Errorf("optir: SCCP integer constant %q is not canonical for %s", constant.Integer, constant.Type)
		}
		replacement.Code = OpConstInt
		replacement.Attributes = []Attribute{{Name: AttributeValue, Value: constant.Integer}}
	case ConstantUnit:
		if constant.Type != Type("()") {
			return Operation{}, fmt.Errorf("optir: SCCP unit constant has type %s", constant.Type)
		}
		replacement.Code = OpConstUnit
	default:
		return Operation{}, fmt.Errorf("optir: unsupported SCCP constant kind %q", constant.Kind)
	}
	return replacement, nil
}

func hasSCCPExecutableEdge(edges []SCCPEdge, from, to BlockID, taken bool) bool {
	arm := "false"
	if taken {
		arm = "true"
	}
	for _, edge := range edges {
		if edge.From == from && edge.To == to && edge.Arm == arm {
			return true
		}
	}
	return false
}

func removeSCCPUnreachable(cfg *CFG, expected map[BlockID]bool, report *SCCPRewriteReport) error {
	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	for index := range cfg.Blocks {
		blocks[cfg.Blocks[index].ID] = &cfg.Blocks[index]
	}
	reachable := reachableBlocks(cfg.Entry, blocks)
	if len(reachable) != len(expected) {
		return fmt.Errorf("optir: simplified CFG reachability disagrees with SCCP evidence")
	}
	for block := range reachable {
		if !expected[block] {
			return fmt.Errorf("optir: block %d is syntactically reachable but absent from SCCP evidence", block)
		}
	}
	kept := make([]Block, 0, len(reachable))
	for _, block := range cfg.Blocks {
		if reachable[block.ID] {
			kept = append(kept, block)
		} else {
			report.RemovedUnreachable = append(report.RemovedUnreachable, block.ID)
		}
	}
	cfg.Blocks = kept
	report.DroppedFunctionFacts += dropFactsWithMissingValues(cfg)
	return nil
}

func dropFactsWithMissingValues(cfg *CFG) int {
	defined := map[ValueID]bool{}
	for _, block := range cfg.Blocks {
		for _, parameter := range block.Parameters {
			defined[parameter.ID] = true
		}
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				defined[result.ID] = true
			}
		}
	}
	kept := make([]Fact, 0, len(cfg.Facts))
	dropped := 0
	for _, fact := range cfg.Facts {
		valid := true
		for _, value := range fact.Values {
			valid = valid && defined[value]
		}
		if valid {
			kept = append(kept, fact)
		} else {
			dropped++
		}
	}
	cfg.Facts = kept
	return dropped
}

func mergeOneStraightLineBlock(cfg *CFG, report *SCCPRewriteReport) (bool, error) {
	indices, incoming := cfgBlockIndicesAndIncoming(*cfg)
	for predecessorIndex := range cfg.Blocks {
		predecessor := cfg.Blocks[predecessorIndex]
		if predecessor.Terminator.Kind != TerminatorBranch {
			continue
		}
		targetID := predecessor.Terminator.True.Target
		targetIndex, exists := indices[targetID]
		if !exists || targetID == cfg.Entry || targetID == predecessor.ID || incoming[targetID] != 1 {
			continue
		}
		target := cfg.Blocks[targetIndex]
		if len(predecessor.Terminator.True.Arguments) != len(target.Parameters) {
			return false, fmt.Errorf("optir: block %d merge edge arity changed", predecessor.ID)
		}
		replacements := make(map[ValueID]ValueID, len(target.Parameters))
		for index, parameter := range target.Parameters {
			replacements[parameter.ID] = predecessor.Terminator.True.Arguments[index]
		}
		remapCFGUses(cfg, replacements)
		// remapCFGUses does not alter operation definitions or block slices.
		// Reload both blocks before growing the predecessor operation slice.
		predecessor = cfg.Blocks[predecessorIndex]
		target = cfg.Blocks[targetIndex]
		mergedOperations := make([]Operation, 0, len(predecessor.Operations)+len(target.Operations))
		mergedOperations = append(mergedOperations, predecessor.Operations...)
		mergedOperations = append(mergedOperations, target.Operations...)
		cfg.Blocks[predecessorIndex].Operations = mergedOperations
		cfg.Blocks[predecessorIndex].Terminator = target.Terminator
		cfg.Blocks = removeCFGBlockAt(cfg.Blocks, targetIndex)
		report.MergedBlocks = append(report.MergedBlocks, BlockMerge{Into: predecessor.ID, Removed: targetID})
		return true, nil
	}
	return false, nil
}

func bypassOneTrampoline(cfg *CFG, report *SCCPRewriteReport) (bool, error) {
	indices, incoming := cfgBlockIndicesAndIncoming(*cfg)
	uses := externalUses(*cfg)
	for trampolineIndex := range cfg.Blocks {
		trampoline := cfg.Blocks[trampolineIndex]
		if trampoline.ID == cfg.Entry || len(trampoline.Operations) != 0 ||
			trampoline.Terminator.Kind != TerminatorBranch || incoming[trampoline.ID] < 2 ||
			trampoline.Terminator.True.Target == trampoline.ID {
			continue
		}
		parameterIndices := make(map[ValueID]int, len(trampoline.Parameters))
		for index, parameter := range trampoline.Parameters {
			parameterIndices[parameter.ID] = index
		}
		expectedUses := make(map[ValueID]int, len(trampoline.Parameters))
		valid := true
		for _, argument := range trampoline.Terminator.True.Arguments {
			if _, exists := parameterIndices[argument]; !exists {
				valid = false
				break
			}
			expectedUses[argument]++
		}
		for _, parameter := range trampoline.Parameters {
			valid = valid && uses[parameter.ID] == expectedUses[parameter.ID]
		}
		if !valid {
			continue
		}

		redirected := 0
		for predecessorIndex := range cfg.Blocks {
			if predecessorIndex == trampolineIndex {
				continue
			}
			terminator := &cfg.Blocks[predecessorIndex].Terminator
			redirect := func(edge *Edge) error {
				if edge.Target != trampoline.ID {
					return nil
				}
				if len(edge.Arguments) != len(trampoline.Parameters) {
					return fmt.Errorf("optir: trampoline %d incoming arity changed", trampoline.ID)
				}
				arguments := make([]ValueID, len(trampoline.Terminator.True.Arguments))
				for index, outgoing := range trampoline.Terminator.True.Arguments {
					arguments[index] = edge.Arguments[parameterIndices[outgoing]]
				}
				edge.Target = trampoline.Terminator.True.Target
				edge.Arguments = arguments
				redirected++
				return nil
			}
			switch terminator.Kind {
			case TerminatorBranch:
				if err := redirect(&terminator.True); err != nil {
					return false, err
				}
			case TerminatorCondBranch:
				if err := redirect(&terminator.True); err != nil {
					return false, err
				}
				if err := redirect(&terminator.False); err != nil {
					return false, err
				}
			}
		}
		if redirected != incoming[trampoline.ID] {
			return false, fmt.Errorf("optir: trampoline %d incoming edge count changed", trampoline.ID)
		}
		cfg.Blocks = removeCFGBlockAt(cfg.Blocks, indices[trampoline.ID])
		report.RemovedTrampolines = append(report.RemovedTrampolines, trampoline.ID)
		return true, nil
	}
	return false, nil
}

func cfgBlockIndicesAndIncoming(cfg CFG) (map[BlockID]int, map[BlockID]int) {
	indices := make(map[BlockID]int, len(cfg.Blocks))
	incoming := make(map[BlockID]int, len(cfg.Blocks))
	for index, block := range cfg.Blocks {
		indices[block.ID] = index
		for _, edge := range transformEdges(block.Terminator) {
			incoming[edge.Target]++
		}
	}
	return indices, incoming
}

func removeCFGBlockAt(blocks []Block, index int) []Block {
	result := make([]Block, 0, len(blocks)-1)
	result = append(result, blocks[:index]...)
	result = append(result, blocks[index+1:]...)
	return result
}
