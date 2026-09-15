package optir

import (
	"fmt"
	"sort"
	"strconv"
	"strings"
)

// ValueReplacement records one SSA identity eliminated by GVN. To always
// names a definition that dominates every former use of From.
type ValueReplacement struct {
	From ValueID
	To   ValueID
}

// GVNReport is deterministic evidence about congruent expressions removed
// from a verified CFG.
type GVNReport struct {
	EliminatedOperations int
	Replacements         []ValueReplacement
}

// DCEReport is deterministic evidence about unused pure operations removed
// from a verified CFG.
type DCEReport struct {
	EliminatedOperations int
	EliminatedValues     []ValueID
}

type GVNDCEReport struct {
	GVN GVNReport
	DCE DCEReport
}

type operationLocation struct {
	block BlockID
	index int
}

// EliminateGlobalValueRedundancies returns a new CFG. It shares only
// operations in the closed, total, pure Oak vocabulary below and only when
// the retained definition dominates the removed definition. Copy results use
// their operand's number, and exact commutative/inverse comparisons have one
// canonical expression key. The caller's CFG is unchanged.
func EliminateGlobalValueRedundancies(cfg CFG) (CFG, GVNReport, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return CFG{}, GVNReport{}, err
	}
	result := cloneCFG(cfg)
	definitions, predecessors := transformGraphInfo(result)
	reachable := make(map[BlockID]bool, len(result.Blocks))
	blocks := make(map[BlockID]*Block, len(result.Blocks))
	for index := range result.Blocks {
		block := &result.Blocks[index]
		reachable[block.ID] = true
		blocks[block.ID] = block
	}
	dominators := computeDominators(result.Entry, reachable, predecessors)

	type blockOrder struct {
		index int
		id    BlockID
		depth int
	}
	order := make([]blockOrder, len(result.Blocks))
	for index, block := range result.Blocks {
		order[index] = blockOrder{index: index, id: block.ID, depth: len(dominators[block.ID])}
	}
	sort.Slice(order, func(i, j int) bool {
		if order[i].depth != order[j].depth {
			return order[i].depth < order[j].depth
		}
		return order[i].id < order[j].id
	})

	type candidate struct {
		location operationLocation
		results  []ValueID
	}
	available := map[string][]candidate{}
	valueNumbers := make(map[ValueID]ValueID, len(definitions))
	for value := range definitions {
		valueNumbers[value] = value
	}
	replacements := map[ValueID]ValueID{}
	removed := map[operationLocation]bool{}
	pendingFacts := map[operationLocation][]Fact{}
	report := GVNReport{}

	for _, ordered := range order {
		block := &result.Blocks[ordered.index]
		for index := range block.Operations {
			operation := &block.Operations[index]
			operation.Operands = remapReplacements(operation.Operands, replacements)
			for factIndex := range operation.Facts {
				operation.Facts[factIndex].Values = remapReplacements(operation.Facts[factIndex].Values, replacements)
			}
			if !isClosedPureOperation(*operation) {
				assignFreshValueNumbers(*operation, valueNumbers)
				continue
			}
			key := globalValueExpressionKey(*operation, valueNumbers)
			current := operationLocation{block: block.ID, index: index}
			var selected *candidate
			var movedFacts []Fact
			for candidateIndex := len(available[key]) - 1; candidateIndex >= 0; candidateIndex-- {
				possible := available[key][candidateIndex]
				if !locationDominates(possible.location.block, possible.location.index, current.block, current.index, dominators) {
					continue
				}
				local := make(map[ValueID]ValueID, len(operation.Results))
				for resultIndex, value := range operation.Results {
					local[value.ID] = possible.results[resultIndex]
				}
				facts := remapFactsWithLocal(operation.Facts, replacements, local)
				if !factsValidAt(facts, possible.location, definitions, dominators) {
					continue
				}
				selected = &possible
				movedFacts = facts
				break
			}
			if selected == nil {
				available[key] = append(available[key], candidate{location: current, results: valueIDs(operation.Results)})
				assignOperationValueNumbers(*operation, valueNumbers)
				continue
			}
			removed[current] = true
			report.EliminatedOperations++
			for resultIndex, value := range operation.Results {
				replacements[value.ID] = selected.results[resultIndex]
				valueNumbers[value.ID] = valueNumberOf(selected.results[resultIndex], valueNumbers)
				report.Replacements = append(report.Replacements, ValueReplacement{From: value.ID, To: selected.results[resultIndex]})
			}
			pendingFacts[selected.location] = append(pendingFacts[selected.location], movedFacts...)
		}
	}

	for location, facts := range pendingFacts {
		block := blocks[location.block]
		operation := &block.Operations[location.index]
		for _, fact := range facts {
			fact.Values = remapReplacements(fact.Values, replacements)
			if !containsFact(operation.Facts, fact) {
				operation.Facts = append(operation.Facts, fact)
			}
		}
	}
	remapCFGUses(&result, replacements)
	for blockIndex := range result.Blocks {
		block := &result.Blocks[blockIndex]
		kept := make([]Operation, 0, len(block.Operations))
		for operationIndex, operation := range block.Operations {
			if !removed[operationLocation{block: block.ID, index: operationIndex}] {
				kept = append(kept, operation)
			}
		}
		block.Operations = kept
	}
	sort.Slice(report.Replacements, func(i, j int) bool { return report.Replacements[i].From < report.Replacements[j].From })
	if err := validateAnalysisCFG(result); err != nil {
		return CFG{}, GVNReport{}, fmt.Errorf("optir: GVN produced invalid CFG: %w", err)
	}
	return result, report, nil
}

// EliminateDeadCode removes only operations in the closed pure vocabulary
// whose complete result tuple has no external SSA use. It iterates so deleting
// a dead consumer can expose its producers. The caller's CFG is unchanged.
func EliminateDeadCode(cfg CFG) (CFG, DCEReport, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return CFG{}, DCEReport{}, err
	}
	result := cloneCFG(cfg)
	report := DCEReport{}
	for {
		uses := externalUses(result)
		removed := false
		for blockIndex := range result.Blocks {
			block := &result.Blocks[blockIndex]
			kept := make([]Operation, 0, len(block.Operations))
			for _, operation := range block.Operations {
				dead := isClosedPureOperation(operation)
				for _, value := range operation.Results {
					dead = dead && uses[value.ID] == 0
				}
				if !dead {
					kept = append(kept, operation)
					continue
				}
				removed = true
				report.EliminatedOperations++
				for _, value := range operation.Results {
					report.EliminatedValues = append(report.EliminatedValues, value.ID)
				}
			}
			block.Operations = kept
		}
		if !removed {
			break
		}
	}
	sort.Slice(report.EliminatedValues, func(i, j int) bool { return report.EliminatedValues[i] < report.EliminatedValues[j] })
	if err := validateAnalysisCFG(result); err != nil {
		return CFG{}, DCEReport{}, fmt.Errorf("optir: DCE produced invalid CFG: %w", err)
	}
	return result, report, nil
}

// SimplifyGVNDCE is the generic scalar cleanup order. GVN exposes unused
// congruent producers and copies, and DCE then removes dead pure chains. The
// result remains an analysis-only candidate until an emission equivalence gate
// consumes it.
func SimplifyGVNDCE(cfg CFG) (CFG, GVNDCEReport, error) {
	common, gvn, err := EliminateGlobalValueRedundancies(cfg)
	if err != nil {
		return CFG{}, GVNDCEReport{}, err
	}
	dead, dce, err := EliminateDeadCode(common)
	if err != nil {
		return CFG{}, GVNDCEReport{}, err
	}
	return dead, GVNDCEReport{GVN: gvn, DCE: dce}, nil
}

func validateAnalysisCFG(cfg CFG) error {
	if err := Verify(cfg); err != nil {
		return err
	}
	types := map[ValueID]Type{}
	for _, block := range cfg.Blocks {
		for _, parameter := range block.Parameters {
			types[parameter.ID] = parameter.Type
		}
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				types[result.ID] = result.Type
			}
		}
	}
	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			if err := validateSCCPOperation(operation, types); err != nil {
				return fmt.Errorf("optir: block %d operation %d (%s): %w", block.ID, index, operation.Code, err)
			}
		}
	}
	return nil
}

// isClosedPureOperation deliberately does not treat an empty Effects slice as
// proof of purity. Unknown and potentially trapping operations remain roots.
func isClosedPureOperation(operation Operation) bool {
	if len(operation.Results) == 0 || len(operation.Effects) != 0 {
		return false
	}
	switch operation.Code {
	case OpConstBool, OpConstInt, OpConstUnit, OpCopy, OpCastInt,
		OpBoolNot, OpIntNeg, OpIntAdd, OpIntSub, OpIntMul,
		OpIntAnd, OpIntOr, OpIntXor,
		OpEqual, OpNotEqual, OpLess, OpLessEqual, OpGreater, OpGreaterEqual:
		return true
	default:
		return false
	}
}

func globalValueExpressionKey(operation Operation, valueNumbers map[ValueID]ValueID) string {
	code := operation.Code
	operands := make([]ValueID, len(operation.Operands))
	for index, operand := range operation.Operands {
		operands[index] = valueNumberOf(operand, valueNumbers)
	}
	// Unknown attributes remain ordered and operand-sensitive. The checked
	// projection emits no attributes on these algebraic operations; refusing
	// normalization when an extension adds one keeps the transform closed.
	if len(operands) == 2 && len(operation.Attributes) == 0 {
		switch code {
		case OpGreater:
			code = OpLess
			operands[0], operands[1] = operands[1], operands[0]
		case OpGreaterEqual:
			code = OpLessEqual
			operands[0], operands[1] = operands[1], operands[0]
		case OpIntAdd, OpIntMul, OpIntAnd, OpIntOr, OpIntXor, OpEqual, OpNotEqual:
			if operands[1] < operands[0] {
				operands[0], operands[1] = operands[1], operands[0]
			}
		}
	}
	var key strings.Builder
	writeKeyString(&key, code)
	writeKeyUint(&key, uint64(len(operation.Results)))
	for _, result := range operation.Results {
		writeKeyString(&key, string(result.Type))
	}
	writeKeyUint(&key, uint64(len(operands)))
	for _, operand := range operands {
		writeKeyUint(&key, uint64(operand))
	}
	writeKeyUint(&key, uint64(len(operation.Attributes)))
	for _, attribute := range operation.Attributes {
		writeKeyString(&key, attribute.Name)
		writeKeyString(&key, attribute.Value)
	}
	return key.String()
}

func assignOperationValueNumbers(operation Operation, valueNumbers map[ValueID]ValueID) {
	if operation.Code == OpCopy && len(operation.Results) == 1 && len(operation.Operands) == 1 && len(operation.Attributes) == 0 {
		valueNumbers[operation.Results[0].ID] = valueNumberOf(operation.Operands[0], valueNumbers)
		return
	}
	assignFreshValueNumbers(operation, valueNumbers)
}

func assignFreshValueNumbers(operation Operation, valueNumbers map[ValueID]ValueID) {
	for _, result := range operation.Results {
		valueNumbers[result.ID] = result.ID
	}
}

func valueNumberOf(value ValueID, valueNumbers map[ValueID]ValueID) ValueID {
	if number, exists := valueNumbers[value]; exists {
		return number
	}
	return value
}

func writeKeyString(key *strings.Builder, value string) {
	writeKeyUint(key, uint64(len(value)))
	key.WriteString(value)
}

func writeKeyUint(key *strings.Builder, value uint64) {
	key.WriteString(strconv.FormatUint(value, 10))
	key.WriteByte(':')
}

func transformGraphInfo(cfg CFG) (map[ValueID]definition, map[BlockID][]BlockID) {
	definitions := map[ValueID]definition{}
	predecessors := map[BlockID][]BlockID{}
	for _, block := range cfg.Blocks {
		for _, parameter := range block.Parameters {
			definitions[parameter.ID] = definition{typeOf: parameter.Type, block: block.ID, index: -1}
		}
		for index, operation := range block.Operations {
			for _, result := range operation.Results {
				definitions[result.ID] = definition{typeOf: result.Type, block: block.ID, index: index}
			}
		}
		for _, edge := range transformEdges(block.Terminator) {
			predecessors[edge.Target] = append(predecessors[edge.Target], block.ID)
		}
	}
	return definitions, predecessors
}

func transformEdges(terminator Terminator) []Edge {
	switch terminator.Kind {
	case TerminatorBranch:
		return []Edge{terminator.True}
	case TerminatorCondBranch:
		return []Edge{terminator.True, terminator.False}
	default:
		return nil
	}
}

func locationDominates(definitionBlock BlockID, definitionIndex int, useBlock BlockID, useIndex int, dominators map[BlockID]map[BlockID]bool) bool {
	if definitionBlock == useBlock {
		return definitionIndex < useIndex
	}
	return dominators[useBlock][definitionBlock]
}

func factsValidAt(facts []Fact, at operationLocation, definitions map[ValueID]definition, dominators map[BlockID]map[BlockID]bool) bool {
	for _, fact := range facts {
		for _, value := range fact.Values {
			if verifyUse(value, at.block, at.index+1, definitions, dominators) != nil {
				return false
			}
		}
	}
	return true
}

func remapFactsWithLocal(facts []Fact, replacements, local map[ValueID]ValueID) []Fact {
	result := cloneFacts(facts)
	for index := range result {
		for valueIndex, value := range result[index].Values {
			if replacement, exists := local[value]; exists {
				value = replacement
			}
			result[index].Values[valueIndex] = resolveReplacement(value, replacements)
		}
	}
	return result
}

func remapReplacements(values []ValueID, replacements map[ValueID]ValueID) []ValueID {
	result := make([]ValueID, len(values))
	for index, value := range values {
		result[index] = resolveReplacement(value, replacements)
	}
	return result
}

func resolveReplacement(value ValueID, replacements map[ValueID]ValueID) ValueID {
	for {
		replacement, exists := replacements[value]
		if !exists || replacement == value {
			return value
		}
		value = replacement
	}
}

func remapCFGUses(cfg *CFG, replacements map[ValueID]ValueID) {
	for blockIndex := range cfg.Blocks {
		block := &cfg.Blocks[blockIndex]
		for operationIndex := range block.Operations {
			operation := &block.Operations[operationIndex]
			operation.Operands = remapReplacements(operation.Operands, replacements)
			for factIndex := range operation.Facts {
				operation.Facts[factIndex].Values = remapReplacements(operation.Facts[factIndex].Values, replacements)
			}
		}
		block.Terminator.Condition = resolveReplacement(block.Terminator.Condition, replacements)
		block.Terminator.Values = remapReplacements(block.Terminator.Values, replacements)
		block.Terminator.True.Arguments = remapReplacements(block.Terminator.True.Arguments, replacements)
		block.Terminator.False.Arguments = remapReplacements(block.Terminator.False.Arguments, replacements)
	}
	for index := range cfg.Facts {
		cfg.Facts[index].Values = remapReplacements(cfg.Facts[index].Values, replacements)
	}
}

func containsFact(facts []Fact, want Fact) bool {
	for _, fact := range facts {
		if fact.Name != want.Name || fact.Provenance != want.Provenance || fact.Witness != want.Witness || len(fact.Values) != len(want.Values) {
			continue
		}
		equal := true
		for index := range fact.Values {
			equal = equal && fact.Values[index] == want.Values[index]
		}
		if equal {
			return true
		}
	}
	return false
}

func externalUses(cfg CFG) map[ValueID]int {
	uses := map[ValueID]int{}
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			for _, operand := range operation.Operands {
				uses[operand]++
			}
			own := make(map[ValueID]bool, len(operation.Results))
			for _, result := range operation.Results {
				own[result.ID] = true
			}
			for _, fact := range operation.Facts {
				for _, value := range fact.Values {
					if !own[value] {
						uses[value]++
					}
				}
			}
		}
		if block.Terminator.Condition != 0 {
			uses[block.Terminator.Condition]++
		}
		for _, value := range block.Terminator.Values {
			uses[value]++
		}
		for _, value := range block.Terminator.True.Arguments {
			uses[value]++
		}
		for _, value := range block.Terminator.False.Arguments {
			uses[value]++
		}
	}
	for _, fact := range cfg.Facts {
		for _, value := range fact.Values {
			uses[value]++
		}
	}
	return uses
}

func cloneCFG(cfg CFG) CFG {
	result := cfg
	result.Results = append([]Type(nil), cfg.Results...)
	result.Facts = cloneFacts(cfg.Facts)
	result.Blocks = make([]Block, len(cfg.Blocks))
	for index, block := range cfg.Blocks {
		result.Blocks[index] = block
		result.Blocks[index].Parameters = cloneValues(block.Parameters)
		result.Blocks[index].Operations = make([]Operation, len(block.Operations))
		for operationIndex, operation := range block.Operations {
			result.Blocks[index].Operations[operationIndex] = cloneOperation(operation)
		}
		result.Blocks[index].Terminator.Values = append([]ValueID(nil), block.Terminator.Values...)
		result.Blocks[index].Terminator.True.Arguments = append([]ValueID(nil), block.Terminator.True.Arguments...)
		result.Blocks[index].Terminator.False.Arguments = append([]ValueID(nil), block.Terminator.False.Arguments...)
	}
	return result
}
