package optir

import (
	"fmt"
	"math/big"
	"sort"
)

// Dominator records one node in the CFG dominator tree. The entry has no
// immediate dominator and depth zero.
type Dominator struct {
	Block        BlockID
	Immediate    BlockID
	HasImmediate bool
	Depth        int
}

// FlowEdge is a deterministic control-flow edge identity. Natural-loop
// analysis does not distinguish two conditional arms with the same endpoints.
type FlowEdge struct {
	From BlockID
	To   BlockID
}

// Induction is one proved affine loop-carried recurrence. Step is a signed
// mathematical decimal even when Type is unsigned. ExactTripCount is present
// only when fixed-width no-wrap reasoning proves it.
type Induction struct {
	HeaderValue       ValueID
	ParameterIndex    int
	Initial           ValueID
	Updates           []ValueID
	Type              Type
	Step              string
	Predicate         ValueID
	Bound             ValueID
	Comparison        string
	ExactTripCount    string
	HasExactTripCount bool
}

// NaturalLoop is the maximal natural loop for one header. Preheader is present
// only for a unique outside predecessor whose sole successor is the header.
type NaturalLoop struct {
	Header       BlockID
	Latches      []BlockID
	Blocks       []BlockID
	Exits        []FlowEdge
	Preheader    BlockID
	HasPreheader bool
	Parent       BlockID
	HasParent    bool
	Depth        int
	Inductions   []Induction
}

// LoopStructure is the value-independent control structure of one CFG:
// traversal order, dominance, back edges, and the natural-loop tree. Loops in
// this artifact never carry Inductions. A checked CFGTopology preservation
// certificate can reuse it across versions.
type LoopStructure struct {
	ReversePostOrder []BlockID
	Dominators       []Dominator
	BackEdges        []FlowEdge
	Loops            []NaturalLoop

	inputFingerprint string
	integrity        string
}

type LoopAnalysis struct {
	ReversePostOrder []BlockID
	Dominators       []Dominator
	BackEdges        []FlowEdge
	Loops            []NaturalLoop

	// inputFingerprint and integrity bind these public facts to the exact CFG
	// that produced them and detect mutation before a transform consumes them.
	// They are deliberately private: an analysis artifact is evidence returned
	// by AnalyzeLoops, not a record callers may forge.
	inputFingerprint string
	integrity        string
}

type loopOperation struct {
	operation Operation
}

type incomingTransfer struct {
	from BlockID
	edge Edge
}

type naturalLoopBuilder struct {
	info    NaturalLoop
	members map[BlockID]bool
	parent  *naturalLoopBuilder
}

// AnalyzeLoops computes target-independent dominance, natural-loop, affine
// recurrence, and exact constant trip-count facts. It never rewrites the CFG.
func AnalyzeLoops(cfg CFG) (LoopAnalysis, error) {
	structure, err := AnalyzeLoopStructure(cfg)
	if err != nil {
		return LoopAnalysis{}, err
	}
	return AnalyzeLoopsWithStructure(cfg, structure)
}

// AnalyzeLoopStructure computes the CFGTopology-only portion of loop analysis.
func AnalyzeLoopStructure(cfg CFG) (LoopStructure, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return LoopStructure{}, err
	}
	blocks, predecessors, _, _, _ := loopGraphInfo(cfg)
	reachable := make(map[BlockID]bool, len(blocks))
	for id := range blocks {
		reachable[id] = true
	}
	dominatorSets := computeDominators(cfg.Entry, reachable, predecessors)
	structure := LoopStructure{
		ReversePostOrder: loopReversePostOrder(cfg.Entry, blocks),
		inputFingerprint: fingerprintCFG(cfg),
	}
	structure.Dominators = publicDominators(dominatorSets)
	structure.BackEdges = loopBackEdges(blocks, dominatorSets)
	builders := buildNaturalLoops(structure.BackEdges, predecessors)
	finishNaturalLoops(builders, blocks, predecessors)
	for _, loop := range builders {
		structure.Loops = append(structure.Loops, cloneNaturalLoop(loop.info))
	}
	sort.Slice(structure.Loops, func(i, j int) bool {
		if structure.Loops[i].Depth != structure.Loops[j].Depth {
			return structure.Loops[i].Depth < structure.Loops[j].Depth
		}
		return structure.Loops[i].Header < structure.Loops[j].Header
	})
	structure.integrity = fingerprintLoopStructure(structure)
	return structure, nil
}

// AnalyzeLoopsWithStructure completes value-dependent induction facts from a
// structure artifact produced for the same exact CFG.
func AnalyzeLoopsWithStructure(cfg CFG, structure LoopStructure) (LoopAnalysis, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return LoopAnalysis{}, err
	}
	if err := validateLoopStructure(structure); err != nil {
		return LoopAnalysis{}, err
	}
	if structure.inputFingerprint != fingerprintCFG(cfg) {
		return LoopAnalysis{}, fmt.Errorf("optir: loop structure belongs to a different CFG")
	}
	return completeLoopAnalysis(cfg, structure), nil
}

// AnalyzeLoopsWithPreservedStructure reuses structure from an older CFG only
// when an intact certificate binds both contents and proves every declared
// LoopStructure requirement.
func AnalyzeLoopsWithPreservedStructure(cfg CFG, structure LoopStructure, certificate PreservationCertificate) (LoopAnalysis, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return LoopAnalysis{}, err
	}
	if err := validateLoopStructure(structure); err != nil {
		return LoopAnalysis{}, err
	}
	currentFingerprint := fingerprintCFG(cfg)
	if err := certificate.permitsContentReuse(structure.inputFingerprint, currentFingerprint, LoopStructureAnalysisRequirements()); err != nil {
		return LoopAnalysis{}, err
	}
	return completeLoopAnalysis(cfg, structure), nil
}

func completeLoopAnalysis(cfg CFG, structure LoopStructure) LoopAnalysis {
	blocks, _, incoming, operations, types := loopGraphInfo(cfg)
	analysis := LoopAnalysis{
		ReversePostOrder: append([]BlockID(nil), structure.ReversePostOrder...),
		Dominators:       append([]Dominator(nil), structure.Dominators...),
		BackEdges:        append([]FlowEdge(nil), structure.BackEdges...),
		inputFingerprint: fingerprintCFG(cfg),
	}
	for _, base := range structure.Loops {
		loop := cloneNaturalLoop(base)
		members := make(map[BlockID]bool, len(loop.Blocks))
		for _, block := range loop.Blocks {
			members[block] = true
		}
		loop.Inductions = analyzeInductions(loop, members, blocks, incoming, operations, types)
		analysis.Loops = append(analysis.Loops, loop)
	}
	analysis.integrity = fingerprintLoopAnalysis(analysis)
	return analysis
}

func validateLoopStructure(structure LoopStructure) error {
	if structure.inputFingerprint == "" {
		return fmt.Errorf("optir: loop structure has no input identity")
	}
	if structure.integrity == "" || structure.integrity != fingerprintLoopStructure(structure) {
		return fmt.Errorf("optir: loop structure was mutated")
	}
	return nil
}

func cloneNaturalLoop(loop NaturalLoop) NaturalLoop {
	result := loop
	result.Latches = append([]BlockID(nil), loop.Latches...)
	result.Blocks = append([]BlockID(nil), loop.Blocks...)
	result.Exits = append([]FlowEdge(nil), loop.Exits...)
	result.Inductions = append([]Induction(nil), loop.Inductions...)
	for index := range result.Inductions {
		result.Inductions[index].Updates = append([]ValueID(nil), result.Inductions[index].Updates...)
	}
	return result
}

func loopGraphInfo(cfg CFG) (map[BlockID]*Block, map[BlockID][]BlockID, map[BlockID][]incomingTransfer, map[ValueID]loopOperation, map[ValueID]Type) {
	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	predecessors := make(map[BlockID][]BlockID, len(cfg.Blocks))
	incoming := make(map[BlockID][]incomingTransfer, len(cfg.Blocks))
	operations := map[ValueID]loopOperation{}
	types := map[ValueID]Type{}
	for index := range cfg.Blocks {
		block := &cfg.Blocks[index]
		blocks[block.ID] = block
		for _, parameter := range block.Parameters {
			types[parameter.ID] = parameter.Type
		}
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				types[result.ID] = result.Type
				operations[result.ID] = loopOperation{operation: operation}
			}
		}
		for _, edge := range transformEdges(block.Terminator) {
			predecessors[edge.Target] = append(predecessors[edge.Target], block.ID)
			incoming[edge.Target] = append(incoming[edge.Target], incomingTransfer{from: block.ID, edge: edge})
		}
	}
	for id := range predecessors {
		sort.Slice(predecessors[id], func(i, j int) bool { return predecessors[id][i] < predecessors[id][j] })
	}
	return blocks, predecessors, incoming, operations, types
}

func loopReversePostOrder(entry BlockID, blocks map[BlockID]*Block) []BlockID {
	type frame struct {
		block      BlockID
		successors []BlockID
		next       int
	}
	successors := func(id BlockID) []BlockID {
		edges := transformEdges(blocks[id].Terminator)
		result := make([]BlockID, len(edges))
		for index, edge := range edges {
			result[index] = edge.Target
		}
		return result
	}
	visited := map[BlockID]bool{entry: true}
	stack := []frame{{block: entry, successors: successors(entry)}}
	postorder := make([]BlockID, 0, len(blocks))
	for len(stack) > 0 {
		top := &stack[len(stack)-1]
		if top.next < len(top.successors) {
			next := top.successors[top.next]
			top.next++
			if !visited[next] {
				visited[next] = true
				stack = append(stack, frame{block: next, successors: successors(next)})
			}
			continue
		}
		postorder = append(postorder, top.block)
		stack = stack[:len(stack)-1]
	}
	result := make([]BlockID, len(postorder))
	for index := range postorder {
		result[index] = postorder[len(postorder)-1-index]
	}
	return result
}

func publicDominators(sets map[BlockID]map[BlockID]bool) []Dominator {
	ids := sortedBlockIDs(sets)
	result := make([]Dominator, 0, len(ids))
	for _, id := range ids {
		record := Dominator{Block: id, Depth: len(sets[id]) - 1}
		bestDepth := -1
		for candidate := range sets[id] {
			if candidate == id {
				continue
			}
			depth := len(sets[candidate])
			if depth > bestDepth || (depth == bestDepth && candidate < record.Immediate) {
				record.Immediate = candidate
				record.HasImmediate = true
				bestDepth = depth
			}
		}
		result = append(result, record)
	}
	return result
}

func loopBackEdges(blocks map[BlockID]*Block, dominators map[BlockID]map[BlockID]bool) []FlowEdge {
	seen := map[FlowEdge]bool{}
	for _, id := range sortedBlockIDs(blocks) {
		for _, edge := range transformEdges(blocks[id].Terminator) {
			candidate := FlowEdge{From: id, To: edge.Target}
			if dominators[id][edge.Target] {
				seen[candidate] = true
			}
		}
	}
	result := make([]FlowEdge, 0, len(seen))
	for edge := range seen {
		result = append(result, edge)
	}
	sortFlowEdges(result)
	return result
}

func buildNaturalLoops(backEdges []FlowEdge, predecessors map[BlockID][]BlockID) []*naturalLoopBuilder {
	byHeader := map[BlockID]*naturalLoopBuilder{}
	for _, edge := range backEdges {
		loop := byHeader[edge.To]
		if loop == nil {
			loop = &naturalLoopBuilder{info: NaturalLoop{Header: edge.To}, members: map[BlockID]bool{edge.To: true}}
			byHeader[edge.To] = loop
		}
		if !containsUnsortedBlockID(loop.info.Latches, edge.From) {
			loop.info.Latches = append(loop.info.Latches, edge.From)
		}
		stack := []BlockID{edge.From}
		for len(stack) > 0 {
			last := len(stack) - 1
			block := stack[last]
			stack = stack[:last]
			if loop.members[block] {
				continue
			}
			loop.members[block] = true
			for _, predecessor := range predecessors[block] {
				if !loop.members[predecessor] {
					stack = append(stack, predecessor)
				}
			}
		}
	}
	result := make([]*naturalLoopBuilder, 0, len(byHeader))
	for _, loop := range byHeader {
		for block := range loop.members {
			loop.info.Blocks = append(loop.info.Blocks, block)
		}
		sort.Slice(loop.info.Blocks, func(i, j int) bool { return loop.info.Blocks[i] < loop.info.Blocks[j] })
		sort.Slice(loop.info.Latches, func(i, j int) bool { return loop.info.Latches[i] < loop.info.Latches[j] })
		result = append(result, loop)
	}
	sort.Slice(result, func(i, j int) bool { return result[i].info.Header < result[j].info.Header })
	return result
}

func finishNaturalLoops(loops []*naturalLoopBuilder, blocks map[BlockID]*Block, predecessors map[BlockID][]BlockID) {
	for _, loop := range loops {
		outside := []BlockID{}
		for _, predecessor := range predecessors[loop.info.Header] {
			if !loop.members[predecessor] && !containsUnsortedBlockID(outside, predecessor) {
				outside = append(outside, predecessor)
			}
		}
		if len(outside) == 1 {
			successors := transformEdges(blocks[outside[0]].Terminator)
			if len(successors) == 1 && successors[0].Target == loop.info.Header {
				loop.info.Preheader = outside[0]
				loop.info.HasPreheader = true
			}
		}
		seenExits := map[FlowEdge]bool{}
		for block := range loop.members {
			for _, edge := range transformEdges(blocks[block].Terminator) {
				if !loop.members[edge.Target] {
					seenExits[FlowEdge{From: block, To: edge.Target}] = true
				}
			}
		}
		for edge := range seenExits {
			loop.info.Exits = append(loop.info.Exits, edge)
		}
		sortFlowEdges(loop.info.Exits)
	}
	for _, loop := range loops {
		for _, possible := range loops {
			if possible == loop || len(possible.members) <= len(loop.members) || !setContains(possible.members, loop.members) {
				continue
			}
			if loop.parent == nil || len(possible.members) < len(loop.parent.members) {
				loop.parent = possible
			}
		}
	}
	for _, loop := range loops {
		loop.info.Depth = 1
		for parent := loop.parent; parent != nil && loop.info.Depth <= len(loops); parent = parent.parent {
			loop.info.Depth++
		}
		if loop.parent != nil {
			loop.info.Parent = loop.parent.info.Header
			loop.info.HasParent = true
		}
	}
}

func analyzeInductions(loop NaturalLoop, members map[BlockID]bool, blocks map[BlockID]*Block, incoming map[BlockID][]incomingTransfer, operations map[ValueID]loopOperation, types map[ValueID]Type) []Induction {
	if !loop.HasPreheader || len(loop.Latches) == 0 {
		return nil
	}
	header := blocks[loop.Header]
	result := []Induction{}
	for parameterIndex, parameter := range header.Parameters {
		current := loopCurrentValues(parameter, loop.Header, members, blocks, incoming)
		initial, ok := loopInitialValue(loop, parameterIndex, incoming)
		if !ok {
			continue
		}
		updates, delta, ok := loopUpdates(loop, parameterIndex, current, blocks, operations, types)
		if !ok {
			continue
		}
		induction := Induction{
			HeaderValue:    parameter.ID,
			ParameterIndex: parameterIndex,
			Initial:        initial,
			Updates:        updates,
			Type:           parameter.Type,
			Step:           delta.String(),
		}
		predicate, bound, comparison, ok := loopPredicate(loop, current, blocks, operations)
		if ok {
			induction.Predicate = predicate
			induction.Bound = bound
			induction.Comparison = comparison
			initialConstant, initialOK := loopIntegerConstant(initial, parameter.Type, operations)
			boundConstant, boundOK := loopIntegerConstant(bound, parameter.Type, operations)
			if initialOK && boundOK {
				if count, proved := exactFixedWidthTripCount(initialConstant, boundConstant, delta, comparison, parameter.Type); proved {
					induction.ExactTripCount = count.String()
					induction.HasExactTripCount = true
				}
			}
		}
		result = append(result, induction)
	}
	return result
}

func loopCurrentValues(parameter Value, header BlockID, members map[BlockID]bool, blocks map[BlockID]*Block, incoming map[BlockID][]incomingTransfer) map[ValueID]bool {
	current := map[ValueID]bool{parameter.ID: true}
	changed := true
	for changed {
		changed = false
		for blockID := range members {
			block := blocks[blockID]
			if blockID != header {
				for parameterIndex, target := range block.Parameters {
					if current[target.ID] {
						continue
					}
					transfers := incoming[blockID]
					equivalent := len(transfers) > 0
					for _, transfer := range transfers {
						if !members[transfer.from] || parameterIndex >= len(transfer.edge.Arguments) || !current[transfer.edge.Arguments[parameterIndex]] {
							equivalent = false
							break
						}
					}
					if equivalent {
						current[target.ID] = true
						changed = true
					}
				}
			}
			for _, operation := range block.Operations {
				if operation.Code == OpCopy && len(operation.Results) == 1 && len(operation.Operands) == 1 && len(operation.Effects) == 0 && current[operation.Operands[0]] && operation.Results[0].Type == parameter.Type && !current[operation.Results[0].ID] {
					current[operation.Results[0].ID] = true
					changed = true
				}
			}
		}
	}
	return current
}

func loopInitialValue(loop NaturalLoop, parameterIndex int, incoming map[BlockID][]incomingTransfer) (ValueID, bool) {
	found := false
	var initial ValueID
	for _, transfer := range incoming[loop.Header] {
		if transfer.from != loop.Preheader {
			continue
		}
		if found || parameterIndex >= len(transfer.edge.Arguments) {
			return 0, false
		}
		initial = transfer.edge.Arguments[parameterIndex]
		found = true
	}
	return initial, found
}

func loopUpdates(loop NaturalLoop, parameterIndex int, current map[ValueID]bool, blocks map[BlockID]*Block, operations map[ValueID]loopOperation, types map[ValueID]Type) ([]ValueID, *big.Int, bool) {
	var delta *big.Int
	seenUpdates := map[ValueID]bool{}
	for _, latch := range loop.Latches {
		foundEdge := false
		for _, edge := range transformEdges(blocks[latch].Terminator) {
			if edge.Target != loop.Header {
				continue
			}
			if parameterIndex >= len(edge.Arguments) {
				return nil, nil, false
			}
			foundEdge = true
			update := edge.Arguments[parameterIndex]
			candidate, ok := loopUpdateDelta(update, current, operations, types)
			if !ok || candidate.Sign() == 0 || (delta != nil && delta.Cmp(candidate) != 0) {
				return nil, nil, false
			}
			delta = candidate
			seenUpdates[update] = true
		}
		if !foundEdge {
			return nil, nil, false
		}
	}
	updates := make([]ValueID, 0, len(seenUpdates))
	for update := range seenUpdates {
		updates = append(updates, update)
	}
	sort.Slice(updates, func(i, j int) bool { return updates[i] < updates[j] })
	return updates, delta, delta != nil
}

func loopUpdateDelta(update ValueID, current map[ValueID]bool, operations map[ValueID]loopOperation, types map[ValueID]Type) (*big.Int, bool) {
	defined, exists := operations[update]
	if !exists || len(defined.operation.Effects) != 0 || len(defined.operation.Operands) != 2 || len(defined.operation.Results) != 1 {
		return nil, false
	}
	left, right := defined.operation.Operands[0], defined.operation.Operands[1]
	constant := func(value ValueID) (*big.Int, bool) {
		return loopIntegerConstant(value, types[update], operations)
	}
	switch defined.operation.Code {
	case OpIntAdd:
		if current[left] {
			return constant(right)
		}
		if current[right] {
			return constant(left)
		}
	case OpIntSub:
		if current[left] {
			value, ok := constant(right)
			if ok {
				return new(big.Int).Neg(value), true
			}
		}
	}
	return nil, false
}

func loopPredicate(loop NaturalLoop, current map[ValueID]bool, blocks map[BlockID]*Block, operations map[ValueID]loopOperation) (ValueID, ValueID, string, bool) {
	if len(loop.Exits) != 1 {
		return 0, 0, "", false
	}
	exit := loop.Exits[0]
	terminator := blocks[exit.From].Terminator
	if terminator.Kind != TerminatorCondBranch {
		return 0, 0, "", false
	}
	trueInside := containsBlockID(loop.Blocks, terminator.True.Target)
	falseInside := containsBlockID(loop.Blocks, terminator.False.Target)
	if trueInside == falseInside {
		return 0, 0, "", false
	}
	defined, exists := operations[terminator.Condition]
	if !exists || !isClosedPureOperation(defined.operation) || len(defined.operation.Operands) != 2 {
		return 0, 0, "", false
	}
	comparison := defined.operation.Code
	if !isIntegerComparison(comparison) {
		return 0, 0, "", false
	}
	left, right := defined.operation.Operands[0], defined.operation.Operands[1]
	var bound ValueID
	switch {
	case current[left] && !current[right]:
		bound = right
	case current[right] && !current[left]:
		bound = left
		comparison = swapComparison(comparison)
	default:
		return 0, 0, "", false
	}
	if !trueInside {
		comparison = negateComparison(comparison)
	}
	return terminator.Condition, bound, comparison, comparison != ""
}

func isIntegerComparison(code string) bool {
	switch code {
	case OpEqual, OpNotEqual, OpLess, OpLessEqual, OpGreater, OpGreaterEqual:
		return true
	default:
		return false
	}
}

func swapComparison(code string) string {
	switch code {
	case OpLess:
		return OpGreater
	case OpLessEqual:
		return OpGreaterEqual
	case OpGreater:
		return OpLess
	case OpGreaterEqual:
		return OpLessEqual
	default:
		return code
	}
}

func negateComparison(code string) string {
	switch code {
	case OpEqual:
		return OpNotEqual
	case OpNotEqual:
		return OpEqual
	case OpLess:
		return OpGreaterEqual
	case OpLessEqual:
		return OpGreater
	case OpGreater:
		return OpLessEqual
	case OpGreaterEqual:
		return OpLess
	default:
		return ""
	}
}

func loopIntegerConstant(value ValueID, typ Type, operations map[ValueID]loopOperation) (*big.Int, bool) {
	defined, exists := operations[value]
	if !exists || defined.operation.Code != OpConstInt || len(defined.operation.Results) != 1 || defined.operation.Results[0].Type != typ {
		return nil, false
	}
	spelling, err := uniqueAttribute(defined.operation.Attributes, AttributeValue)
	if err != nil {
		return nil, false
	}
	constant, ok := new(big.Int).SetString(spelling, 10)
	return constant, ok
}

func exactFixedWidthTripCount(initial, bound, step *big.Int, comparison string, typ Type) (*big.Int, bool) {
	minimum, maximum, ok := fixedWidthRange(typ)
	if !ok || initial.Cmp(minimum) < 0 || initial.Cmp(maximum) > 0 || bound.Cmp(minimum) < 0 || bound.Cmp(maximum) > 0 {
		return nil, false
	}
	if !integerComparisonHolds(initial, bound, comparison) {
		return big.NewInt(0), true
	}
	var count *big.Int
	switch comparison {
	case OpLess:
		if step.Sign() <= 0 {
			return nil, false
		}
		count = ceilPositive(new(big.Int).Sub(bound, initial), step)
	case OpLessEqual:
		if step.Sign() <= 0 {
			return nil, false
		}
		count = new(big.Int).Add(new(big.Int).Quo(new(big.Int).Sub(bound, initial), step), big.NewInt(1))
	case OpGreater:
		if step.Sign() >= 0 {
			return nil, false
		}
		count = ceilPositive(new(big.Int).Sub(initial, bound), new(big.Int).Neg(step))
	case OpGreaterEqual:
		if step.Sign() >= 0 {
			return nil, false
		}
		count = new(big.Int).Add(new(big.Int).Quo(new(big.Int).Sub(initial, bound), new(big.Int).Neg(step)), big.NewInt(1))
	default:
		return nil, false
	}
	final := new(big.Int).Add(initial, new(big.Int).Mul(count, step))
	if final.Cmp(minimum) < 0 || final.Cmp(maximum) > 0 || integerComparisonHolds(final, bound, comparison) {
		return nil, false
	}
	return count, true
}

func integerComparisonHolds(left, right *big.Int, comparison string) bool {
	order := left.Cmp(right)
	switch comparison {
	case OpEqual:
		return order == 0
	case OpNotEqual:
		return order != 0
	case OpLess:
		return order < 0
	case OpLessEqual:
		return order <= 0
	case OpGreater:
		return order > 0
	case OpGreaterEqual:
		return order >= 0
	default:
		return false
	}
}

func fixedWidthRange(typ Type) (*big.Int, *big.Int, bool) {
	signed, bits, ok := integerType(typ)
	if !ok {
		return nil, nil, false
	}
	if !signed {
		return big.NewInt(0), new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), uint(bits)), big.NewInt(1)), true
	}
	half := new(big.Int).Lsh(big.NewInt(1), uint(bits-1))
	return new(big.Int).Neg(new(big.Int).Set(half)), new(big.Int).Sub(half, big.NewInt(1)), true
}

func ceilPositive(numerator, denominator *big.Int) *big.Int {
	adjusted := new(big.Int).Add(numerator, new(big.Int).Sub(denominator, big.NewInt(1)))
	return adjusted.Quo(adjusted, denominator)
}

func sortedBlockIDs[T any](values map[BlockID]T) []BlockID {
	result := make([]BlockID, 0, len(values))
	for id := range values {
		result = append(result, id)
	}
	sort.Slice(result, func(i, j int) bool { return result[i] < result[j] })
	return result
}

func sortFlowEdges(edges []FlowEdge) {
	sort.Slice(edges, func(i, j int) bool {
		if edges[i].From != edges[j].From {
			return edges[i].From < edges[j].From
		}
		return edges[i].To < edges[j].To
	})
}

func containsBlockID(values []BlockID, want BlockID) bool {
	index := sort.Search(len(values), func(i int) bool { return values[i] >= want })
	return index < len(values) && values[index] == want
}

func containsUnsortedBlockID(values []BlockID, want BlockID) bool {
	for _, value := range values {
		if value == want {
			return true
		}
	}
	return false
}

func setContains(outer, inner map[BlockID]bool) bool {
	for block := range inner {
		if !outer[block] {
			return false
		}
	}
	return true
}
