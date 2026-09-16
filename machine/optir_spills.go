package machine

import (
	"fmt"
	"math"
	"sort"

	"github.com/SCKelemen/oak/optir"
)

// optIRRV64SpillLayout gives a verified abstract spill slot an RV64 frame
// offset. The materializer owns the spill portion of the frame; a disjoint
// return-address save area may be composed above it.
type optIRRV64SpillLayout struct {
	Offsets map[optir.SpillSlotID]int64
	Frame   int64
}

func layoutOptIRRV64Spills(plan optir.RegisterPlan, rematerialized map[optir.ValueID]optir.RematerializationDecision, maximumFrame int64) (optIRRV64SpillLayout, error) {
	layout := optIRRV64SpillLayout{Offsets: map[optir.SpillSlotID]int64{}}
	for value := range rematerialized {
		if _, spilled := plan.Spills[value]; !spilled {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 rematerialized value %d is not spilled", value)
		}
	}
	if len(plan.Spills) == 0 {
		if len(plan.Slots) != 0 {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill plan has slots without spilled values")
		}
		return layout, nil
	}
	if maximumFrame < 16 {
		return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill frame limit %d is smaller than one aligned frame", maximumFrame)
	}

	var next int64
	for index, slot := range plan.Slots {
		if slot.ID != optir.SpillSlotID(index+1) {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill slot %d is not canonical", slot.ID)
		}
		width, alignment := int64(slot.WidthBytes), int64(slot.AlignmentBytes)
		if width != 1 && width != 2 && width != 4 && width != 8 || alignment != width {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill slot %d has unsupported %d-byte width/%d-byte alignment", slot.ID, width, alignment)
		}
		materialized := false
		for _, value := range slot.Values {
			if _, omitted := rematerialized[value]; !omitted {
				materialized = true
				break
			}
		}
		if !materialized {
			continue
		}
		aligned, ok := checkedAlign(next, alignment)
		if !ok || aligned > maximumFrame-width {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill slots exceed the %d-byte target frame limit", maximumFrame)
		}
		layout.Offsets[slot.ID] = aligned
		next = aligned + width
	}
	for value, slot := range plan.Spills {
		_, omitted := rematerialized[value]
		if _, exists := layout.Offsets[slot]; !exists && !omitted {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spilled value %d names missing slot %d", value, slot)
		}
	}
	if next == 0 {
		return layout, nil
	}
	frame, ok := checkedAlign(next, 16)
	if !ok || frame == 0 || frame > maximumFrame {
		return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill frame exceeds the %d-byte target limit", maximumFrame)
	}
	layout.Frame = frame
	return layout, nil
}

func checkedAlign(value, alignment int64) (int64, bool) {
	if value < 0 || alignment <= 0 || alignment&(alignment-1) != 0 {
		return 0, false
	}
	mask := alignment - 1
	if value > int64(^uint64(0)>>1)-mask {
		return 0, false
	}
	return (value + mask) &^ mask, true
}

func composeOptIRRV64Frame(spillFrame int64, hasCalls bool) (frame, raOffset int64, err error) {
	if spillFrame < 0 || spillFrame%16 != 0 || spillFrame > optIRRV64MaxFrame {
		return 0, 0, fmt.Errorf("machine: invalid OptIR RV64 spill frame %d", spillFrame)
	}
	if !hasCalls {
		return spillFrame, 0, nil
	}
	if spillFrame > optIRRV64MaxFrame-16 {
		return 0, 0, fmt.Errorf("machine: OptIR RV64 spill/call frame needs more than %d bytes", optIRRV64MaxFrame)
	}
	return spillFrame + 16, spillFrame + 8, nil
}

func validateOptIRRV64SpillCFG(cfg optir.CFG, plan optir.RegisterPlan) error {
	return validateOptIRRV64SpillCFGSelection(cfg, plan, nil)
}

func validateOptIRRV64SpillCFGSelection(cfg optir.CFG, plan optir.RegisterPlan, memory *optIRRegionMemorySelection) error {
	if len(plan.Spills) == 0 {
		return nil
	}
	for _, block := range cfg.Blocks {
		for operationIndex, operation := range block.Operations {
			site := optir.OperationSite{Block: block.ID, Index: operationIndex}
			if optIRRV64AdmitsSpillEffect(memory, operation.Code, site) {
				continue
			}
			if operation.Code != optir.OpCall && len(operation.Effects) != 0 {
				return fmt.Errorf("machine: OptIR RV64 spill materialization refuses non-call effects")
			}
		}
	}

	// Distinguish acyclic spill materialization from the one exact natural-loop
	// form admitted below.
	acyclic, err := optIRCFGAcyclic(cfg)
	if err != nil {
		return err
	}
	if !acyclic {
		return validateOptIRRV64SpillLoop(cfg, plan)
	}
	return nil
}

func optIRRV64AdmitsSpillEffect(memory *optIRRegionMemorySelection, code string, site optir.OperationSite) bool {
	if memory == nil {
		return false
	}
	switch code {
	case optir.OpLoadRegion:
		_, admitted := memory.loads[site]
		return admitted
	case optir.OpStoreRegion:
		_, admitted := memory.stores[site]
		return admitted
	default:
		return false
	}
}

// optIRCFGAcyclic counts every CFG edge, including two conditional arms with
// the same target. A Kahn traversal therefore rejects irreducible cycles as
// well as natural loops.
func optIRCFGAcyclic(cfg optir.CFG) (bool, error) {
	indegree := make(map[optir.BlockID]int, len(cfg.Blocks))
	outgoing := make(map[optir.BlockID][]optir.BlockID, len(cfg.Blocks))
	for _, block := range cfg.Blocks {
		indegree[block.ID] = 0
	}
	for _, block := range cfg.Blocks {
		for _, edge := range optIRTerminatorEdges(block.Terminator) {
			if _, exists := indegree[edge.Target]; !exists {
				return false, fmt.Errorf("machine: OptIR CFG names missing block %d", edge.Target)
			}
			outgoing[block.ID] = append(outgoing[block.ID], edge.Target)
			indegree[edge.Target]++
		}
	}
	queue := make([]optir.BlockID, 0, len(cfg.Blocks))
	for _, block := range cfg.Blocks {
		if indegree[block.ID] == 0 {
			queue = append(queue, block.ID)
		}
	}
	visited := 0
	for cursor := 0; cursor < len(queue); cursor++ {
		block := queue[cursor]
		visited++
		for _, target := range outgoing[block] {
			indegree[target]--
			if indegree[target] == 0 {
				queue = append(queue, target)
			}
		}
	}
	return visited == len(cfg.Blocks), nil
}

// planOptIRSpillsKeepingCanonicalLoopCondition keeps the predicate of the one
// admitted spill-loop shape in a register. The generic cost model otherwise
// (correctly) prefers spilling that cheap Bool, but byte-width loop stores are
// outside the instruction verifier's frame-memory model. Each attempted
// precolor is checked by the generic planner; failure remains an ordinary
// candidate refusal.
func planOptIRSpillsKeepingCanonicalLoopCondition(cfg optir.CFG, pool []int, fixed map[optir.ValueID]int) (optir.RegisterPlan, map[optir.ValueID]int, error) {
	condition, canonicalLoop := optIRCanonicalLoopCondition(cfg)
	if canonicalLoop {
		if _, alreadyFixed := fixed[condition]; alreadyFixed {
			plan, err := optir.PlanRegisters(cfg, pool, fixed)
			return plan, fixed, err
		}
		registers := append([]int(nil), pool...)
		sort.Ints(registers)
		seen := map[int]bool{}
		for _, register := range registers {
			if register < 0 || seen[register] {
				continue
			}
			seen[register] = true
			constrained := make(map[optir.ValueID]int, len(fixed)+1)
			for value, color := range fixed {
				constrained[value] = color
			}
			constrained[condition] = register
			plan, err := optir.PlanRegisters(cfg, pool, constrained)
			if err == nil {
				return plan, constrained, nil
			}
		}
	}
	plan, err := optir.PlanRegisters(cfg, pool, fixed)
	return plan, fixed, err
}

func optIRRV64Rematerializations(cfg optir.CFG, pool []int, fixed map[optir.ValueID]int, plan optir.RegisterPlan) (map[optir.ValueID]optir.RematerializationDecision, error) {
	accepted := map[optir.ValueID]optir.RematerializationDecision{}
	acyclic, err := optIRCFGAcyclic(cfg)
	if err != nil || !acyclic {
		return accepted, err
	}
	evidence, err := optir.AnalyzeRematerialization(cfg, pool, fixed, plan)
	if err != nil {
		return nil, fmt.Errorf("machine: OptIR RV64 rematerialization analysis: %w", err)
	}
	if err := optir.VerifyRematerializationPlan(cfg, pool, fixed, plan, evidence); err != nil {
		return nil, fmt.Errorf("machine: OptIR RV64 rematerialization evidence: %w", err)
	}
	definitions := optIRRV64Definitions(cfg)
	for _, decision := range evidence.Decisions {
		if decision.Code != optir.OpConstBool && decision.Code != optir.OpConstInt {
			continue
		}
		operation, exists := definitions[decision.Value]
		cost, ok := optIRRV64RematerializationCost(operation)
		if !exists || !ok || decision.Uses == 0 || cost > math.MaxUint64/decision.Uses || decision.Uses == math.MaxUint64 {
			continue
		}
		if cost*decision.Uses <= decision.Uses+1 {
			accepted[decision.Value] = decision
		}
	}
	return accepted, nil
}

func optIRRV64RematerializationCost(operation optir.Operation) (uint64, bool) {
	if len(operation.Results) != 1 || len(operation.Operands) != 0 || len(operation.Effects) != 0 || len(operation.Facts) != 0 {
		return 0, false
	}
	switch operation.Code {
	case optir.OpConstBool:
		if operation.Results[0].Type != optir.TypeBool || len(operation.Attributes) != 1 || operation.Attributes[0].Name != optir.AttributeValue {
			return 0, false
		}
		value, ok := optIRAttribute(operation, optir.AttributeValue)
		return 1, ok && (value == "true" || value == "false")
	case optir.OpConstInt:
		if len(operation.Attributes) != 1 || operation.Attributes[0].Name != optir.AttributeValue {
			return 0, false
		}
		spelling, ok := optIRAttribute(operation, optir.AttributeValue)
		if !ok {
			return 0, false
		}
		value, err := optIRIntegerConstant(spelling, operation.Results[0].Type)
		if err != nil {
			return 0, false
		}
		canonical := optIRRV64Canonical(value, operation.Results[0].Type)
		if canonical >= -(1<<31) && canonical < 1<<31 {
			return optIRRV64LIWords(canonical), true
		}
		low := int64(int32(uint32(uint64(canonical))))
		high := int64(int32(uint32((uint64(canonical) - uint64(low)) >> 32)))
		return optIRRV64LIWords(high) + 1 + optIRRV64LIWords(low) + 1, true
	default:
		return 0, false
	}
}

func optIRRV64LIWords(value int64) uint64 {
	if value >= -2048 && value <= 2047 {
		return 1
	}
	high := (value + 0x800) >> 12
	if value-(high<<12) == 0 {
		return 1
	}
	return 2
}

func optIRCanonicalLoopCondition(cfg optir.CFG) (optir.ValueID, bool) {
	structure, err := optir.AnalyzeLoopStructure(cfg)
	if err != nil || len(structure.Loops) != 1 || len(structure.BackEdges) != 1 {
		return 0, false
	}
	loop := structure.Loops[0]
	if len(loop.Blocks) != 2 || len(loop.Latches) != 1 || len(loop.Exits) != 1 || !loop.HasPreheader || loop.HasParent || loop.Depth != 1 {
		return 0, false
	}
	header := optIRBlock(cfg, loop.Header)
	latch := optIRBlock(cfg, loop.Latches[0])
	preheader := optIRBlock(cfg, loop.Preheader)
	exit := optIRBlock(cfg, loop.Exits[0].To)
	if header == nil || latch == nil || preheader == nil || exit == nil || header.ID == latch.ID {
		return 0, false
	}
	backedge := structure.BackEdges[0]
	if backedge.From != latch.ID || backedge.To != header.ID || loop.Exits[0].From != header.ID {
		return 0, false
	}
	if preheader.Terminator.Kind != optir.TerminatorBranch || preheader.Terminator.True.Target != header.ID ||
		latch.Terminator.Kind != optir.TerminatorBranch || latch.Terminator.True.Target != header.ID ||
		header.Terminator.Kind != optir.TerminatorCondBranch || exit.Terminator.Kind != optir.TerminatorReturn {
		return 0, false
	}
	trueEdge, falseEdge := header.Terminator.True, header.Terminator.False
	if len(trueEdge.Arguments) != 0 || len(falseEdge.Arguments) != 0 {
		return 0, false
	}
	trueIsBody := trueEdge.Target == latch.ID
	falseIsBody := falseEdge.Target == latch.ID
	if trueIsBody == falseIsBody {
		return 0, false
	}
	exitEdge := falseEdge
	if falseIsBody {
		exitEdge = trueEdge
	}
	if exitEdge.Target != exit.ID {
		return 0, false
	}
	return header.Terminator.Condition, true
}

// validateOptIRRV64SpillLoop admits only the canonical loop shape that the
// instruction verifier can couple with loop-carried frame memory: a unique
// preheader, a conditional header, one straight-line body/latch, and one
// return exit. Broader loops remain ordinary candidate refusals.
func validateOptIRRV64SpillLoop(cfg optir.CFG, plan optir.RegisterPlan) error {
	refuse := func() error {
		return fmt.Errorf("machine: OptIR RV64 spill materialization refuses unsupported cyclic control flow")
	}
	for _, slot := range plan.Slots {
		if slot.WidthBytes != slot.AlignmentBytes || slot.WidthBytes != 4 && slot.WidthBytes != 8 {
			return fmt.Errorf("machine: OptIR RV64 loop spill slot %d has unsupported %d-byte width/%d-byte alignment", slot.ID, slot.WidthBytes, slot.AlignmentBytes)
		}
	}
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			if operation.Code == optir.OpCall {
				return fmt.Errorf("machine: OptIR RV64 spill materialization refuses calls in cyclic control flow")
			}
		}
	}
	if _, canonical := optIRCanonicalLoopCondition(cfg); !canonical {
		return refuse()
	}
	return nil
}

func validateOptIRRV64SpillScratches(pool, scratches []int) error {
	allocated := map[int]bool{}
	for _, register := range pool {
		if register < 0 || allocated[register] {
			return fmt.Errorf("machine: OptIR RV64 allocation pool has invalid register %d", register)
		}
		allocated[register] = true
	}
	if len(scratches) < 2 {
		return fmt.Errorf("machine: OptIR RV64 spill materialization needs two scratch registers")
	}
	seen := map[int]bool{}
	for _, register := range scratches {
		if register < 0 || seen[register] || allocated[register] {
			return fmt.Errorf("machine: OptIR RV64 spill scratch register %d is invalid, duplicate, or allocated", register)
		}
		seen[register] = true
	}
	return nil
}
