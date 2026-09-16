package optir

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
)

// BranchReason explains the target-independent evidence behind one static
// branch estimate. A neutral branch carries no semantic or profile claim.
type BranchReason string

const (
	BranchNeutral      BranchReason = "neutral"
	BranchLoopBackedge BranchReason = "loop-backedge"
	BranchLoopStay     BranchReason = "loop-stay"
)

const (
	neutralBranchWeight uint8 = 1
	likelyBranchWeight  uint8 = 8
)

// BranchProbability is a deterministic integer-weight estimate for one
// conditional branch. The weights are deliberately qualitative: they guide
// layout but are never transformation or emission permission.
type BranchProbability struct {
	Block       BlockID
	TrueWeight  uint8
	FalseWeight uint8
	Reason      BranchReason
}

// BlockLayout is a target-independent physical ordering proposal. Order is an
// exact permutation of the CFG's reachable blocks and never changes an edge.
// Private identity fields prevent mutated or stale evidence from being reused.
type BlockLayout struct {
	Order         []BlockID
	Probabilities []BranchProbability

	inputFingerprint string
	integrity        string
}

// AnalyzeBlockLayout estimates only conventional loop behavior: a unique
// conditional backedge is likely, and otherwise an edge that remains in the
// innermost containing natural loop is likely relative to an exit. All other
// conditionals remain neutral. Deterministic traces then keep preferred edges
// adjacent where possible.
func AnalyzeBlockLayout(cfg CFG) (BlockLayout, error) {
	if err := Verify(cfg); err != nil {
		return BlockLayout{}, err
	}
	structure, err := AnalyzeLoopStructure(cfg)
	if err != nil {
		return BlockLayout{}, err
	}

	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	for index := range cfg.Blocks {
		blocks[cfg.Blocks[index].ID] = &cfg.Blocks[index]
	}
	backedges := make(map[FlowEdge]bool, len(structure.BackEdges))
	for _, edge := range structure.BackEdges {
		backedges[edge] = true
	}

	probabilities := make([]BranchProbability, 0)
	byBlock := make(map[BlockID]BranchProbability)
	for _, id := range sortedBlockIDs(blocks) {
		block := blocks[id]
		if block.Terminator.Kind != TerminatorCondBranch {
			continue
		}
		probability := BranchProbability{
			Block: id, TrueWeight: neutralBranchWeight,
			FalseWeight: neutralBranchWeight, Reason: BranchNeutral,
		}
		trueBackedge := backedges[FlowEdge{From: id, To: block.Terminator.True.Target}]
		falseBackedge := backedges[FlowEdge{From: id, To: block.Terminator.False.Target}]
		switch {
		case trueBackedge != falseBackedge:
			probability.Reason = BranchLoopBackedge
			if trueBackedge {
				probability.TrueWeight = likelyBranchWeight
			} else {
				probability.FalseWeight = likelyBranchWeight
			}
		default:
			loop, ok := innermostContainingLoop(structure.Loops, id)
			if ok {
				members := blockIDSet(loop.Blocks)
				trueStays := members[block.Terminator.True.Target]
				falseStays := members[block.Terminator.False.Target]
				if trueStays != falseStays {
					probability.Reason = BranchLoopStay
					if trueStays {
						probability.TrueWeight = likelyBranchWeight
					} else {
						probability.FalseWeight = likelyBranchWeight
					}
				}
			}
		}
		probabilities = append(probabilities, probability)
		byBlock[id] = probability
	}

	layout := BlockLayout{
		Order:            traceBlockOrder(cfg.Entry, blocks, structure.ReversePostOrder, byBlock, nonBackedgePredecessors(blocks, backedges)),
		Probabilities:    probabilities,
		inputFingerprint: fingerprintCFG(cfg),
	}
	layout.integrity = fingerprintBlockLayout(layout)
	if err := VerifyBlockLayout(cfg, layout); err != nil {
		return BlockLayout{}, fmt.Errorf("optir: internally invalid block layout: %w", err)
	}
	return layout, nil
}

// VerifyBlockLayout checks exact CFG ownership, evidence integrity, and the
// permutation invariant before a backend consumes a layout proposal.
func VerifyBlockLayout(cfg CFG, layout BlockLayout) error {
	if err := Verify(cfg); err != nil {
		return err
	}
	if layout.inputFingerprint == "" || layout.inputFingerprint != fingerprintCFG(cfg) {
		return fmt.Errorf("optir: block layout belongs to a different CFG")
	}
	if layout.integrity == "" || layout.integrity != fingerprintBlockLayout(layout) {
		return fmt.Errorf("optir: block layout was mutated")
	}
	if len(layout.Order) != len(cfg.Blocks) {
		return fmt.Errorf("optir: block layout contains %d blocks, want %d", len(layout.Order), len(cfg.Blocks))
	}
	if len(layout.Order) == 0 || layout.Order[0] != cfg.Entry {
		return fmt.Errorf("optir: block layout does not begin at entry block %d", cfg.Entry)
	}
	blocks := make(map[BlockID]bool, len(cfg.Blocks))
	for _, block := range cfg.Blocks {
		blocks[block.ID] = true
	}
	seen := make(map[BlockID]bool, len(layout.Order))
	for _, block := range layout.Order {
		if !blocks[block] {
			return fmt.Errorf("optir: block layout names missing block %d", block)
		}
		if seen[block] {
			return fmt.Errorf("optir: block layout repeats block %d", block)
		}
		seen[block] = true
	}

	conditional := make(map[BlockID]bool)
	for _, block := range cfg.Blocks {
		conditional[block.ID] = block.Terminator.Kind == TerminatorCondBranch
	}
	previous := BlockID(0)
	for index, probability := range layout.Probabilities {
		if !conditional[probability.Block] {
			return fmt.Errorf("optir: branch probability names non-conditional block %d", probability.Block)
		}
		if index > 0 && probability.Block <= previous {
			return fmt.Errorf("optir: branch probabilities are not in canonical block order")
		}
		if probability.TrueWeight == 0 || probability.FalseWeight == 0 {
			return fmt.Errorf("optir: branch probability for block %d has zero weight", probability.Block)
		}
		delete(conditional, probability.Block)
		previous = probability.Block
	}
	for block, isConditional := range conditional {
		if isConditional {
			return fmt.Errorf("optir: block layout has no probability for conditional block %d", block)
		}
	}
	return nil
}

func innermostContainingLoop(loops []NaturalLoop, block BlockID) (NaturalLoop, bool) {
	var result NaturalLoop
	found := false
	for _, loop := range loops {
		if !containsBlockID(loop.Blocks, block) {
			continue
		}
		if !found || loop.Depth > result.Depth || loop.Depth == result.Depth && loop.Header < result.Header {
			result, found = loop, true
		}
	}
	return result, found
}

func blockIDSet(ids []BlockID) map[BlockID]bool {
	result := make(map[BlockID]bool, len(ids))
	for _, id := range ids {
		result[id] = true
	}
	return result
}

func traceBlockOrder(entry BlockID, blocks map[BlockID]*Block, reversePostOrder []BlockID, probabilities map[BlockID]BranchProbability, predecessors map[BlockID][]BlockID) []BlockID {
	seeds := append([]BlockID(nil), reversePostOrder...)
	sorted := sortedBlockIDs(blocks)
	seeds = append(seeds, sorted...)
	visited := make(map[BlockID]bool, len(blocks))
	order := make([]BlockID, 0, len(blocks))

	follow := func(seed BlockID) {
		for !visited[seed] {
			visited[seed] = true
			order = append(order, seed)
			successors := layoutSuccessors(*blocks[seed], probabilities[seed])
			next, found := BlockID(0), false
			for _, successor := range successors {
				if !visited[successor] && layoutPredecessorsReady(predecessors[successor], visited) {
					next, found = successor, true
					break
				}
			}
			if !found {
				return
			}
			seed = next
		}
	}
	follow(entry)
	for _, seed := range seeds {
		follow(seed)
	}
	return order
}

func nonBackedgePredecessors(blocks map[BlockID]*Block, backedges map[FlowEdge]bool) map[BlockID][]BlockID {
	sets := make(map[BlockID]map[BlockID]bool, len(blocks))
	for _, from := range sortedBlockIDs(blocks) {
		for _, edge := range transformEdges(blocks[from].Terminator) {
			if backedges[FlowEdge{From: from, To: edge.Target}] {
				continue
			}
			if sets[edge.Target] == nil {
				sets[edge.Target] = map[BlockID]bool{}
			}
			sets[edge.Target][from] = true
		}
	}
	result := make(map[BlockID][]BlockID, len(sets))
	for block, incoming := range sets {
		result[block] = sortedBlockIDs(incoming)
	}
	return result
}

func layoutPredecessorsReady(predecessors []BlockID, visited map[BlockID]bool) bool {
	for _, predecessor := range predecessors {
		if !visited[predecessor] {
			return false
		}
	}
	return true
}

func layoutSuccessors(block Block, probability BranchProbability) []BlockID {
	switch block.Terminator.Kind {
	case TerminatorBranch:
		return []BlockID{block.Terminator.True.Target}
	case TerminatorCondBranch:
		trueTarget, falseTarget := block.Terminator.True.Target, block.Terminator.False.Target
		if trueTarget == falseTarget {
			return []BlockID{trueTarget}
		}
		if probability.TrueWeight > probability.FalseWeight {
			return []BlockID{trueTarget, falseTarget}
		}
		if probability.FalseWeight > probability.TrueWeight {
			return []BlockID{falseTarget, trueTarget}
		}
		if trueTarget < falseTarget {
			return []BlockID{trueTarget, falseTarget}
		}
		return []BlockID{falseTarget, trueTarget}
	default:
		return nil
	}
}

func fingerprintBlockLayout(layout BlockLayout) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.block-layout.v1")
	fingerprintString(digest, layout.inputFingerprint)
	fingerprintBlockIDs(digest, layout.Order)
	fingerprintUint64(digest, uint64(len(layout.Probabilities)))
	for _, probability := range layout.Probabilities {
		fingerprintUint64(digest, uint64(probability.Block))
		fingerprintUint64(digest, uint64(probability.TrueWeight))
		fingerprintUint64(digest, uint64(probability.FalseWeight))
		fingerprintString(digest, string(probability.Reason))
	}
	return hex.EncodeToString(digest.Sum(nil))
}
