package optir

import "fmt"

// AcyclicOrder returns a deterministic forward order of every block in a valid
// acyclic CFG. A valid cyclic CFG returns nil, nil, not a partial schedule.
// Invalid CFGs return an error. This is a topology analysis, not permission to
// omit operations or to reorder their execution. It does not use constant facts.
// The order depends on edge polarity, not numeric IDs or CFG slice order.
func AcyclicOrder(cfg CFG) ([]BlockID, error) {
	return AcyclicRegionOrder(cfg, cfg.Entry, nil)
}

// AcyclicRegionOrder schedules the region reachable from entry without crossing
// any boundary block. Boundaries are excluded from the order, but incoming edges
// to them remain the caller's responsibility. This is analysis, not a CFG rewrite
// or authorization to omit code outside the region. A cycle within the region
// returns nil, nil; the whole CFG and all requested block IDs must be valid.
func AcyclicRegionOrder(cfg CFG, entry BlockID, boundaries []BlockID) ([]BlockID, error) {
	if err := Verify(cfg); err != nil {
		return nil, err
	}
	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	for i := range cfg.Blocks {
		blocks[cfg.Blocks[i].ID] = &cfg.Blocks[i]
	}
	if blocks[entry] == nil {
		return nil, fmt.Errorf("optir: missing region entry %d", entry)
	}
	stops := make(map[BlockID]bool, len(boundaries))
	for _, id := range boundaries {
		if blocks[id] == nil || id == entry || stops[id] {
			return nil, fmt.Errorf("optir: invalid or repeated region boundary %d", id)
		}
		stops[id] = true
		// The traversal reads only terminator edges. Stop at a copied boundary
		// node without touching the actual CFG, its SSA uses or its operations.
		boundary := *blocks[id]
		boundary.Terminator = Terminator{Kind: TerminatorReturn}
		blocks[id] = &boundary
	}
	// Reuse the iterative traversal used by loop and memory analyses. Reverse
	// postorder is topological exactly when every edge in it goes forward.
	visited := loopReversePostOrder(entry, blocks)
	order := make([]BlockID, 0, len(visited))
	for _, id := range visited {
		if !stops[id] {
			order = append(order, id)
		}
	}
	positions := make(map[BlockID]int, len(order))
	for i, id := range order {
		positions[id] = i
	}
	for _, id := range order {
		block := blocks[id]
		for _, edge := range transformEdges(block.Terminator) {
			if !stops[edge.Target] && positions[edge.Target] <= positions[block.ID] {
				return nil, nil
			}
		}
	}
	return order, nil
}
