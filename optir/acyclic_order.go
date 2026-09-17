package optir

// AcyclicOrder returns a deterministic forward order of every block in a valid
// acyclic CFG. A valid cyclic CFG returns nil, nil, not a partial schedule.
// Invalid CFGs return an error. This is a topology analysis, not permission to
// omit operations or to reorder their execution. It does not use constant facts.
// The order depends on edge polarity, not numeric IDs or CFG slice order.
func AcyclicOrder(cfg CFG) ([]BlockID, error) {
	if err := Verify(cfg); err != nil {
		return nil, err
	}
	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	for i := range cfg.Blocks {
		blocks[cfg.Blocks[i].ID] = &cfg.Blocks[i]
	}
	// Reuse the iterative traversal used by loop and memory analyses. Reverse
	// postorder is topological exactly when every edge in it goes forward.
	order := loopReversePostOrder(cfg.Entry, blocks)
	positions := make(map[BlockID]int, len(order))
	for i, id := range order {
		positions[id] = i
	}
	for _, block := range cfg.Blocks {
		for _, edge := range transformEdges(block.Terminator) {
			if positions[edge.Target] <= positions[block.ID] {
				return nil, nil
			}
		}
	}
	return order, nil
}
