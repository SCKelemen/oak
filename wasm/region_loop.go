package wasm

import "github.com/SCKelemen/oak/optir"

// The body nests inside an exit block, loop and header if, in addition to the
// function/operation frames already reserved by forward lowering.
const maxLoopRegionBlocks = maxForwardBlocks - 3

type regionLoopShape struct {
	header, exit optir.Block
	body         []optir.BlockID
}

// matchRegionLoop composes a pre-test loop with a forward body region. Its
// entry/header/returning exit and region must exhaust the whole CFG. No nested
// or irreducible cycle may be hidden by constant conditions or a partial order.
func (f *function) matchRegionLoop() (regionLoopShape, bool, error) {
	if f.entry.Terminator.Kind != optir.TerminatorBranch || len(f.cfg.Blocks) < 4 || len(f.cfg.Blocks) > maxLoopRegionBlocks+3 {
		return regionLoopShape{}, false, nil
	}
	header, ok := f.lookupBlock(f.entry.Terminator.True.Target)
	if !ok || header.Terminator.Kind != optir.TerminatorCondBranch {
		return regionLoopShape{}, false, nil
	}
	start, aOK := f.lookupBlock(header.Terminator.True.Target)
	exit, bOK := f.lookupBlock(header.Terminator.False.Target)
	if !aOK || !bOK {
		return regionLoopShape{}, false, nil
	}
	if start.Terminator.Kind == optir.TerminatorReturn {
		start, exit = exit, start
	}
	if exit.Terminator.Kind != optir.TerminatorReturn || len(map[optir.BlockID]bool{f.entry.ID: true, header.ID: true, start.ID: true, exit.ID: true}) != 4 {
		return regionLoopShape{}, false, nil
	}
	body, err := optir.AcyclicRegionOrder(f.cfg, start.ID, []optir.BlockID{header.ID, exit.ID})
	if err != nil {
		return regionLoopShape{}, false, err
	}
	if len(body) == 0 || len(body)+3 != len(f.cfg.Blocks) {
		return regionLoopShape{}, false, nil
	}
	backedge := false
	for _, id := range body {
		if id == f.entry.ID {
			return regionLoopShape{}, false, nil
		}
		block, _ := f.lookupBlock(id)
		t := block.Terminator
		if ((t.Kind == optir.TerminatorBranch || t.Kind == optir.TerminatorCondBranch) && t.True.Target == header.ID) ||
			(t.Kind == optir.TerminatorCondBranch && t.False.Target == header.ID) {
			backedge = true
		}
	}
	if !backedge {
		return regionLoopShape{}, false, nil
	}
	return regionLoopShape{header: header, exit: exit, body: body}, true, nil
}

func (f *function) regionLoopBody(b *binary, loop regionLoopShape, functions map[string]*function) error {
	if err := f.operations(b, f.entry, functions); err != nil {
		return err
	}
	if err := f.edgeValues(b, f.entry.Terminator.True, functions); err != nil {
		return err
	}
	b.op(0x02, 0x40, 0x03, 0x40) // outer exit block; repeating header loop
	if err := f.operations(b, loop.header, functions); err != nil {
		return err
	}
	if err := f.emitValue(b, loop.header.Terminator.Condition, functions); err != nil {
		return err
	}
	b.op(0x04, 0x40)
	for i, edge := range []optir.Edge{loop.header.Terminator.True, loop.header.Terminator.False} {
		if i == 1 {
			b.op(0x05)
		}
		if err := f.edgeValues(b, edge, functions); err != nil {
			return err
		}
		if edge.Target == loop.exit.ID {
			b.op(0x0c, 2) // leave if, loop and outer exit block
		} else {
			if err := f.forwardRegion(b, loop.body, functions, map[optir.BlockID]int{loop.header.ID: 1, loop.exit.ID: 2}, false); err != nil {
				return err
			}
		}
	}
	b.op(0x0b, 0x0b, 0x0b) // end header if, loop and exit block
	if err := f.operations(b, loop.exit, functions); err != nil {
		return err
	}
	if err := f.returnValue(b, loop.exit.Terminator, functions); err != nil {
		return err
	}
	b.op(0x0b) // function end
	return nil
}
