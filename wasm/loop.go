package wasm

import "github.com/SCKelemen/oak/optir"

// loopShape covers the entire CFG, not a selected reachable subgraph. No block
// or operation may be omitted because an analysis predicts it will not execute.
type loopShape struct{ header, body, exit optir.Block }

// matchLoop recognizes only entry -> header -> {body -> header, exit -> return}.
// Both condition polarities work. Block order and numeric IDs have no meaning.
// CFG/SSA/type validation must precede this purely structural recognizer.
func (f *function) matchLoop() (loopShape, bool) {
	if len(f.cfg.Blocks) != 4 || f.entry.Terminator.Kind != optir.TerminatorBranch {
		return loopShape{}, false
	}
	header, ok := f.lookupBlock(f.entry.Terminator.True.Target)
	if !ok || header.Terminator.Kind != optir.TerminatorCondBranch {
		return loopShape{}, false
	}
	a, aOK := f.lookupBlock(header.Terminator.True.Target)
	b, bOK := f.lookupBlock(header.Terminator.False.Target)
	if !aOK || !bOK || len(map[optir.BlockID]bool{f.entry.ID: true, header.ID: true, a.ID: true, b.ID: true}) != 4 {
		return loopShape{}, false
	}
	if a.Terminator.Kind == optir.TerminatorReturn {
		a, b = b, a
	}
	if a.Terminator.Kind != optir.TerminatorBranch || a.Terminator.True.Target != header.ID || b.Terminator.Kind != optir.TerminatorReturn {
		return loopShape{}, false
	}
	return loopShape{header: header, body: a, exit: b}, true
}

func (f *function) loopBody(b *binary, loop loopShape, functions map[string]*function) error {
	if err := f.operations(b, f.entry, functions); err != nil {
		return err
	}
	f.edgeValues(b, f.entry.Terminator.True)
	b.op(0x03, 0x40) // loop, no parameters/results
	if err := f.operations(b, loop.header, functions); err != nil {
		return err
	}
	f.get(b, loop.header.Terminator.Condition)
	b.op(0x04, 0x40) // if, no parameters/results
	for i, edge := range []optir.Edge{loop.header.Terminator.True, loop.header.Terminator.False} {
		if i == 1 {
			b.op(0x05) // else
		}
		f.edgeValues(b, edge)
		if edge.Target == loop.body.ID {
			if err := f.operations(b, loop.body, functions); err != nil {
				return err
			}
			f.edgeValues(b, loop.body.Terminator.True)
			b.op(0x0c, 1) // br: past the if label to the enclosing loop
		} else {
			if err := f.operations(b, loop.exit, functions); err != nil {
				return err
			}
			f.returnValue(b, loop.exit.Terminator)
			b.op(0x0f)
		}
	}
	b.op(0x0b, 0x0b, 0x00, 0x0b) // end if; end loop; unreachable; end function
	return nil
}
