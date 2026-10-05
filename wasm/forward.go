package wasm

import (
	"fmt"

	"github.com/SCKelemen/oak/optir"
)

// Forward scopes reserve one control frame for the function and one for an
// operation's signed-division if or a terminator's conditional. The independent
// scalar byte validator caps the total at 128; deeper CFGs retain dispatch.
const maxForwardBlocks = 127

// forwardBody maps a topological CFG schedule to nested forward labels:
//
//	block label C
//	  block label B
//	    A
//	  end
//	  B
//	end
//	C
//
// Each source block is emitted exactly once. A branch exits scopes to reach its
// target, never executes skipped blocks, and never needs a program counter.
// The caller obtains order from optir.AcyclicOrder after CFG/type validation.
func (f *function) forwardBody(b *binary, order []optir.BlockID, functions map[string]*function) error {
	if err := f.forwardRegion(b, order, functions, nil, true); err != nil {
		return err
	}
	b.op(0x0b) // function end returns the final block's result
	return nil
}

// forwardRegion also permits transfers to explicit enclosing labels. Each exit
// depth is measured just outside this region's forward scopes; an edge adds the
// still-open scopes and its own conditional label. No other target is allowed.
// A returning region leaves a result on the stack only at the end of a function;
// inside a loop, every return must explicitly leave the function instead.
func (f *function) forwardRegion(b *binary, order []optir.BlockID, functions map[string]*function, exits map[optir.BlockID]int, returnAtEnd bool) error {
	positions := make(map[optir.BlockID]int, len(order))
	for i, id := range order {
		positions[id] = i
	}
	for i := len(order) - 1; i > 0; i-- {
		b.op(0x02, 0x40) // empty block: values cross edges through SSA locals
	}
	for i, id := range order {
		if i > 0 {
			b.op(0x0b) // target label: the preceding scope has ended
		}
		block, ok := f.lookupBlock(id)
		if !ok {
			return fmt.Errorf("forward schedule names missing block %d", id)
		}
		if err := f.operations(b, block, functions); err != nil {
			return err
		}
		edge := func(e optir.Edge, conditional bool) error {
			target, ok := positions[e.Target]
			depth := target - i - 1
			if ok {
				if target <= i {
					return fmt.Errorf("non-forward edge %d -> %d", id, e.Target)
				}
			} else {
				outer, allowed := exits[e.Target]
				if !allowed || outer < 0 || outer > 127 {
					return fmt.Errorf("unbound region exit %d -> %d", id, e.Target)
				}
				depth = len(order) - i - 1 + outer
			}
			if conditional {
				depth++ // also exit the selected if/else arm
			}
			if depth > 127 {
				return fmt.Errorf("region branch depth exceeds scalar profile")
			}
			if err := f.edgeValues(b, e, functions); err != nil {
				return err
			}
			if ok && target == i+1 && !conditional {
				return nil // unconditional fallthrough to the next label
			}
			b.op(0x0c)
			b.u(uint64(depth))
			return nil
		}
		switch t := block.Terminator; t.Kind {
		case optir.TerminatorReturn:
			if err := f.returnValue(b, t, functions); err != nil {
				return err
			}
			if i != len(order)-1 || !returnAtEnd {
				b.op(0x0f) // early return must skip remaining blocks
			}
		case optir.TerminatorBranch:
			if err := edge(t.True, false); err != nil {
				return err
			}
		case optir.TerminatorCondBranch:
			if err := f.emitValue(b, t.Condition, functions); err != nil {
				return err
			}
			b.op(0x04, 0x40)
			if err := edge(t.True, true); err != nil {
				return err
			}
			b.op(0x05)
			if err := edge(t.False, true); err != nil {
				return err
			}
			b.op(0x0b)
		default:
			return fmt.Errorf("unsupported forward terminator %s", t.Kind)
		}
	}
	return nil
}
