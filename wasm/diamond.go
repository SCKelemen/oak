package wasm

import "github.com/SCKelemen/oak/optir"

type diamondShape struct{ whenTrue, whenFalse, merge optir.Block }

// matchDiamond covers exactly entry -> {true, false} -> merge -> return.
// All four blocks must be distinct. No additional block, even one predicted
// unreachable, may disappear. CFG/SSA/type validation precedes recognition.
func (f *function) matchDiamond() (diamondShape, bool) {
	if len(f.cfg.Blocks) != 4 || f.entry.Terminator.Kind != optir.TerminatorCondBranch {
		return diamondShape{}, false
	}
	a, aOK := f.lookupBlock(f.entry.Terminator.True.Target)
	b, bOK := f.lookupBlock(f.entry.Terminator.False.Target)
	if !aOK || !bOK || a.Terminator.Kind != optir.TerminatorBranch || b.Terminator.Kind != optir.TerminatorBranch || a.Terminator.True.Target != b.Terminator.True.Target {
		return diamondShape{}, false
	}
	merge, ok := f.lookupBlock(a.Terminator.True.Target)
	if !ok || merge.Terminator.Kind != optir.TerminatorReturn || len(map[optir.BlockID]bool{f.entry.ID: true, a.ID: true, b.ID: true, merge.ID: true}) != 4 {
		return diamondShape{}, false
	}
	return diamondShape{whenTrue: a, whenFalse: b, merge: merge}, true
}

func (f *function) diamondBody(b *binary, diamond diamondShape, functions map[string]*function) error {
	if err := f.operations(b, f.entry, functions); err != nil {
		return err
	}
	f.get(b, f.entry.Terminator.Condition)
	b.op(0x04, 0x40) // if with empty stack result; phi values use SSA locals
	for i, arm := range []optir.Block{diamond.whenTrue, diamond.whenFalse} {
		edge := f.entry.Terminator.True
		if i == 1 {
			b.op(0x05) // else: only this chosen arm's operations may execute
			edge = f.entry.Terminator.False
		}
		f.edgeValues(b, edge)
		if err := f.operations(b, arm, functions); err != nil {
			return err
		}
		f.edgeValues(b, arm.Terminator.True)
	}
	b.op(0x0b)
	if err := f.operations(b, diamond.merge, functions); err != nil {
		return err
	}
	f.returnValue(b, diamond.merge.Terminator)
	b.op(0x0b) // merge executes once, then the function returns its result
	return nil
}
