package asm

// noteLoopBodyBounds replays a linear comparison-only loop test on a
// private state, learning the bounds on its continuing side. The ordinary
// loop proof still compares the complete condition and iteration. For a
// rotated loop the recognized, matching entry/tail tests establish the
// same facts before each iteration. No fact learned here escapes into
// the state after the loop, where its exit condition holds instead.
//
// This is used only when the frame-store probe runs: otherwise a newly
// bounded store could change slots that the loop inventory did not carry.
// Headers with calls, loads, register setup or internal forks are left to
// the existing model; there is no speculative execution of their effects.
func (x *pathExecutor) noteLoopBodyBounds(shape loopShape, state *symbolicState) {
	probe := state.clone()
	segments := [][2]int{{shape.testStart, shape.testEnd}}
	if shape.entryEnd > shape.entryStart {
		segments = append([][2]int{{shape.entryStart, shape.entryEnd}}, segments...)
	}
	for _, segment := range segments {
		for pc := segment[0]; pc < segment[1]; pc++ {
			instr, ok := x.items[pc].(Instruction)
			if !ok {
				return
			}
			if isConditionalBranch(instr.Mnemonic) {
				if len(instr.Operands) == 0 {
					return
				}
				sym, ok := instr.Operands[len(instr.Operands)-1].(Symbol)
				if !ok {
					return
				}
				target, known := x.labels[sym.Name]
				switch {
				case known && target == shape.exitLabel:
					noteBranchBound(instr, nil, probe)
				case known && shape.tail && target == shape.header:
					noteBranchBound(instr, probe, nil)
				default:
					return
				}
				continue
			}
			switch instr.Mnemonic {
			case "cmp", "ccmp", "tst":
				if _, ok := step(instr, probe); !ok {
					return
				}
			default:
				return
			}
		}
	}
	state.bounds, state.termBounds = probe.bounds, probe.termBounds
}
