package machine

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
)

// Recurrence analysis over the lifted IR
// (docs/notes/optimizer-search-2026-09.md §10.2, the ScalarEvolution-like
// analysis scoped to Oak's needs): the basic induction variables of each
// natural loop, their steps and initial values, the exit test's bound,
// and a trip bound where one follows without arithmetic the machine
// could wrap. It changes no code; the cost model and the loop planners
// read it.

// Induction is a basic induction variable of a loop: a register advanced
// by one constant step once per trip.
type Induction struct {
	Web  *Web
	Reg  Reg
	Step int64 // the change per trip, signed
	// Increment is the instruction that advances it.
	Increment *Instr
	// Start is the initial value when its only definition outside the
	// loop materializes a constant; StartKnown says so.
	Start      int64
	StartKnown bool
}

// LoopShape is what the analysis says of one loop.
type LoopShape struct {
	Loop       *Loop
	Header     string // the header's label, "" when it has none
	Inductions []Induction
	// Index is the induction the exit test compares, if any.
	Index *Induction
	// Bound is the exit test's other operand: a loop-invariant register
	// (BoundReg) or an immediate (BoundImm, BoundIsImm).
	BoundReg   Reg
	BoundImm   int64
	BoundIsImm bool
	// Stride is the elements one trip advances the index by (|Step|), 1
	// when there is no index.
	Stride int
	// MaxTrips bounds the trips when the shape does, 0 when it does not:
	// a constant start against an immediate bound with an unsigned exit,
	// or the remainder loop after a strided loop over the same index.
	MaxTrips int
}

// Shapes analyzes the loops of a lifted function.
func (f *Function) Shapes() ([]*LoopShape, error) {
	webs, err := f.Webs()
	if err != nil {
		return nil, err
	}
	dom := f.Dominators()
	loops := dom.Loops()
	siteWeb := map[site]*Web{}
	for _, w := range webs {
		for _, d := range w.Defs {
			if d.Instr != nil {
				siteWeb[site{d.Instr, d.Access, true}] = w
			}
		}
		for _, u := range w.Uses {
			siteWeb[site{u.Instr, u.Access, false}] = w
		}
	}
	var shapes []*LoopShape
	for _, l := range loops {
		sh := &LoopShape{Loop: l, Header: l.Header.Label, Stride: 1}
		inLoop := map[*Block]bool{}
		for _, b := range l.Blocks {
			inLoop[b] = true
		}
		// Induction variables: one increment inside the loop, by a
		// constant, executed every trip; every other definition outside.
		for _, b := range l.Blocks {
			for _, ins := range b.Instrs {
				reg, step, ok := f.t.increment(ins.Asm)
				if !ok || len(ins.Defs) != 1 {
					continue
				}
				w := siteWeb[site{ins, ins.Defs[0], true}]
				if w == nil || w.Reg != reg {
					continue
				}
				inside := 0
				for _, d := range w.Defs {
					if d.Instr != nil && inLoop[d.Instr.Block] {
						inside++
					}
				}
				if inside != 1 {
					continue
				}
				everyTrip := true
				for _, latch := range l.Latches {
					if !dom.Dominates(b, latch) {
						everyTrip = false
					}
				}
				if !everyTrip {
					continue
				}
				iv := Induction{Web: w, Reg: reg, Step: step, Increment: ins}
				var outside []site
				for _, d := range w.Defs {
					if d.Instr == nil || !inLoop[d.Instr.Block] {
						outside = append(outside, d)
					}
				}
				if len(outside) == 1 && outside[0].Instr != nil {
					if c, isConst := f.t.constant(outside[0].Instr.Asm); isConst {
						iv.Start, iv.StartKnown = c, true
					}
				}
				sh.Inductions = append(sh.Inductions, iv)
			}
		}
		// The exit test: a compare in a block dominating the latches
		// whose operands are an induction and an invariant.
		for _, b := range l.Blocks {
			dominatesLatches := true
			for _, latch := range l.Latches {
				if !dom.Dominates(b, latch) {
					dominatesLatches = false
				}
			}
			if !dominatesLatches {
				continue
			}
			for _, ins := range b.Instrs {
				regs, imm, hasImm, ok := f.t.exitTest(ins.Asm)
				if !ok {
					continue
				}
				for k := range sh.Inductions {
					iv := &sh.Inductions[k]
					for i, r := range regs {
						if r != iv.Reg || siteWeb[site{ins, ins.Uses[i], false}] != iv.Web {
							continue
						}
						sh.Index = iv
						if hasImm {
							sh.BoundImm, sh.BoundIsImm = imm, true
						} else if len(regs) == 2 {
							other := regs[1-i]
							ow := siteWeb[site{ins, ins.Uses[1-i], false}]
							invariant := ow != nil
							if ow != nil {
								for _, d := range ow.Defs {
									if d.Instr != nil && inLoop[d.Instr.Block] {
										invariant = false
									}
								}
							}
							if invariant {
								sh.BoundReg = other
							} else {
								sh.Index = nil
							}
						}
					}
				}
				if sh.Index != nil {
					break
				}
			}
			if sh.Index != nil {
				break
			}
		}
		if sh.Index != nil {
			if sh.Index.Step < 0 {
				sh.Stride = int(-sh.Index.Step)
			} else {
				sh.Stride = int(sh.Index.Step)
			}
			if sh.Stride == 0 {
				sh.Stride = 1
			}
			// A trip bound only where the arithmetic cannot wrap: a known
			// start, an immediate bound, a positive step, in int64.
			if sh.Index.StartKnown && sh.BoundIsImm && sh.Index.Step > 0 && sh.BoundImm >= sh.Index.Start {
				span := sh.BoundImm - sh.Index.Start
				if span >= 0 && span <= 1<<40 {
					trips := (span + sh.Index.Step - 1) / sh.Index.Step
					if trips > 0 && trips <= 1<<31 {
						sh.MaxTrips = int(trips)
					}
				}
			}
		}
		shapes = append(shapes, sh)
	}
	// Remainder loops: a stride-one loop right after a strided loop over
	// the same induction web and the same bound runs fewer than the
	// stride's trips.
	for i := 1; i < len(shapes); i++ {
		cur, prev := shapes[i], shapes[i-1]
		if cur.Index == nil || prev.Index == nil || cur.Stride != 1 || prev.Stride <= 1 || cur.MaxTrips != 0 {
			continue
		}
		if cur.Index.Web == prev.Index.Web && cur.BoundReg == prev.BoundReg && cur.BoundIsImm == prev.BoundIsImm && prev.Loop.Header.Index < cur.Loop.Header.Index {
			cur.MaxTrips = prev.Stride - 1
		}
	}
	return shapes, nil
}

// LoopShapes lifts a lowered body and analyzes its loops. An error means
// the lift refused the body; the caller falls back to its own reading.
func LoopShapes(fn *asm.Function) ([]*LoopShape, error) {
	lifted, err := Lift(cloneFunction(fn))
	if err != nil {
		return nil, err
	}
	return lifted.Shapes()
}

// String spells a shape for the report.
func (s *LoopShape) String() string {
	out := fmt.Sprintf("loop %s: stride %d", s.Header, s.Stride)
	if s.Index != nil {
		out += fmt.Sprintf(", index %s step %d", s.Index.Reg, s.Index.Step)
		if s.Index.StartKnown {
			out += fmt.Sprintf(" from %d", s.Index.Start)
		}
		if s.BoundIsImm {
			out += fmt.Sprintf(" to #%d", s.BoundImm)
		} else {
			out += fmt.Sprintf(" to %s", s.BoundReg)
		}
	}
	if s.MaxTrips > 0 {
		out += fmt.Sprintf(", <= %d trips", s.MaxTrips)
	}
	return out
}
