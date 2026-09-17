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
	// MaxTrips is a cost-only trip-bound estimate, 0 when unknown:
	// a constant start against an immediate bound with an unsigned exit,
	// or a smaller-stride remainder after a loop over the same index.
	// Pattern-derived remainder hints are not verification authority.
	MaxTrips int
	// ExactTrips is the positive number of body iterations per entered loop
	// when the conservative CFG/induction recognizer establishes it; zero
	// means unknown. This cost-only hint is not verification authority.
	ExactTrips int
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
				if !ok {
					// A register step: `add rd, rd, rs` with rs a
					// materialized constant (`li t0, 4; addw t1, t1, t0`,
					// the RV64 lane's stride).
					reg, step, ok = f.registerIncrement(ins, siteWeb)
				}
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
							if ow != nil && f.invariantWeb(ow, inLoop, siteWeb, 3) {
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
		if sh.Index == nil && len(sh.Inductions) == 1 {
			// No exit test the analysis reads (a slack guard computed into
			// a flag, `sltu; xori; beqz`), one induction: the loop walks
			// it, so its step is the stride; no trip bound.
			sh.Index = &sh.Inductions[0]
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
		sh.ExactTrips = f.exactLoopTrips(l, dom, siteWeb)
		shapes = append(shapes, sh)
	}
	// Remainder loops: a smaller-stride loop right after a strided loop over
	// the same induction web and the same bound runs fewer than the
	// stride's trips.
	for i := 1; i < len(shapes); i++ {
		cur, prev := shapes[i], shapes[i-1]
		if cur.Index == nil || prev.Index == nil || cur.Index.Step <= 0 || prev.Index.Step <= 0 || cur.Stride >= prev.Stride || cur.MaxTrips != 0 || cur.Loop.Parent != prev.Loop.Parent {
			continue
		}
		sameBound := cur.BoundReg == prev.BoundReg && cur.BoundIsImm == prev.BoundIsImm && (!cur.BoundIsImm || cur.BoundImm == prev.BoundImm)
		// A strided loop whose exit test the analysis could not read (a
		// slack guard computed into a flag) still walks the same index to
		// the same length as the remainder after it: the remainder runs
		// fewer than the stride's trips (a cost, not a proof).
		unreadBound := prev.BoundReg == (Reg{}) && !prev.BoundIsImm
		if cur.Index.Web == prev.Index.Web && (sameBound || unreadBound) && prev.Loop.Header.Index < cur.Loop.Header.Index {
			cur.MaxTrips = (prev.Stride - 1) / cur.Stride
		}
	}
	return shapes, nil
}

// registerIncrement reads `add rd, rd, rs` (or the word form) whose step
// register rs has one definition, a materialized constant: rd advances by
// that constant. The web of rs at this use finds its definition.
func (f *Function) registerIncrement(ins *Instr, siteWeb map[site]*Web) (Reg, int64, bool) {
	a := ins.Asm
	switch a.Mnemonic {
	case "add", "addw", "sub", "subw":
	default:
		return Reg{}, 0, false
	}
	if len(a.Operands) != 3 || len(ins.Defs) != 1 || len(ins.Uses) != 2 {
		return Reg{}, 0, false
	}
	dst := ins.Defs[0]
	if ins.Uses[0].Op != 1 || ins.Uses[0].Reg != dst.Reg || ins.Uses[1].Op != 2 {
		return Reg{}, 0, false
	}
	w := siteWeb[site{ins, ins.Uses[1], false}]
	if w == nil || len(w.Defs) != 1 || w.Defs[0].Instr == nil {
		return Reg{}, 0, false
	}
	c, isConst := f.t.constant(w.Defs[0].Instr.Asm)
	if !isConst {
		return Reg{}, 0, false
	}
	if a.Mnemonic == "sub" || a.Mnemonic == "subw" {
		c = -c
	}
	return dst.Reg, c, true
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

// invariantWeb reports a web whose value is the same every trip: every
// definition lies outside the loop, or is a pure instruction inside it
// computing from invariant webs (a bound like `sub w9, w20, #16` in the
// header), to a small depth.
func (f *Function) invariantWeb(w *Web, inLoop map[*Block]bool, siteWeb map[site]*Web, depth int) bool {
	for _, d := range w.Defs {
		if d.Instr == nil || !inLoop[d.Instr.Block] {
			continue
		}
		if depth == 0 || !f.t.pure(d.Instr.Asm) || f.t.readsFlags(d.Instr.Asm) {
			return false
		}
		for _, op := range d.Instr.Asm.Operands {
			if _, isMem := op.(asm.Memory); isMem {
				return false // a load may see a different value each trip
			}
		}
		for _, u := range d.Instr.Uses {
			uw := siteWeb[site{d.Instr, u, false}]
			if uw == nil || uw == w || !f.invariantWeb(uw, inLoop, siteWeb, depth-1) {
				return false
			}
		}
	}
	return true
}
