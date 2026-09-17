package machine

import "github.com/SCKelemen/oak/asm"

// Post-allocation instruction scheduling over the lifted IR
// (docs/notes/optimizer-search-2026-09.md §16 Phase B item 13): within a
// block, between barriers, instructions reorder so a value's consumer
// follows its producer by at least the producer's latency where the
// region has independent work to fill the gap — a load's result used
// three instructions later instead of the next one. The dependences come
// from the lift's definitions and uses, a pseudo-register for the
// condition flags, and a conservative memory order (a store keeps its
// place against every other memory instruction; loads may pass loads).
// The schedule is a candidate like any other: the checker and the
// verifier judge it.

// flagsReg is the pseudo-register of the condition flags.
var flagsReg = Reg{Class: 9, Num: 0}

// Schedule reorders the instructions of every block and reports how many
// left their original position. The function is rewritten in place.
func (f *Function) Schedule() int {
	f.regs = f.regsOfAll()
	defer func() { f.regs = nil }()
	moved := 0
	for _, b := range f.Blocks {
		moved += f.scheduleBlock(b)
	}
	if moved > 0 {
		f.reindex()
	}
	return moved
}

// scheduleBlock schedules one block region by region: a region ends at a
// barrier (a call, a return, a trap, a branch, a memory barrier, an
// atomic, an sp write, a system instruction), which keeps its place.
func (f *Function) scheduleBlock(b *Block) int {
	n := len(b.Instrs)
	if n < 3 {
		return 0
	}
	moved := 0
	var out []*Instr
	start := 0
	for i := 0; i <= n; i++ {
		if i < n && !f.t.barrier(b.Instrs[i]) && !f.t.writesFlags(b.Instrs[i].Asm) {
			continue
		}
		// A compare keeps its place too, so the verifier's loop and
		// condition shapes (a compare and its branch) survive the schedule.
		region := b.Instrs[start:i]
		scheduled := f.scheduleRegion(region)
		for k := range scheduled {
			if scheduled[k] != region[k] {
				moved++
			}
		}
		out = append(out, scheduled...)
		if i < n {
			out = append(out, b.Instrs[i])
		}
		start = i + 1
	}
	b.Instrs = out
	return moved
}

// scheduleRegion list-schedules one barrier-free region by critical
// path, ties in original order. Instructions the checker reads as one
// idiom (target.bonded) schedule as one unit.
func (f *Function) scheduleRegion(region []*Instr) []*Instr {
	units := f.units(region)
	n := len(units)
	if n < 2 {
		return region
	}
	preds := make([][]int, n)
	weights := make([][]int, n)
	succs := make([][]int, n)
	for j := 1; j < n; j++ {
		for i := j - 1; i >= 0; i-- {
			w, dep := 0, false
			for _, a := range units[i] {
				for _, b := range units[j] {
					if wab, dab := f.dependence(a, b); dab {
						dep = true
						if wab > w {
							w = wab
						}
					}
				}
			}
			if dep {
				preds[j] = append(preds[j], i)
				weights[j] = append(weights[j], w)
				succs[i] = append(succs[i], j)
			}
		}
	}
	// Priority: the longest latency path from the unit to the region's
	// end, a unit's latency its last instruction's.
	priority := make([]int, n)
	for i := n - 1; i >= 0; i-- {
		lat := f.t.latency(units[i][len(units[i])-1].Asm)
		priority[i] = lat
		for _, s := range succs[i] {
			if p := lat + priority[s]; p > priority[i] {
				priority[i] = p
			}
		}
	}
	scheduled := make([]bool, n)
	cycleOf := make([]int, n)
	out := make([]*Instr, 0, len(region))
	cycle := 0
	for len(out) < len(region) {
		best, bestReady := -1, 0
		for i := 0; i < n; i++ {
			if scheduled[i] {
				continue
			}
			ready, ok := 0, true
			for k, p := range preds[i] {
				if !scheduled[p] {
					ok = false
					break
				}
				if at := cycleOf[p] + weights[i][k]; at > ready {
					ready = at
				}
			}
			if !ok {
				continue
			}
			if best < 0 {
				best, bestReady = i, ready
				continue
			}
			// Prefer a unit ready now with the longest path; among those
			// not yet ready, the one ready first; ties keep order.
			nowBest, nowI := bestReady <= cycle, ready <= cycle
			switch {
			case nowI && !nowBest:
				best, bestReady = i, ready
			case nowI == nowBest && (priority[i] > priority[best] || (priority[i] == priority[best] && ready < bestReady)):
				best, bestReady = i, ready
			}
		}
		if bestReady > cycle {
			cycle = bestReady
		}
		scheduled[best] = true
		cycleOf[best] = cycle
		out = append(out, units[best]...)
		cycle += len(units[best])
	}
	return out
}

// units groups a region into the units the scheduler moves: each
// instruction alone, or with the next when the target bonds the two.
func (f *Function) units(region []*Instr) [][]*Instr {
	var out [][]*Instr
	for i := 0; i < len(region); i++ {
		if i+1 < len(region) && f.t.bonded != nil && f.t.bonded(region[i].Asm, region[i+1].Asm) {
			out = append(out, []*Instr{region[i], region[i+1]})
			i++
			continue
		}
		out = append(out, []*Instr{region[i]})
	}
	return out
}

// dependence reports whether b must stay after a, and the cycles b must
// wait after a issues. The instructions' registers are f.regs's, computed
// once for the scheduling (Schedule): the region scheduler asks for
// every pair, and two maps per instruction per pair were the scheduler's
// time.
func (f *Function) dependence(a, b *Instr) (int, bool) {
	weight, dep := 0, false
	ra, rb := &f.regs[a.Index], &f.regs[b.Index]
	for _, r := range ra.defs {
		if hasReg(rb.uses, r) { // read after write
			dep = true
			if lat := f.t.latency(a.Asm); lat > weight {
				weight = lat
			}
		}
		if hasReg(rb.defs, r) { // write after write
			dep = true
		}
	}
	for _, r := range ra.uses {
		if hasReg(rb.defs, r) { // write after read
			dep = true
		}
	}
	// Memory: a store orders against every memory instruction.
	if ra.mem && rb.mem && (ra.store || rb.store) {
		dep = true
	}
	return weight, dep
}

func hasReg(regs []Reg, r Reg) bool {
	for _, x := range regs {
		if x == r {
			return true
		}
	}
	return false
}

// instrRegs is an instruction's registers as the scheduler reads them:
// the ones it writes and reads, including the flags pseudo-register (sp
// and the zero register are not lifted as registers: an sp write is a
// barrier, an sp read — a frame access — needs no edge), and whether it
// touches memory and stores.
type instrRegs struct {
	defs, uses []Reg
	mem, store bool
}

// regsOfAll collects every instruction's registers, indexed by the
// instruction's index.
func (f *Function) regsOfAll() []instrRegs {
	regs := make([]instrRegs, len(f.Instrs))
	for _, ins := range f.Instrs {
		r := &regs[ins.Index]
		for _, d := range ins.Defs {
			r.defs = append(r.defs, d.Reg)
		}
		for _, u := range ins.Uses {
			r.uses = append(r.uses, u.Reg)
		}
		if f.t.writesFlags(ins.Asm) {
			r.defs = append(r.defs, flagsReg)
		}
		if f.t.readsFlags(ins.Asm) || (ins.Branch && f.t.conditional(ins.Asm)) {
			r.uses = append(r.uses, flagsReg)
		}
		r.mem, r.store = memoryOf(ins.Asm)
	}
	return regs
}

// memoryOf reports whether an instruction touches memory and whether it
// stores (a memory instruction with no register result).
func memoryOf(a asm.Instruction) (mem bool, store bool) {
	for _, op := range a.Operands {
		if _, ok := op.(asm.Memory); ok {
			mem = true
		}
	}
	if !mem {
		return false, false
	}
	sh, known := shapes[a.Mnemonic]
	if !known {
		sh, known = rv64Shapes[a.Mnemonic]
	}
	return true, known && len(sh.defs) == 0
}

// Stalls estimates, in the current order, the cycles an in-order machine
// waits for producers: the sum over read-after-write pairs, at most eight
// instructions apart in the function's linear order, of the latency the
// distance does not cover. It reports the total and the share per block
// (the consumer's). The measure runs across barriers and block
// boundaries alike — a guard branch between a divide and its consumer
// hides none of the divide's latency on the path that falls through —
// so a form with fewer guards is not charged the stalls its branches
// merely interrupted. A pair whose two instructions lie in different
// loops (a preheader's load consumed by the body's first instruction)
// counts once, in the total, and in no block: the block share is what a
// loop pays every trip, so it holds only pairs that run together.
func (f *Function) Stalls() (total int, byBlock map[*Block]int) {
	byBlock = map[*Block]int{}
	var instrs []*Instr
	blockOf := map[*Instr]*Block{}
	for _, b := range f.Blocks {
		for _, ins := range b.Instrs {
			instrs = append(instrs, ins)
			blockOf[ins] = b
		}
	}
	// The innermost loop of each block, for the pairs that run together.
	loopOf := map[*Block]*Loop{}
	for _, l := range f.Dominators().Loops() {
		for _, b := range l.Blocks {
			if cur, ok := loopOf[b]; !ok || len(l.Blocks) < len(cur.Blocks) {
				loopOf[b] = l
			}
		}
	}
	regs := f.regsOfAll()
	for j := 1; j < len(instrs); j++ {
		bUses := regs[instrs[j].Index].uses
		for k := j - 1; k >= 0 && j-k <= 8; k-- {
			for _, r := range regs[instrs[k].Index].defs {
				if hasReg(bUses, r) {
					if stall := f.t.latency(instrs[k].Asm) - (j - k); stall > 0 {
						total += stall
						if producer, consumer := blockOf[instrs[k]], blockOf[instrs[j]]; producer == consumer || loopOf[producer] == loopOf[consumer] {
							byBlock[consumer] += stall
						}
					}
				}
			}
		}
	}
	return total, byBlock
}

// Schedule lifts a body, schedules it, and lowers it back; it reports the
// instructions moved. An error is the lift's; the caller keeps its body.
func Schedule(fn *asm.Function) (*asm.Function, int, error) {
	lifted, err := Lift(cloneFunction(fn))
	if err != nil {
		return nil, 0, err
	}
	moved := lifted.Schedule()
	out := lifted.Asm
	out.Items = lifted.Items()
	return out, moved, nil
}

// StallEstimate lifts a body and estimates its stalls, in total and per
// label: a block without a label (the fall-through after a branch) is
// counted under the last label before it, the region the label opens, so
// a loop's share is what lies between its labels. A body the lift
// refuses estimates zero.
func StallEstimate(fn *asm.Function) (total int, byLabel map[string]int) {
	lifted, err := Lift(cloneFunction(fn))
	if err != nil {
		return 0, nil
	}
	total, byBlock := lifted.Stalls()
	byLabel = map[string]int{}
	current := ""
	for _, b := range lifted.Blocks {
		if b.Label != "" {
			current = b.Label
		}
		if n := byBlock[b]; n > 0 {
			byLabel[current] += n
		}
	}
	return total, byLabel
}
