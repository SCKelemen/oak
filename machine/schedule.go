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
// path, ties in original order.
func (f *Function) scheduleRegion(region []*Instr) []*Instr {
	n := len(region)
	if n < 2 {
		return region
	}
	preds := make([][]int, n)
	weights := make([][]int, n)
	succs := make([][]int, n)
	for j := 1; j < n; j++ {
		for i := j - 1; i >= 0; i-- {
			if w, dep := f.dependence(region[i], region[j]); dep {
				preds[j] = append(preds[j], i)
				weights[j] = append(weights[j], w)
				succs[i] = append(succs[i], j)
			}
		}
	}
	// Priority: the longest latency path from the instruction to the
	// region's end.
	priority := make([]int, n)
	for i := n - 1; i >= 0; i-- {
		lat := f.t.latency(region[i].Asm)
		priority[i] = lat
		for _, s := range succs[i] {
			if p := lat + priority[s]; p > priority[i] {
				priority[i] = p
			}
		}
	}
	scheduled := make([]bool, n)
	cycleOf := make([]int, n)
	var out []*Instr
	cycle := 0
	for len(out) < n {
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
			// Prefer an instruction ready now with the longest path; among
			// those not yet ready, the one ready first; ties keep order.
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
		out = append(out, region[best])
		cycle++
	}
	return out
}

// dependence reports whether b must stay after a, and the cycles b must
// wait after a issues.
func (f *Function) dependence(a, b *Instr) (int, bool) {
	weight, dep := 0, false
	aDefs, aUses := f.regsOf(a)
	bDefs, bUses := f.regsOf(b)
	for r := range aDefs {
		if bUses[r] { // read after write
			dep = true
			if lat := f.t.latency(a.Asm); lat > weight {
				weight = lat
			}
		}
		if bDefs[r] { // write after write
			dep = true
		}
	}
	for r := range aUses {
		if bDefs[r] { // write after read
			dep = true
		}
	}
	// Memory: a store orders against every memory instruction.
	aMem, aStore := memoryOf(a.Asm)
	bMem, bStore := memoryOf(b.Asm)
	if aMem && bMem && (aStore || bStore) {
		dep = true
	}
	return weight, dep
}

// regsOf collects the registers an instruction writes and reads,
// including the flags pseudo-register. sp and the zero register are not
// lifted as registers: an sp write is a barrier, an sp read (a frame
// access) needs no edge.
func (f *Function) regsOf(ins *Instr) (defs, uses map[Reg]bool) {
	defs, uses = map[Reg]bool{}, map[Reg]bool{}
	for _, d := range ins.Defs {
		defs[d.Reg] = true
	}
	for _, u := range ins.Uses {
		uses[u.Reg] = true
	}
	if f.t.writesFlags(ins.Asm) {
		defs[flagsReg] = true
	}
	if f.t.readsFlags(ins.Asm) || (ins.Branch && f.t.conditional(ins.Asm)) {
		uses[flagsReg] = true
	}
	return defs, uses
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
// waits for producers within each barrier-free region: the sum over
// read-after-write pairs, at most eight instructions apart, of the
// latency the distance does not cover. It reports the total and the
// share per block.
func (f *Function) Stalls() (total int, byBlock map[*Block]int) {
	byBlock = map[*Block]int{}
	for _, b := range f.Blocks {
		start := 0
		n := len(b.Instrs)
		for i := 0; i <= n; i++ {
			if i < n && !f.t.barrier(b.Instrs[i]) && !f.t.writesFlags(b.Instrs[i].Asm) {
				continue
			}
			region := b.Instrs[start:i]
			for j := 1; j < len(region); j++ {
				_, bUses := f.regsOf(region[j])
				for k := j - 1; k >= 0 && j-k <= 8; k-- {
					aDefs, _ := f.regsOf(region[k])
					for r := range aDefs {
						if bUses[r] {
							if stall := f.t.latency(region[k].Asm) - (j - k); stall > 0 {
								total += stall
								byBlock[b] += stall
							}
						}
					}
				}
			}
			start = i + 1
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
// block label; a body the lift refuses estimates zero.
func StallEstimate(fn *asm.Function) (total int, byLabel map[string]int) {
	lifted, err := Lift(cloneFunction(fn))
	if err != nil {
		return 0, nil
	}
	total, byBlock := lifted.Stalls()
	byLabel = map[string]int{}
	for b, n := range byBlock {
		byLabel[b.Label] += n
	}
	return total, byLabel
}
