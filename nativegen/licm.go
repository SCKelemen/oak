package nativegen

import (
	"strings"

	"github.com/SCKelemen/oak/asm"
)

// Loop-invariant code motion (docs/spec/94-assembler.md §9 "Loop
// invariants"): a pass over the emitted items of one function, judged like
// every lowering by the seam checker and the verifier. A loop is the
// generator's shape — the `loop_N` header label, its exit tests branching
// to `done_M`, the body, the unconditional back edge — and, innermost
// first, three things leave the body for a preheader placed before the
// header:
//
//   - a pure instruction (a constant, a global's address, an element
//     address, arithmetic) whose sources are never written in the loop; its
//     destination is renamed to a register the whole function never names,
//     and the reads it fed in its basic block follow the new name;
//   - a copy `mov wD, wS` of an invariant register is not moved but
//     propagated: its reads take wS and the copy disappears (a copy of
//     the zero register likewise, so `mov x10, xzr; str x10, […]` stores
//     `xzr`);
//   - the first trapping instruction of the body, when it is an element
//     guard `cmp wA, wB; b.cond trap` over invariant registers and nothing
//     before it in the body stores, calls, or traps, is peeled into the
//     preheader behind a copy of the loop's exit tests — the preheader
//     then runs exactly when the body would have run at least once, so
//     the trap fires on the same inputs as before, once instead of every
//     iteration — and the fact it establishes (`wA < wB`) holds at the
//     header on both edges, so the element address the guard licensed
//     hoists with it (the checker keeps constants, global addresses,
//     element regions, and index guards across labels, §7).
//
// What stays: loads (memory the loop stores through may alias), stores,
// calls, and anything reading a register the loop writes. A rename needs
// the old destination's next write inside the same basic block, or no read
// of it anywhere after the block in the loop, so no path can reach a read
// through the old name.

// pureInvariantMnemonics are the instructions the pass may move: they read
// registers and immediates and write one register, without flags, memory,
// or a trap.
var pureInvariantMnemonics = map[string]bool{
	"mov": true, "movz": true, "movk": true, "adrp": true, "adrl": true,
	"add": true, "sub": true, "lsl": true, "lsr": true, "asr": true,
	"and": true, "orr": true, "eor": true, "mul": true, "madd": true, "msub": true, "umaddl": true, "umull": true, "smull": true,
	"uxtb": true, "uxth": true, "sxtb": true, "sxth": true, "sxtw": true,
}

// loadMnemonics: what may precede a peeled guard besides pure instructions
// (a load neither traps in checked code nor stores).
func isPlainLoadMnemonic(m string) bool {
	switch m {
	case "ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "ldrsw", "ldp", "ldur":
		return true
	}
	return false
}

func isBranchMnemonic(m string) bool {
	switch m {
	case "b", "b.", "bl", "blr", "br", "ret", "cbz", "cbnz", "tbz", "tbnz", "brk", "eret", "svc":
		return true
	}
	return false
}

// invariantLoop is one loop's extent in the items.
type invariantLoop struct {
	header, back int // the header label's index and the back edge's
	name         string
}

// findGeneratorLoops lists the loops by their header labels and last back
// edges, innermost (shortest) first.
func findGeneratorLoops(items []asm.Item) []invariantLoop {
	headers := map[string]int{}
	for i, item := range items {
		if l, isLabel := item.(asm.Label); isLabel && strings.HasPrefix(l.Name, "loop_") {
			headers[l.Name] = i
		}
	}
	backs := map[string]int{}
	for i, item := range items {
		ins, isIns := item.(asm.Instruction)
		if !isIns || ins.Mnemonic != "b" || len(ins.Operands) != 1 {
			continue
		}
		if sym, isSym := ins.Operands[0].(asm.Symbol); isSym {
			if h, isHeader := headers[sym.Name]; isHeader && i > h {
				backs[sym.Name] = i
			}
		}
	}
	var loops []invariantLoop
	for name, h := range headers {
		if b, ok := backs[name]; ok {
			loops = append(loops, invariantLoop{header: h, back: b, name: name})
		}
	}
	// Innermost first: a shorter range inside a longer one is processed
	// before the enclosing loop sees its hoisted code.
	for i := 1; i < len(loops); i++ {
		for j := i; j > 0 && loops[j].back-loops[j].header < loops[j-1].back-loops[j-1].header; j-- {
			loops[j], loops[j-1] = loops[j-1], loops[j]
		}
	}
	return loops
}

// hoistInvariants runs the pass over a function's body items. mentioned is
// the set of general registers the function names (a rename never takes
// one); trap names the trap block's label. It returns the items, the
// registers the renames took, and how many instructions moved or
// disappeared (the compiler's fallback lowers the body again without the
// pass when the checker refuses the hoisted form).
func hoistInvariants(items []asm.Item, mentioned map[int]bool, loopHomes map[string]map[int]bool, reserve []int, globals map[string]asm.Global, trap string) ([]asm.Item, []int, int, int) {
	var taken []int
	changed, wanted := 0, 0
	pool := &registerPool{reserve: reserve, mentioned: mentioned}
	done := map[string]bool{}
	for {
		var next *invariantLoop
		for _, loop := range findGeneratorLoops(items) {
			if !done[loop.name] {
				l := loop
				next = &l
				break
			}
		}
		if next == nil {
			return items, taken, changed, wanted
		}
		done[next.name] = true
		before := len(items)
		out, used, missed := hoistLoop(items, *next, pool, loopHomes[next.name], globals, trap)
		if len(out) != before || used != nil {
			changed++
		}
		wanted += missed
		items = out
		taken = append(taken, used...)
	}
}

// registerPool hands out the registers a hoisted value may take: the
// callee-saved registers reserved for the pass first (they survive calls),
// then the scratch registers the function never names (not across a call).
type registerPool struct {
	reserve   []int
	mentioned map[int]bool
}

func (p *registerPool) take(acrossCall bool) (asm.Register, bool) {
	if len(p.reserve) > 0 {
		r := p.reserve[0]
		p.reserve = p.reserve[1:]
		return xr(r), true
	}
	if acrossCall {
		return asm.Register{}, false
	}
	for _, r := range []int{15, 14, 13, 12, 11, 10, 9, 16, 17} {
		if !p.mentioned[r] {
			p.mentioned[r] = true
			return xr(r), true
		}
	}
	return asm.Register{}, false
}

// hoistLoop processes one loop. homes are the registers of the variables
// in scope at the loop's header: a write into one is the variable's value,
// read where no block analysis sees (after the loop, at the header, in
// another arm), so it is neither moved nor propagated away.
func hoistLoop(items []asm.Item, loop invariantLoop, pool *registerPool, homes map[int]bool, globals map[string]asm.Global, trap string) ([]asm.Item, []int, int) {
	h, b := loop.header, loop.back
	// Registers the loop writes; a call writes every caller-saved register.
	written := map[int]bool{}
	hasCall := false
	for i := h; i <= b; i++ {
		ins, isIns := items[i].(asm.Instruction)
		if !isIns {
			continue
		}
		for _, r := range writtenGeneral(ins) {
			written[r] = true
		}
		if ins.Mnemonic == "bl" || ins.Mnemonic == "blr" {
			// A call clobbers every caller-saved register: nothing hoisted
			// into a scratch register survives the body, so only copies
			// propagate and guards peel in a loop that calls.
			hasCall = true
			for r := 0; r <= 18; r++ {
				written[r] = true
			}
		}
	}
	invariant := func(reg asm.Register) bool {
		return reg.ZeroRegister() || reg.Class == asm.ClassSP || !written[reg.Num]
	}
	// A scalar global's value is invariant when the loop neither stores
	// to a global's address nor calls: a span cannot alias a scalar
	// global (its elements lie in arrays and aggregates), so the loop's
	// span stores leave it alone (docs/spec/94-assembler.md §9). The
	// global-address registers the loop forms, and whether any store
	// goes through one.
	globalAddr := map[int]string{}
	storesGlobal := false
	for i := h; i <= b; i++ {
		ins, isIns := items[i].(asm.Instruction)
		if !isIns {
			continue
		}
		if ins.Mnemonic == "add" && len(ins.Operands) == 3 {
			if sym, isSym := ins.Operands[2].(asm.Symbol); isSym && sym.Lo12 {
				if d, isReg := ins.Operands[0].(asm.Register); isReg {
					globalAddr[d.Num] = sym.Name
				}
			}
		}
	}
	for i := h; i <= b; i++ {
		ins, isIns := items[i].(asm.Instruction)
		if !isIns || !strings.HasPrefix(ins.Mnemonic, "st") || len(ins.Operands) == 0 {
			continue
		}
		if mem, isMem := ins.Operands[len(ins.Operands)-1].(asm.Memory); isMem {
			if _, isGlobal := globalAddr[mem.Base.Num]; isGlobal {
				storesGlobal = true
			}
		}
	}
	// scalarGlobalLoad reports a load of a scalar global through an
	// address the loop formed, hoistable when nothing writes globals.
	scalarGlobalLoad := func(ins asm.Instruction) bool {
		if hasCall || storesGlobal || !isPlainLoadMnemonic(ins.Mnemonic) || ins.Mnemonic == "ldp" || len(ins.Operands) != 2 {
			return false
		}
		mem, isMem := ins.Operands[1].(asm.Memory)
		if !isMem || mem.Index != nil || mem.Mode != asm.MemOffset || mem.Offset != 0 {
			return false
		}
		sym, isGlobal := globalAddr[mem.Base.Num]
		if !isGlobal {
			return false
		}
		global, known := globals[sym]
		return known && !global.Aggregate
	}
	// The exit tests: the header's run of compares and branches leaving
	// the loop; the body begins after the last exit branch.
	bodyStart := h + 1
	exitPure := true
	for i := h + 1; i <= b; i++ {
		ins, isIns := items[i].(asm.Instruction)
		if !isIns {
			break
		}
		if ins.Mnemonic == "cmp" || ins.Mnemonic == "cmn" || ins.Mnemonic == "tst" || pureInvariantMnemonics[ins.Mnemonic] {
			continue
		}
		if ins.Mnemonic == "b." || ins.Mnemonic == "cbz" || ins.Mnemonic == "cbnz" || ins.Mnemonic == "tbz" || ins.Mnemonic == "tbnz" {
			target := branchTarget(ins)
			if target == trap {
				break // a guard: the body has begun
			}
			bodyStart = i + 1
			continue
		}
		if isPlainLoadMnemonic(ins.Mnemonic) {
			continue // a load: the header's when an exit branch follows (judged below), else the body's
		}
		break
	}
	for i := h + 1; i < bodyStart; i++ {
		if ins, isIns := items[i].(asm.Instruction); isIns && !(ins.Mnemonic == "cmp" || ins.Mnemonic == "cmn" || ins.Mnemonic == "tst" || pureInvariantMnemonics[ins.Mnemonic] || ins.Mnemonic == "b." || ins.Mnemonic == "cbz" || ins.Mnemonic == "cbnz" || ins.Mnemonic == "tbz" || ins.Mnemonic == "tbnz") {
			exitPure = false
		}
	}
	body := make([]asm.Item, b-bodyStart)
	copy(body, items[bodyStart:b])
	var preheader []asm.Item
	type movedItem struct {
		at   int
		item asm.Item
	}
	var moved []movedItem
	var used []int
	removed := map[int]bool{}
	// Basic blocks of the body: [start, end) ranges split at labels and
	// after branches.
	// A branch to the trap block delivers no result, so the fall-through
	// is the block's only continuation and the block runs on.
	endsBlock := func(ins asm.Instruction) bool {
		return isBranchMnemonic(ins.Mnemonic) && branchTarget(ins) != trap
	}
	blockEnd := func(i int) int {
		for j := i + 1; j < len(body); j++ {
			if _, isLabel := body[j].(asm.Label); isLabel {
				return j
			}
			if ins, isIns := body[j-1].(asm.Instruction); isIns && endsBlock(ins) {
				return j
			}
		}
		return len(body)
	}
	// readOutside reports a read of reg anywhere in the loop — the exit
	// tests included — outside the body range [from, to): a value whose
	// definition leaves the loop must have no reader the block does not
	// hold, on any path, including the next iteration's header.
	readOutside := func(from, to, reg int) bool {
		for i := h + 1; i < bodyStart; i++ {
			if ins, isIns := items[i].(asm.Instruction); isIns && readsGeneral(ins, reg) {
				return true
			}
		}
		for j := 0; j < len(body); j++ {
			if j >= from && j < to {
				continue
			}
			ins, isIns := body[j].(asm.Instruction)
			if !isIns || removed[j] {
				continue
			}
			if readsGeneral(ins, reg) {
				// A read the same block writes first (`ldrh w10; lsl w10,
				// w10, #11` before the zero copy into w10) reads that
				// write, not the value that left.
				if j < from && writtenEarlierInBlock(body, removed, j, reg) {
					continue
				}
				return true
			}
		}
		return false
	}
	// renameUses renames the reads of old (of class cls) to new from index
	// from to the next write of old in the same block; reports whether the
	// renaming is complete (the def's every reader is in the block).
	renameUses := func(from, old int, cls asm.RegClass, new asm.Register, requireClass bool) bool {
		end := blockEnd(from - 1)
		for j := from; j < end; j++ {
			ins, isIns := body[j].(asm.Instruction)
			if !isIns || removed[j] {
				continue
			}
			if readsGeneral(ins, old) {
				if requireClass && !readsOnlyAsClass(ins, old, cls) {
					return false
				}
			}
			if writesGeneral(ins, old) {
				// The reads in this instruction (before its write) rename too.
				body[j] = renameReads(ins, old, new)
				return true
			}
			body[j] = renameReads(ins, old, new)
		}
		// The block ended without a write: no reader outside the block.
		return !readOutside(from, end, old)
	}
	// A dry run first: whether every read up to the next write is of the
	// matching class (for a copy) — renameUses mutates, so check before.
	canRename := func(from, old int, cls asm.RegClass, requireClass bool) bool {
		end := blockEnd(from - 1)
		for j := from; j < end; j++ {
			ins, isIns := body[j].(asm.Instruction)
			if !isIns || removed[j] {
				continue
			}
			if readsGeneral(ins, old) && requireClass && !readsOnlyAsClass(ins, old, cls) {
				return false
			}
			if ins.Mnemonic == "movk" && writesGeneral(ins, old) {
				// A movk extends the register it reads: the old value is
				// still being built here, so it cannot be renamed away
				// (a constant's chain hoists whole or not at all).
				return false
			}
			if writesGeneral(ins, old) {
				return true
			}
		}
		return !readOutside(from, end, old)
	}
	missed := 0
	free := func() (asm.Register, bool) {
		r, ok := pool.take(hasCall)
		if ok {
			used = append(used, r.Num)
		}
		return r, ok
	}
	for i := 0; i < len(body); i++ {
		ins, isIns := body[i].(asm.Instruction)
		if !isIns || removed[i] {
			continue
		}
		if (!pureInvariantMnemonics[ins.Mnemonic] && !scalarGlobalLoad(ins)) || len(ins.Operands) < 2 {
			continue
		}
		dest, isReg := ins.Operands[0].(asm.Register)
		if !isReg || (dest.Class != asm.ClassX && dest.Class != asm.ClassW) || homes[dest.Num] {
			continue
		}
		// A write into an ABI register (an argument, the result, the
		// indirect-result address, the platform and frame registers)
		// belongs to a call or a return: it stays where it is.
		if dest.Num <= 8 || dest.Num == 18 || dest.Num >= 29 {
			continue
		}
		// movk reads its destination: only as the second half of a
		// constant pair whose movz was hoisted (handled with the movz).
		if ins.Mnemonic == "movk" {
			continue
		}
		sources := sourceRegisters(ins)
		allInvariant := true
		for _, s := range sources {
			if !invariant(s) {
				allInvariant = false
			}
		}
		// A copy (`mov wD, wS`, or `add xD, xS, #0`, a field at offset
		// zero) is not moved but propagated: its readers take the source,
		// when the source holds still until the last of them — an
		// invariant register, the zero register, or one the block does
		// not write before then.
		isCopy := ins.Mnemonic == "mov" && len(ins.Operands) == 2
		if ins.Mnemonic == "add" && len(ins.Operands) == 3 {
			if k, isImm := ins.Operands[2].(asm.Immediate); isImm && k.Value == 0 && k.Shift == 0 {
				isCopy = true
			}
		}
		if isCopy {
			if src, ok := ins.Operands[1].(asm.Register); ok && src.ZeroRegister() {
				// The zero register reaches a store's data operand alone:
				// a compare or an index through it carries no fact the
				// checker can key (the constant index of `cursor[0]`).
				if zeroStoreOnly(body, removed, i+1, blockEnd(i), dest.Num) || (zeroStoreReaders(body, removed, i+1, blockEnd(i), dest.Num) && !readOutside(i+1, blockEnd(i), dest.Num)) {
					renameUses(i+1, dest.Num, dest.Class, asm.Register{Text: "xzr", Class: asm.ClassX, Num: 31, Lane: -1}, true)
					removed[i] = true
				}
				continue
			}
			if src, ok := ins.Operands[1].(asm.Register); ok && src.Class == dest.Class {
				if canRename(i+1, dest.Num, dest.Class, true) && (invariant(src) || sourceHolds(body, removed, i+1, blockEnd(i), dest.Num, src.Num)) {
					renameUses(i+1, dest.Num, dest.Class, src, true)
					removed[i] = true
				}
				continue
			}
		}
		if !allInvariant {
			continue
		}
		// A movz followed by movk into the same register: the whole
		// chain moves (a 64-bit constant is up to four instructions; the
		// first two alone would leave the later movk extending a register
		// the loop now writes for something else).
		var chain []int
		if ins.Mnemonic == "movz" {
			for j := i + 1; j < len(body); j++ {
				k, isIns := body[j].(asm.Instruction)
				if !isIns || k.Mnemonic != "movk" {
					break
				}
				kd, ok := k.Operands[0].(asm.Register)
				if !ok || kd.Num != dest.Num || kd.Class != dest.Class {
					break
				}
				chain = append(chain, j)
			}
		}
		from := i + 1
		if len(chain) > 0 {
			from = chain[len(chain)-1] + 1
		}
		if !canRename(from, dest.Num, dest.Class, false) {
			continue
		}
		r, ok := free()
		if !ok {
			missed++
			continue
		}
		renamed := asm.Register{Text: dest.Text[:1] + itoa(r.Num), Class: dest.Class, Num: r.Num}
		if dest.Class == asm.ClassX {
			renamed.Text = "x" + itoa(r.Num)
		} else {
			renamed.Text = "w" + itoa(r.Num)
		}
		hoisted := ins
		hoisted.Operands = append([]asm.Operand(nil), ins.Operands...)
		hoisted.Operands[0] = renamed
		if sym, isGlobal := globalAddr[dest.Num]; isGlobal {
			globalAddr[renamed.Num] = sym // the global's address under its new name
		}
		preheader = append(preheader, hoisted)
		moved = append(moved, movedItem{at: i, item: hoisted})
		removed[i] = true
		for _, at := range chain {
			k := body[at].(asm.Instruction)
			k.Operands = append([]asm.Operand(nil), k.Operands...)
			k.Operands[0] = renamed
			preheader = append(preheader, k)
			moved = append(moved, movedItem{at: at, item: k})
			removed[at] = true
		}
		renameUses(from, dest.Num, dest.Class, renamed, false)
	}
	// Guard peeling: the first trapping or effectful instruction.
	var peeled []asm.Item
	peeledAt := -1
	if exitPure && bodyStart > h+1 {
		for i := 0; i < len(body); i++ {
			ins, isIns := body[i].(asm.Instruction)
			if !isIns || removed[i] {
				continue
			}
			if pureInvariantMnemonics[ins.Mnemonic] || isPlainLoadMnemonic(ins.Mnemonic) {
				continue
			}
			if ins.Mnemonic == "cmp" && i+1 < len(body) {
				if br, isBr := body[i+1].(asm.Instruction); isBr && br.Mnemonic == "b." && branchTarget(br) == trap {
					left, okL := ins.Operands[0].(asm.Register)
					rightInv := true
					if right, isReg := ins.Operands[1].(asm.Register); isReg {
						rightInv = invariant(right)
					}
					if okL && invariant(left) && rightInv {
						peeled = append(peeled, ins, br)
						peeledAt = i
						removed[i], removed[i+1] = true, true
					}
				}
			}
			break
		}
	}
	if len(preheader) == 0 && len(peeled) == 0 && len(removed) == 0 {
		return items, nil, missed
	}
	var out []asm.Item
	out = append(out, items[:h]...)
	if len(peeled) > 0 {
		// The exit tests' copy: the preheader runs only when the body would.
		for i := h + 1; i < bodyStart; i++ {
			out = append(out, items[i])
		}
	}
	// The moved instructions in their body order — the peeled guard before
	// the address arithmetic it licenses, as the checker reads them.
	if peeledAt < 0 {
		out = append(out, preheader...)
	} else {
		placed := false
		for _, m := range moved {
			if !placed && m.at > peeledAt {
				out = append(out, peeled...)
				placed = true
			}
			out = append(out, m.item)
		}
		if !placed {
			out = append(out, peeled...)
		}
	}
	out = append(out, items[h:bodyStart]...)
	for i, item := range body {
		if !removed[i] {
			out = append(out, item)
		}
	}
	out = append(out, items[b:]...)
	return out, used, missed
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	s := ""
	for n > 0 {
		s = string(rune('0'+n%10)) + s
		n /= 10
	}
	return s
}

func branchTarget(ins asm.Instruction) string {
	if len(ins.Operands) == 0 {
		return ""
	}
	if sym, isSym := ins.Operands[len(ins.Operands)-1].(asm.Symbol); isSym {
		return sym.Name
	}
	return ""
}

// sourceRegisters lists an instruction's general source registers: every
// register operand but the destination, memory bases and indices, and
// extended-register operands.
func sourceRegisters(ins asm.Instruction) []asm.Register {
	var regs []asm.Register
	for i, operand := range ins.Operands {
		if i == 0 {
			continue
		}
		switch o := operand.(type) {
		case asm.Register:
			if o.Class == asm.ClassX || o.Class == asm.ClassW {
				regs = append(regs, o)
			}
		case asm.Memory:
			regs = append(regs, o.Base)
			if o.Index != nil {
				regs = append(regs, *o.Index)
			}
		case asm.Extended:
			regs = append(regs, o.Reg)
		case asm.Shifted:
			regs = append(regs, o.Reg)
		}
	}
	return regs
}

// writtenGeneral lists the general registers an instruction writes.
func writtenGeneral(ins asm.Instruction) []int {
	if len(ins.Operands) == 0 || isBranchMnemonic(ins.Mnemonic) {
		return nil
	}
	switch ins.Mnemonic {
	case "cmp", "cmn", "tst", "ccmp", "prfm":
		return nil
	}
	if strings.HasPrefix(ins.Mnemonic, "st") {
		// A store writes no register, except a post/pre-indexed base.
		if mem, isMem := ins.Operands[len(ins.Operands)-1].(asm.Memory); isMem && mem.Mode != asm.MemOffset {
			return []int{mem.Base.Num}
		}
		return nil
	}
	n := 1
	if ins.Mnemonic == "ldp" || ins.Mnemonic == "ldpsw" {
		n = 2
	}
	var regs []int
	for i := 0; i < n && i < len(ins.Operands); i++ {
		if r, isReg := ins.Operands[i].(asm.Register); isReg && (r.Class == asm.ClassX || r.Class == asm.ClassW) && !r.ZeroRegister() {
			regs = append(regs, r.Num)
		}
	}
	if mem, isMem := ins.Operands[len(ins.Operands)-1].(asm.Memory); isMem && mem.Mode != asm.MemOffset {
		regs = append(regs, mem.Base.Num)
	}
	return regs
}

func writesGeneral(ins asm.Instruction, reg int) bool {
	for _, r := range writtenGeneral(ins) {
		if r == reg {
			return true
		}
	}
	return false
}

// readsGeneral reports whether the instruction reads reg: a source
// register, a memory base or index, a store's data register, a compare's
// operands, or a destination the instruction also reads (movk, madd's
// addend is a source anyway).
func readsGeneral(ins asm.Instruction, reg int) bool {
	// A call reads its argument registers and the indirect-result
	// register; a return reads the result registers. Neither names them
	// as operands (the pass once dropped `mov x1, x24` before a `bl`).
	switch ins.Mnemonic {
	case "bl", "blr":
		if reg <= 8 {
			return true
		}
	case "ret":
		if reg <= 1 || reg == 8 {
			return true
		}
	}
	for _, r := range sourceRegisters(ins) {
		if r.Num == reg {
			return true
		}
	}
	if len(ins.Operands) == 0 {
		return false
	}
	first, isReg := ins.Operands[0].(asm.Register)
	if !isReg || first.Num != reg {
		return false
	}
	// The first operand is read by stores, compares, branches, and movk.
	if strings.HasPrefix(ins.Mnemonic, "st") || isBranchMnemonic(ins.Mnemonic) || ins.Mnemonic == "movk" {
		return true
	}
	switch ins.Mnemonic {
	case "cmp", "cmn", "tst", "ccmp", "cbz", "cbnz", "tbz", "tbnz":
		return true
	}
	return false
}

// readsOnlyAsClass reports whether every read of reg in the instruction is
// at class cls (a W copy's readers must read the W view).
func readsOnlyAsClass(ins asm.Instruction, reg int, cls asm.RegClass) bool {
	check := func(r asm.Register) bool { return r.Num != reg || r.Class == cls }
	for _, r := range sourceRegisters(ins) {
		if !check(r) {
			return false
		}
	}
	if first, isReg := ins.Operands[0].(asm.Register); isReg && first.Num == reg && readsGeneral(ins, reg) && first.Class != cls {
		return false
	}
	return true
}

// renameReads replaces reads of old by new (keeping each read's class) in
// every source position; the destination keeps its name unless the
// instruction reads it (a store's data, a compare's left operand).
func renameReads(ins asm.Instruction, old int, new asm.Register) asm.Instruction {
	out := ins
	out.Operands = append([]asm.Operand(nil), ins.Operands...)
	view := func(r asm.Register) asm.Register {
		renamed := new
		renamed.Class = r.Class
		if new.ZeroRegister() {
			if r.Class == asm.ClassW {
				renamed.Text = "wzr"
			} else {
				renamed.Text = "xzr"
			}
			return renamed
		}
		if r.Class == asm.ClassW {
			renamed.Text = "w" + itoa(new.Num)
		} else {
			renamed.Text = "x" + itoa(new.Num)
		}
		return renamed
	}
	for i, operand := range out.Operands {
		if i == 0 {
			// The first operand: renamed only where it is a read.
			if r, isReg := operand.(asm.Register); isReg && r.Num == old && readsGeneral(ins, old) && !writesGeneral(ins, old) {
				out.Operands[i] = view(r)
			}
			continue
		}
		switch o := operand.(type) {
		case asm.Register:
			if o.Num == old && (o.Class == asm.ClassX || o.Class == asm.ClassW) {
				out.Operands[i] = view(o)
			}
		case asm.Memory:
			if o.Base.Num == old {
				o.Base = view(o.Base)
			}
			if o.Index != nil && o.Index.Num == old {
				idx := view(*o.Index)
				o.Index = &idx
			}
			out.Operands[i] = o
		case asm.Extended:
			if o.Reg.Num == old {
				o.Reg = view(o.Reg)
			}
			out.Operands[i] = o
		case asm.Shifted:
			if o.Reg.Num == old {
				o.Reg = view(o.Reg)
			}
			out.Operands[i] = o
		}
	}
	return out
}

// registersNamed collects every general register number the items name.
func registersNamed(items []asm.Item) map[int]bool {
	out := map[int]bool{}
	for _, item := range items {
		ins, isIns := item.(asm.Instruction)
		if !isIns {
			continue
		}
		for _, r := range sourceRegisters(ins) {
			out[r.Num] = true
		}
		if len(ins.Operands) > 0 {
			if r, isReg := ins.Operands[0].(asm.Register); isReg && (r.Class == asm.ClassX || r.Class == asm.ClassW) {
				out[r.Num] = true
			}
		}
	}
	return out
}

// sourceHolds reports whether register src is written by no instruction
// in [from, end) of the body that still reads dest — the range a copy's
// readers occupy — so the readers may take src instead.
func sourceHolds(body []asm.Item, removed map[int]bool, from, end, dest, src int) bool {
	last := from - 1
	for j := from; j < end; j++ {
		ins, isIns := body[j].(asm.Instruction)
		if !isIns || removed[j] {
			continue
		}
		if readsGeneral(ins, dest) {
			last = j
		}
		if writesGeneral(ins, dest) {
			break
		}
	}
	for j := from; j <= last; j++ {
		ins, isIns := body[j].(asm.Instruction)
		if !isIns || removed[j] {
			continue
		}
		if writesGeneral(ins, src) {
			return false
		}
	}
	return true
}

// zeroStoreOnly reports whether every reader of dest in [from, end) before
// its next write is a store's data operand, and dest is written again in
// the block — the readers a copy of zero may take `xzr` for.
func zeroStoreOnly(body []asm.Item, removed map[int]bool, from, end, dest int) bool {
	readers := 0
	for j := from; j < end; j++ {
		ins, isIns := body[j].(asm.Instruction)
		if !isIns || removed[j] {
			continue
		}
		if readsGeneral(ins, dest) {
			if !strings.HasPrefix(ins.Mnemonic, "st") || len(ins.Operands) < 2 {
				return false
			}
			data, isReg := ins.Operands[0].(asm.Register)
			if !isReg || data.Num != dest {
				return false
			}
			if mem, isMem := ins.Operands[len(ins.Operands)-1].(asm.Memory); isMem && (mem.Base.Num == dest || (mem.Index != nil && mem.Index.Num == dest)) {
				return false
			}
			readers++
		}
		if writesGeneral(ins, dest) {
			return readers > 0
		}
	}
	return false
}

// zeroStoreReaders reports whether every reader of dest in [from, end) is
// a store's data operand and the block ends without writing dest again
// (the readers then take `xzr` when nothing outside the block reads it).
func zeroStoreReaders(body []asm.Item, removed map[int]bool, from, end, dest int) bool {
	readers := 0
	for j := from; j < end; j++ {
		ins, isIns := body[j].(asm.Instruction)
		if !isIns || removed[j] {
			continue
		}
		if readsGeneral(ins, dest) {
			if !strings.HasPrefix(ins.Mnemonic, "st") || len(ins.Operands) < 2 {
				return false
			}
			data, isReg := ins.Operands[0].(asm.Register)
			if !isReg || data.Num != dest {
				return false
			}
			if mem, isMem := ins.Operands[len(ins.Operands)-1].(asm.Memory); isMem && (mem.Base.Num == dest || (mem.Index != nil && mem.Index.Num == dest)) {
				return false
			}
			readers++
		}
		if writesGeneral(ins, dest) {
			return false
		}
	}
	return readers > 0
}

// writtenEarlierInBlock reports a write of reg between the start of the
// basic block holding index at and at itself (no label between).
func writtenEarlierInBlock(body []asm.Item, removed map[int]bool, at, reg int) bool {
	for k := at - 1; k >= 0; k-- {
		if _, isLabel := body[k].(asm.Label); isLabel {
			return false
		}
		ins, isIns := body[k].(asm.Instruction)
		if !isIns || removed[k] {
			continue
		}
		if isBranchMnemonic(ins.Mnemonic) && ins.Mnemonic != "b." && ins.Mnemonic != "cbz" && ins.Mnemonic != "cbnz" && ins.Mnemonic != "tbz" && ins.Mnemonic != "tbnz" {
			return false // an unconditional transfer: another block
		}
		if writesGeneral(ins, reg) {
			return true
		}
	}
	return false
}
