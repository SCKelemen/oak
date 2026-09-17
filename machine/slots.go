package machine

import (
	"fmt"
	"os"
	"sort"

	"github.com/SCKelemen/oak/asm"
)

// Frame-slot promotion: a value the lowering parked in a frame slot
// ([sp, #N]) and read back with plain loads moves into a register that is
// free over the slot's live range; the store and the loads become copies,
// which reallocation then coalesces. It is the inverse of spilling and
// the first repair of a lowering that ran out of homes.
//
// A slot qualifies only when every access to it is a plain ldr/str of one
// width and one register class, its bytes overlap no other access to the
// frame (a pair, a byte or halfword access, a structure load), its
// address is never taken (no sp arithmetic reaches it), it lies within
// the declared frame, and every read is reached by a store — a slot read
// before any store is the checker's fresh unknown, not a register.

// traceSlots prints one promotion event when OAK_MACHINE_TRACE_SLOTS is
// set (default off): the escapes and blocked ranges the accesses record,
// the slots that qualify, and each slot's register or why it kept none.
func traceSlots(format string, args ...interface{}) {
	if os.Getenv("OAK_MACHINE_TRACE_SLOTS") == "" {
		return
	}
	fmt.Fprintf(os.Stderr, "// slots: "+format+"\n", args...)
}

// SLOT is the pseudo-class of a frame slot in the web machinery: Num is
// the slot's byte offset from sp.
const SLOT Class = 2

// slotAccess is one plain load or store of a frame slot.
type slotAccess struct {
	ins    *Instr
	op     int // the register operand
	offset int64
	bits   int
	class  Class
	store  bool
}

// FrameObject is an aggregate the lowering placed in the frame — an
// array or record local — by its sp-relative byte offset and size. With
// the layout known, an address taken at the object's base blocks only the
// object; without it, everything above the address.
type FrameObject = asm.FrameObject

// Promote rewrites the promotable frame slots of a body into registers
// and removes the stores to qualified slots nothing reads. It returns the
// rewritten function (a new value; the input is not modified), how many
// slots moved, how many dead stores went, or the lift's error.
func Promote(fn *asm.Function) (*asm.Function, int, int, error) { return PromoteWith(fn, nil) }

// PromoteWith is Promote with the lowering's frame layout, when known.
func PromoteWith(fn *asm.Function, objects []FrameObject) (*asm.Function, int, int, error) {
	return promoteWith(fn, objects, true)
}

func promoteWith(fn *asm.Function, objects []FrameObject, splitPairs bool) (*asm.Function, int, int, error) {
	lifted, err := Lift(cloneFunction(fn))
	if err != nil {
		return nil, 0, 0, err
	}
	if fn.Frame <= 0 {
		return lifted.Asm, 0, 0, nil
	}
	var splitWords map[int64]bool
	if splitPairs {
		split, words, splitErr := splitFramePairInitializers(lifted, objects)
		if splitErr != nil {
			return nil, 0, 0, splitErr
		}
		if split != nil {
			lifted, err = Lift(split)
			if err != nil {
				return nil, 0, 0, err
			}
			splitWords = words
		}
	}
	accesses, escaped, blocked := frameAccesses(lifted)
	// An address taken inside a recorded object blocks the object; the
	// rest of the escapes keep the conservative rule.
	var loose []int64
	for _, e := range escaped {
		placed := false
		for _, obj := range objects {
			if obj.Offset < 0 || obj.Size <= 0 || obj.Offset+obj.Size > fn.Frame {
				continue // malformed: not trusted
			}
			if e >= obj.Offset && e < obj.Offset+obj.Size {
				blocked = append(blocked, [2]int64{obj.Offset, obj.Offset + obj.Size})
				placed = true
				break
			}
		}
		if !placed {
			loose = append(loose, e)
		}
	}
	escaped = loose
	slots := qualify(accesses, escaped, blocked, fn.Frame)
	traceSlots("%s: frame %d, %d access(es), escapes %v, blocked %v, %d slot(s) qualify", fn.Name, fn.Frame, len(accesses), escaped, blocked, len(slots))
	if len(slots) == 0 {
		if len(splitWords) != 0 {
			return promoteWith(fn, objects, false)
		}
		return lifted.Asm, 0, 0, nil
	}
	// The slots join the web machinery as pseudo-registers: a store
	// defines, a load uses.
	for _, acc := range accesses {
		s, ok := slots[acc.offset]
		if !ok {
			continue
		}
		a := Access{Op: acc.op, Part: partReg, Reg: Reg{SLOT, int(acc.offset)}, Bits: s.bits}
		if acc.store {
			acc.ins.Defs = append(acc.ins.Defs, a)
		} else {
			acc.ins.Uses = append(acc.ins.Uses, a)
		}
	}
	webs, err := lifted.Webs()
	if err != nil {
		return nil, 0, 0, err
	}
	lifted.liveRanges(webs)
	var calls []int
	for _, ins := range lifted.Instrs {
		if ins.Call {
			calls = append(calls, defPos(ins))
		}
	}
	// Registers the body writes (so its callee-saved ones are saved), and
	// the caller-saved ones it leaves alone.
	written := map[Reg]bool{}
	for _, ins := range lifted.Instrs {
		for _, d := range ins.Defs {
			if !d.Implicit && d.Reg.Class != SLOT {
				written[d.Reg] = true
			}
		}
	}
	var regWebs []*Web
	var slotWebs []*Web
	for _, w := range webs {
		if w.Reg.Class == SLOT {
			slotWebs = append(slotWebs, w)
		} else {
			regWebs = append(regWebs, w)
		}
	}
	sort.SliceStable(slotWebs, func(i, j int) bool { return slotWebs[i].From < slotWebs[j].From })
	taken := map[Reg][]*Web{} // promoted slot webs by their register
	promoted := 0
	splitBenefit := false
	dead := map[*Instr]bool{}
	for _, w := range slotWebs {
		if w.From >= 0 && len(w.Uses) == 0 && !isSaveSlot(lifted, w) {
			// A qualified slot's store no load reaches is dead: the slot's
			// address is never taken and nothing else reads its bytes (the
			// lowering wrote a variable's home the reads never came back
			// to). The stores go; the register they read stays live for
			// its other readers.
			for _, d := range w.Defs {
				if d.Instr != nil {
					dead[d.Instr] = true
				}
			}
			traceSlots("slot [sp, #%d]: %d dead store(s)", w.Reg.Num, len(w.Defs))
			continue
		}
		if w.From < 0 || len(w.Uses) == 0 {
			continue
		}
		uninitialized := false
		for _, d := range w.Defs {
			if d.Instr == nil {
				uninitialized = true
			}
		}
		if uninitialized || isSaveSlot(lifted, w) {
			continue
		}
		s := slots[int64(w.Reg.Num)]
		crossing := false
		for _, c := range calls {
			if w.crosses(c) {
				crossing = true
			}
		}
		r, ok := slotRegister(lifted.t, s, w, crossing, written, regWebs, taken)
		if !ok && crossing && s.class == GPR {
			// No saved callee-saved register is free: save another in the
			// prologue's save area and restore it in the epilogue, when the
			// lowering's shapes allow (growCalleeSaved).
			r, ok = growCalleeSaved(lifted, w, written, regWebs, taken, accesses, escaped, blocked, fn.Frame)
			if ok {
				written[r] = true
			}
		}
		if !ok {
			traceSlots("slot [sp, #%d]: no register (crossing a call: %v)", w.Reg.Num, crossing)
			continue
		}
		traceSlots("slot [sp, #%d] -> %v", w.Reg.Num, r)
		for _, d := range w.Defs {
			d.Instr.Asm = lifted.t.slotCopy(r, regAt(d.Instr.Asm, d.Access), s, true, d.Instr.Asm.Line)
		}
		for _, u := range w.Uses {
			u.Instr.Asm = lifted.t.slotCopy(r, regAt(u.Instr.Asm, u.Access), s, false, u.Instr.Asm.Line)
		}
		taken[r] = append(taken[r], w)
		promoted++
		splitBenefit = splitBenefit || splitWords[int64(w.Reg.Num)]
	}
	if len(splitWords) != 0 && !splitBenefit {
		// Expansion is only preparation for a successful promotion, not
		// an independently selected code-size increase.
		return promoteWith(fn, objects, false)
	}
	if len(dead) > 0 {
		for _, b := range lifted.Blocks {
			kept := b.Instrs[:0]
			for _, ins := range b.Instrs {
				if !dead[ins] {
					kept = append(kept, ins)
				}
			}
			b.Instrs = kept
		}
		lifted.reindex()
	}
	out := lifted.Asm
	out.Items = lifted.Items()
	if promoted > 0 {
		declared := map[Reg]bool{}
		for _, c := range out.Clobbers {
			if r, _, _, ok, err := lifted.t.regOf(c); err == nil && ok {
				declared[r] = true
			}
		}
		for r := range taken {
			if !declared[r] && !lifted.t.calleeSaved(r) {
				out.Clobbers = append(out.Clobbers, lifted.t.clobber(r))
			}
		}
	}
	return out, promoted, len(dead), nil
}

// frameAccesses finds every access to the frame: the plain loads and
// stores by slot, the bases of sp arithmetic (addresses taken), and the
// byte ranges of every other sp-relative access.
func frameAccesses(f *Function) (accesses []slotAccess, escaped []int64, blocked [][2]int64) {
	for _, ins := range f.Instrs {
		a := ins.Asm
		if len(a.Operands) > 0 {
			if dst, ok := a.Operands[0].(asm.Register); ok && dst.Class == asm.ClassSP {
				continue // the frame's own adjustment (sub/add sp, sp, #frame)
			}
		}
		for i, op := range a.Operands {
			switch o := op.(type) {
			case asm.Register:
				if o.Class == asm.ClassSP {
					// sp read as a value: an address taken. `add xN, sp, #k`
					// escapes k and everything above it; `mov xN, sp` and
					// anything else, the whole frame.
					base := int64(0)
					if a.Mnemonic == "add" && i == 1 && len(a.Operands) == 3 {
						if imm, ok := a.Operands[2].(asm.Immediate); ok {
							base = imm.Value
						}
					}
					escaped = append(escaped, base)
					traceSlots("escape at %d by %s", base, a.String())
				}
			case asm.Memory:
				if o.Base.Class != asm.ClassSP {
					continue
				}
				if o.Index != nil || o.Mode != asm.MemOffset {
					escaped = append(escaped, 0)
					continue
				}
				if op, bits, store, plain := f.t.slotAccess(a); plain && i != op {
					if r, _, _, isReg, err := f.t.regOf(a.Operands[op].(asm.Register)); err == nil && isReg && f.t.promotable(r.Class, bits) {
						accesses = append(accesses, slotAccess{ins: ins, op: op, offset: o.Offset, bits: bits, class: r.Class, store: store})
						continue
					}
				}
				// A pair blocks two registers' width; any other frame access
				// disqualifies the whole frame (its width is not known).
				if (a.Mnemonic == "stp" || a.Mnemonic == "ldp") && len(a.Operands) == 3 {
					if reg, ok := a.Operands[0].(asm.Register); ok {
						width := int64(viewBits(reg) / 8)
						blocked = append(blocked, [2]int64{o.Offset, o.Offset + 2*width})
						continue
					}
				}
				if f.t.arch == asm.ArchRV64 {
					// A narrower load or store (lw, sw, lbu, ...): its bytes,
					// at most eight, are not a slot.
					blocked = append(blocked, [2]int64{o.Offset, o.Offset + 8})
					continue
				}
				traceSlots("whole frame escapes by %s", a.String())
				escaped = append(escaped, 0)
			}
		}
	}
	return accesses, escaped, blocked
}

// slot is a qualified frame slot.
type slot struct {
	offset int64
	bits   int
	class  Class
}

// qualify keeps the slots every access agrees on, that overlap nothing
// else, whose address is not taken, within the frame, with at least one
// store — a slot never loaded qualifies so its stores are seen dead.
func qualify(accesses []slotAccess, escaped []int64, blocked [][2]int64, frame int64) map[int64]slot {
	minEscaped := int64(-1)
	for _, e := range escaped {
		if minEscaped < 0 || e < minEscaped {
			minEscaped = e
		}
	}
	byOffset := map[int64][]slotAccess{}
	for _, a := range accesses {
		byOffset[a.offset] = append(byOffset[a.offset], a)
	}
	overlap := func(a0, a1, b0, b1 int64) bool { return a0 < b1 && b0 < a1 }
	out := map[int64]slot{}
	for offset, list := range byOffset {
		first := list[0]
		ok, stores := true, 0
		for _, a := range list {
			if a.bits != first.bits || a.class != first.class {
				ok = false
			}
			if a.store {
				stores++
			}
		}
		size := int64(first.bits / 8)
		if !ok || stores == 0 || offset < 0 || offset+size > frame {
			continue
		}
		if minEscaped >= 0 && offset+size > minEscaped {
			continue
		}
		for _, b := range blocked {
			if overlap(offset, offset+size, b[0], b[1]) {
				ok = false
			}
		}
		for other, olist := range byOffset {
			if other == offset {
				continue
			}
			for _, oa := range olist {
				// Every access at the other offset, at its own width: a word
				// stored inside a chunk read whole is part of the chunk.
				if overlap(offset, offset+size, other, other+int64(oa.bits/8)) {
					ok = false
				}
			}
		}
		if ok {
			out[offset] = slot{offset: offset, bits: first.bits, class: first.class}
		}
	}
	return out
}

// slotRegister chooses a register for a slot's value: of the slot's
// class, not reserved, free of every register web and promoted slot over
// the web's range; across a call, a callee-saved register the body
// already saves (and never v8–v15 for a wide vector).
func slotRegister(t *target, s slot, w *Web, crossing bool, written map[Reg]bool, regWebs []*Web, taken map[Reg][]*Web) (Reg, bool) {
	for _, r := range t.slotCandidates(s.class) {
		if t.reserved(r) {
			continue
		}
		if t.calleeSaved(r) && !written[r] {
			continue // not saved by the prologue
		}
		if crossing && (!t.calleeSaved(r) || (r.Class == VEC && s.bits > 64)) {
			continue
		}
		free := true
		for _, other := range regWebs {
			if other.Reg == r && overlaps(other, w) {
				free = false
				break
			}
		}
		for _, other := range taken[r] {
			if overlaps(other, w) {
				free = false
			}
		}
		if free {
			return r, true
		}
	}
	return Reg{}, false
}

// String spells a slot for the report.
func (s slot) String() string { return fmt.Sprintf("[sp, #%d] (%d bits)", s.offset, s.bits) }

// growCalleeSaved saves one more callee-saved register for a value live
// across a call: the next of x19–x28 the body does not write, at the next
// slot of the prologue's save area — the lowering saves x19, x20, ... at
// consecutive eight-byte slots after the [x29, x30] pair (nativegen's
// saveBase) — with `str xR, [sp, #slot]` after the last save and `ldr xR,
// [sp, #slot]` before the epilogue restores the pair. It refuses when the
// prologue or the single epilogue has another shape, the slot would leave
// the frame or overlap another frame access, or the register is busy
// over the web's range.
func growCalleeSaved(f *Function, w *Web, written map[Reg]bool, regWebs []*Web, taken map[Reg][]*Web, accesses []slotAccess, escaped []int64, blocked [][2]int64, frame int64) (Reg, bool) {
	t, shape := f.t, f.t.frame
	if len(f.Blocks) == 0 || len(f.Blocks[0].Instrs) == 0 {
		return Reg{}, false
	}
	// The prologue: [sp adjustment] [the frame pair's save] then the saves
	// of the callee-saved registers in the lowering's order.
	entry := f.Blocks[0]
	pairAt, lastSave, saveBase, saved := -1, -1, int64(-1), 0
	for i, ins := range entry.Instrs {
		a := ins.Asm
		if off, ok := shape.isPairSave(a); ok {
			pairAt = i
			if saveBase < 0 {
				saveBase = off + shape.pairArea
			}
			continue
		}
		if regs, off, ok := shape.isSave(a); ok && pairAt >= 0 && saved < len(shape.saveOrder) && regs[0] == shape.saveOrder[saved] {
			if lastSave < 0 {
				saveBase = off
			}
			saved += len(regs)
			lastSave = i
			continue
		}
		if i == 0 {
			continue // the sp adjustment
		}
		if pairAt >= 0 {
			break
		}
		return Reg{}, false
	}
	if pairAt < 0 || saved >= len(shape.saveOrder) {
		return Reg{}, false // no calls, another prologue shape, or the area is full
	}
	r := shape.saveOrder[saved]
	if written[r] || t.reserved(r) {
		return Reg{}, false
	}
	slotOff := saveBase + int64(8*saved)
	if slotOff < 0 || slotOff+8 > frame {
		return Reg{}, false
	}
	for _, e := range escaped {
		if slotOff+8 > e {
			return Reg{}, false
		}
	}
	for _, b := range blocked {
		if slotOff < b[1] && b[0] < slotOff+8 {
			return Reg{}, false
		}
	}
	for _, a := range accesses {
		if slotOff < a.offset+int64(a.bits/8) && a.offset < slotOff+8 {
			return Reg{}, false
		}
	}
	for _, other := range regWebs {
		if other.Reg == r && overlaps(other, w) {
			return Reg{}, false
		}
	}
	for _, other := range taken[r] {
		if overlaps(other, w) {
			return Reg{}, false
		}
	}
	// The single epilogue: the block of the one ret, restoring the pair
	// before the sp adjustment.
	var epilogue *Block
	rets := 0
	for _, ins := range f.Instrs {
		if ins.Ret {
			rets++
			epilogue = ins.Block
		}
	}
	if rets != 1 {
		return Reg{}, false
	}
	restoreAt := -1
	for i, ins := range epilogue.Instrs {
		if _, ok := shape.isPairRestore(ins.Asm); ok {
			restoreAt = i
		}
	}
	if restoreAt < 0 {
		return Reg{}, false
	}
	after := lastSave
	if after < 0 {
		after = pairAt
	}
	save := &Instr{Asm: shape.save(r, slotOff, entry.Instrs[after].Asm.Line), Block: entry}
	entry.Instrs = append(entry.Instrs[:after+1], append([]*Instr{save}, entry.Instrs[after+1:]...)...)
	restore := &Instr{Asm: shape.restore(r, slotOff, epilogue.Instrs[restoreAt].Asm.Line), Block: epilogue}
	epilogue.Instrs = append(epilogue.Instrs[:restoreAt], append([]*Instr{restore}, epilogue.Instrs[restoreAt:]...)...)
	return r, true
}

// lastOperandMemory reads a memory operand in the last position.
func lastOperandMemory(a asm.Instruction) (asm.Memory, bool) {
	if len(a.Operands) == 0 {
		return asm.Memory{}, false
	}
	m, ok := a.Operands[len(a.Operands)-1].(asm.Memory)
	return m, ok
}

// isSaveSlot reports a slot the prologue saves a callee-saved register or
// the return address into: its store sits in the entry block and stores a
// callee-saved or reserved register. Moving the save into another
// callee-saved register would only move the obligation.
func isSaveSlot(f *Function, w *Web) bool {
	for _, d := range w.Defs {
		if d.Instr == nil || d.Instr.Block != f.Blocks[0] {
			continue
		}
		reg := regAt(d.Instr.Asm, d.Access)
		if r, _, _, ok, err := f.t.regOf(reg); err == nil && ok && (f.t.calleeSaved(r) || f.t.reserved(r)) {
			return true // a callee-saved register's, or the return address's
		}
	}
	return false
}
