package machine

import (
	"fmt"
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

// Promote rewrites the promotable frame slots of an AArch64 body into
// registers. It returns the rewritten function (a new value; the input is
// not modified) and how many slots moved, or the lift's error.
func Promote(fn *asm.Function) (*asm.Function, int, error) {
	lifted, err := Lift(cloneFunction(fn))
	if err != nil {
		return nil, 0, err
	}
	if fn.Frame <= 0 {
		return lifted.Asm, 0, nil
	}
	accesses, escaped, blocked := frameAccesses(lifted)
	slots := qualify(accesses, escaped, blocked, fn.Frame)
	if len(slots) == 0 {
		return lifted.Asm, 0, nil
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
		return nil, 0, err
	}
	lifted.Liveness(webs)
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
	for _, w := range slotWebs {
		if w.From < 0 || len(w.Uses) == 0 {
			continue // never read: the store stays (the checker may read it)
		}
		uninitialized := false
		for _, d := range w.Defs {
			if d.Instr == nil {
				uninitialized = true
			}
		}
		if uninitialized {
			continue
		}
		s := slots[int64(w.Reg.Num)]
		crossing := false
		for _, c := range calls {
			if w.crosses(c) {
				crossing = true
			}
		}
		r, ok := slotRegister(s, w, crossing, written, regWebs, taken)
		if !ok {
			continue
		}
		for _, d := range w.Defs {
			d.Instr.Asm = slotCopy(r, regAt(d.Instr.Asm, d.Access), s, true, d.Instr.Asm.Line)
		}
		for _, u := range w.Uses {
			u.Instr.Asm = slotCopy(r, regAt(u.Instr.Asm, u.Access), s, false, u.Instr.Asm.Line)
		}
		taken[r] = append(taken[r], w)
		promoted++
	}
	out := lifted.Asm
	out.Items = lifted.Items()
	if promoted > 0 {
		declared := map[Reg]bool{}
		for _, c := range out.Clobbers {
			if r, _, _, ok, err := regOf(c); err == nil && ok {
				declared[r] = true
			}
		}
		for r := range taken {
			if !declared[r] && !calleeSaved(r) {
				out.Clobbers = append(out.Clobbers, clobberRegister(r))
			}
		}
	}
	return out, promoted, nil
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
				}
			case asm.Memory:
				if o.Base.Class != asm.ClassSP {
					continue
				}
				if o.Index != nil || o.Mode != asm.MemOffset {
					escaped = append(escaped, 0)
					continue
				}
				plain := (a.Mnemonic == "ldr" || a.Mnemonic == "str") && len(a.Operands) == 2 && i == 1
				if plain {
					if reg, ok := a.Operands[0].(asm.Register); ok {
						r, bits, lane, isReg, err := regOf(reg)
						if err == nil && isReg && !lane && (bits == 32 || bits == 64 || bits == 128) {
							accesses = append(accesses, slotAccess{ins: ins, op: 0, offset: o.Offset, bits: bits, class: r.Class, store: a.Mnemonic == "str"})
							continue
						}
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
// store and one load.
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
		ok, stores, loads := true, 0, 0
		for _, a := range list {
			if a.bits != first.bits || a.class != first.class {
				ok = false
			}
			if a.store {
				stores++
			} else {
				loads++
			}
		}
		size := int64(first.bits / 8)
		if !ok || stores == 0 || loads == 0 || offset < 0 || offset+size > frame {
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
func slotRegister(s slot, w *Web, crossing bool, written map[Reg]bool, regWebs []*Web, taken map[Reg][]*Web) (Reg, bool) {
	var candidates []Reg
	if s.class == GPR {
		for n := 9; n <= 17; n++ {
			candidates = append(candidates, Reg{GPR, n})
		}
		for n := 19; n <= 28; n++ {
			candidates = append(candidates, Reg{GPR, n})
		}
		for n := 0; n <= 7; n++ {
			candidates = append(candidates, Reg{GPR, n})
		}
	} else {
		for n := 16; n <= 31; n++ {
			candidates = append(candidates, Reg{VEC, n})
		}
		for n := 8; n <= 15; n++ {
			candidates = append(candidates, Reg{VEC, n})
		}
		for n := 0; n <= 7; n++ {
			candidates = append(candidates, Reg{VEC, n})
		}
	}
	for _, r := range candidates {
		if reserved(r) {
			continue
		}
		if calleeSaved(r) && !written[r] {
			continue // not saved by the prologue
		}
		if crossing {
			if !calleeSaved(r) || (r.Class == VEC && s.bits > 64) {
				continue
			}
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

// slotCopy spells the copy that replaces a slot access: into the slot's
// register for a store, out of it for a load, at the slot's width.
func slotCopy(r Reg, reg asm.Register, s slot, store bool, line int) asm.Instruction {
	home := spell(reg, r)
	dst, src := home, reg
	if !store {
		dst, src = reg, home
	}
	switch {
	case s.class == GPR:
		return asm.Instruction{Mnemonic: "mov", Operands: []asm.Operand{dst, src}, Line: line}
	case s.bits == 128:
		d := asm.Register{Text: "v" + itoa(dst.Num) + ".16b", Class: asm.ClassV, Num: dst.Num, Vec: "16b", Lane: -1}
		sr := asm.Register{Text: "v" + itoa(src.Num) + ".16b", Class: asm.ClassV, Num: src.Num, Vec: "16b", Lane: -1}
		return asm.Instruction{Mnemonic: "orr", Operands: []asm.Operand{d, sr, sr}, Line: line}
	default:
		return asm.Instruction{Mnemonic: "fmov", Operands: []asm.Operand{dst, src}, Line: line}
	}
}

// String spells a slot for the report.
func (s slot) String() string { return fmt.Sprintf("[sp, #%d] (%d bits)", s.offset, s.bits) }
