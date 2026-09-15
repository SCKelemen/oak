package nativegen

import "github.com/SCKelemen/oak/asm"

// Frame-slot forwarding (docs/spec/94-assembler.md §9 "Slot forwarding").
// The generator keeps, per frame slot addressed from sp, the integer
// register whose value the slot holds: a store records the register it
// stored, a load records the register it loaded into. A later load of the
// same slot at the same width, while the register has not been written
// since, is the register's value already — the load becomes a `mov` into
// its destination, or nothing when the destination is that register (the
// increment of a record field, `ldr; add; str; ldr`, reads its own result).
// Every write of a register drops the slots it held; a label (paths meet),
// a call (the callee owns the scratch registers and may write frame memory
// through a span), a store through a base other than sp (frame memory
// reached by address), an sp move, and a truncation of the emitted items
// drop them all. The meaning is unchanged: the slot and the register hold
// the same value at the forwarded load (Oak.Forwarding.load_store).

// heldSlot is the register a frame slot's value is in, and its width.
type heldSlot struct {
	reg  int
	wide bool
}

// forwardable reports an integer register the forwarding tracks: a W or X
// register that is not the zero register.
func forwardable(r asm.Register) bool {
	return (r.Class == asm.ClassW || r.Class == asm.ClassX) && r.Num != 31
}

// forget drops every slot a register holds.
func (g *generator) forget(num int) {
	for off, h := range g.held {
		if h.reg == num {
			delete(g.held, off)
		}
	}
}

// forgetSlots drops the slots a store over [off, off+size) touches.
func (g *generator) forgetSlots(off, size int64) {
	for at, h := range g.held {
		width := int64(4)
		if h.wide {
			width = 8
		}
		if at < off+size && off < at+width {
			delete(g.held, at)
		}
	}
}

// forgetAll drops every held slot.
func (g *generator) forgetAll() { g.held = nil }

// noRegisterWrite lists the mnemonics that write no general register.
var noRegisterWrite = map[string]bool{"str": true, "strb": true, "strh": true, "stur": true, "stp": true, "stlr": true, "stlrb": true, "stlrh": true, "cmp": true, "cmn": true, "tst": true, "ccmp": true, "ccmn": true, "b": true, "b.": true, "cbz": true, "cbnz": true, "tbz": true, "tbnz": true, "ret": true, "brk": true, "dmb": true, "dsb": true, "isb": true, "nop": true, "prfm": true, "msr": true, "eret": true}

// forward runs the forwarding over an instruction about to be appended and
// returns the instruction to append, or false when nothing is appended.
func (g *generator) forward(ins asm.Instruction) (asm.Instruction, bool) {
	if g.rvLane {
		return ins, true
	}
	if len(ins.Operands) == 2 && (ins.Mnemonic == "str" || ins.Mnemonic == "ldr") {
		r, isReg := ins.Operands[0].(asm.Register)
		m, isMem := ins.Operands[1].(asm.Memory)
		if isReg && isMem && forwardable(r) && m.Base.Class == asm.ClassSP && m.Mode == asm.MemOffset && m.Index == nil {
			wide := r.Class == asm.ClassX
			size := int64(4)
			if wide {
				size = 8
			}
			if ins.Mnemonic == "str" {
				g.forgetSlots(m.Offset, size)
				g.hold(m.Offset, heldSlot{reg: r.Num, wide: wide})
				return ins, true
			}
			if h, ok := g.held[m.Offset]; ok && h.wide == wide {
				if h.reg == r.Num {
					return ins, false
				}
				g.forget(r.Num)
				g.hold(m.Offset, h)
				src := wr(h.reg)
				if wide {
					src = xr(h.reg)
				}
				return g.ins("mov", r, src), true
			}
			g.forget(r.Num)
			g.hold(m.Offset, heldSlot{reg: r.Num, wide: wide})
			return ins, true
		}
	}
	switch ins.Mnemonic {
	case "bl", "blr":
		g.forgetAll()
		return ins, true
	}
	if noRegisterWrite[ins.Mnemonic] {
		if n := len(ins.Operands); n > 0 {
			if m, isMem := ins.Operands[n-1].(asm.Memory); isMem {
				// A store: to frame slots by their extent (a pair or a
				// narrow store covers what it covers), through another
				// base to any memory.
				if m.Base.Class == asm.ClassSP && m.Mode == asm.MemOffset && m.Index == nil {
					g.forgetSlots(m.Offset, 16)
				} else {
					g.forgetAll()
				}
			}
		}
		return ins, true
	}
	if len(ins.Operands) == 0 {
		return ins, true
	}
	if dst, isReg := ins.Operands[0].(asm.Register); isReg {
		if dst.Class == asm.ClassSP {
			g.forgetAll()
			return ins, true
		}
		if dst.Class == asm.ClassW || dst.Class == asm.ClassX {
			g.forget(dst.Num)
		}
	}
	if ins.Mnemonic == "ldp" || ins.Mnemonic == "ldxp" || ins.Mnemonic == "ldaxp" {
		if second, isReg := ins.Operands[1].(asm.Register); isReg && (second.Class == asm.ClassW || second.Class == asm.ClassX) {
			g.forget(second.Num)
		}
	}
	if n := len(ins.Operands); n > 1 {
		if m, isMem := ins.Operands[n-1].(asm.Memory); isMem && m.Mode != asm.MemOffset {
			// A pre- or post-indexed access writes its base.
			g.forget(m.Base.Num)
		}
	}
	return ins, true
}

func (g *generator) hold(off int64, h heldSlot) {
	if g.held == nil {
		g.held = map[int64]heldSlot{}
	}
	g.held[off] = h
}
