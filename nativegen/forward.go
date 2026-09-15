package nativegen

import "github.com/SCKelemen/oak/asm"

// Slot forwarding (docs/spec/94-assembler.md §9 "Slot forwarding"). The
// generator keeps, per memory word addressed as a constant offset from a
// base register — a frame slot from sp, a field of a record behind a
// register (an in-place parameter, the x8 result area, a span element) —
// the integer register whose value the word holds: a store records the
// register it stored, a load records the register it loaded into. A later
// load of the same word at the same width, while the register has not been
// written since, is the register's value already — the load becomes a
// `mov` into its destination, or nothing when the destination is that
// register (the increment of a record field, `ldr; add; str; ldr`, reads
// its own result). Every write of a register drops the words it held and
// the words addressed through it; a store drops the words under every
// other base (two bases may address the same memory) and the words it
// overlaps under its own; a label (paths meet), a call (the callee owns the
// scratch registers and may write memory through a span), an sp move, and
// a truncation of the emitted items drop them all. The meaning is
// unchanged: the word and the register hold the same value at the
// forwarded load (Oak.Forwarding.load_store, held_survives).

// heldSlot is the register a memory word's value is in, and its width.
type heldSlot struct {
	reg  int
	wide bool
}

// heldKey addresses a word: a base register (sp as spBase) and an offset.
type heldKey struct {
	base int
	off  int64
}

const spBase = -1

// baseOf is the forwarding base of a memory operand with a constant offset
// and no index register, or false.
func baseOf(m asm.Memory) (int, bool) {
	if m.Mode != asm.MemOffset || m.Index != nil {
		return 0, false
	}
	switch m.Base.Class {
	case asm.ClassSP:
		return spBase, true
	case asm.ClassX:
		if m.Base.Num == 31 {
			return 0, false
		}
		return m.Base.Num, true
	}
	return 0, false
}

// forwardable reports an integer register the forwarding tracks: a W or X
// register that is not the zero register.
func forwardable(r asm.Register) bool {
	return (r.Class == asm.ClassW || r.Class == asm.ClassX) && r.Num != 31
}

// forget drops every word a register holds, and every word addressed
// through it.
func (g *generator) forget(num int) {
	for key, h := range g.held {
		if h.reg == num || key.base == num {
			delete(g.held, key)
		}
	}
}

// forgetSlots drops the words a store over [off, off+size) under base
// touches, and every word under another base, which may be the same memory.
func (g *generator) forgetSlots(base int, off, size int64) {
	for key, h := range g.held {
		if key.base != base {
			delete(g.held, key)
			continue
		}
		width := int64(4)
		if h.wide {
			width = 8
		}
		if key.off < off+size && off < key.off+width {
			delete(g.held, key)
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
		base, hasBase := baseOf(m)
		if isReg && isMem && hasBase && forwardable(r) && (base == spBase || base != r.Num) {
			key := heldKey{base: base, off: m.Offset}
			wide := r.Class == asm.ClassX
			size := int64(4)
			if wide {
				size = 8
			}
			if ins.Mnemonic == "str" {
				g.forgetSlots(base, m.Offset, size)
				g.hold(key, heldSlot{reg: r.Num, wide: wide})
				return ins, true
			}
			if h, ok := g.held[key]; ok && h.wide == wide {
				if h.reg == r.Num {
					return ins, false
				}
				g.forget(r.Num)
				g.hold(key, h)
				src := wr(h.reg)
				if wide {
					src = xr(h.reg)
				}
				return g.ins("mov", r, src), true
			}
			g.forget(r.Num)
			g.hold(key, heldSlot{reg: r.Num, wide: wide})
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
				// A store: the words its extent may cover under its base
				// (a pair or a narrow store covers what it covers), and
				// every word under another base; an indexed store, any
				// word at all.
				if base, hasBase := baseOf(m); hasBase {
					g.forgetSlots(base, m.Offset, 16)
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

func (g *generator) hold(key heldKey, h heldSlot) {
	if g.held == nil {
		g.held = map[heldKey]heldSlot{}
	}
	g.held[key] = h
}
