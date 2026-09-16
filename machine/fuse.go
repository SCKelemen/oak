package machine

import "github.com/SCKelemen/oak/asm"

// Peephole fusion over the lifted IR (docs/notes/optimizer-search-2026-09.md
// §16 Phase B): two instructions the lowering emits one after the other
// become the one AArch64 instruction that does both, where the lifted
// webs show the intermediate register has one definition and one use in
// the same block and nothing it reads changes in between. The binary
// search's inner loop (benchmarks/kernels, `search`, `page_probe`) is
// eleven instructions where clang's is nine; these two fusions are the
// difference:
//
//	lsr w9, w9, #1; add w25, w7, w9      →  add w25, w7, w9, lsr #1
//	add w10, w25, #1; csel w7, w10, w7, lo →  csinc w7, w7, w25, hs
//
// The fusion is a candidate like any other: the checker and the verifier
// judge it, and it ships only on a verdict (a gated transform).

// invertCondition is the AArch64 condition an instruction takes to select
// the other operand.
var invertCondition = map[string]string{"eq": "ne", "ne": "eq", "hs": "lo", "cs": "cc", "lo": "hs", "cc": "cs", "hi": "ls", "ls": "hi", "ge": "lt", "lt": "ge", "gt": "le", "le": "gt", "mi": "pl", "pl": "mi", "vs": "vc", "vc": "vs"}

// Fuse rewrites the function in place and reports how many pairs fused.
func (f *Function) Fuse() (int, error) {
	webs, err := f.Webs()
	if err != nil {
		return 0, err
	}
	defWeb := map[*Instr]*Web{}
	for _, w := range webs {
		for _, d := range w.Defs {
			if d.Instr != nil && len(d.Instr.Defs) == 1 {
				defWeb[d.Instr] = w
			}
		}
	}
	fused := 0
	for _, b := range f.Blocks {
		kept := make([]*Instr, 0, len(b.Instrs))
		removed := map[*Instr]bool{}
		for i, ins := range b.Instrs {
			if removed[ins] {
				continue
			}
			w := defWeb[ins]
			if w == nil || len(w.Defs) != 1 || len(w.Uses) != 1 || w.Uses[0].Instr == nil || w.Uses[0].Instr.Block != b {
				kept = append(kept, ins)
				continue
			}
			use := w.Uses[0]
			j := indexIn(b, use.Instr)
			if j <= i || !f.sourceStable(b, i, j, ins) {
				kept = append(kept, ins)
				continue
			}
			if f.fuseShift(ins, use) || f.fuseIncrement(ins, use) {
				fused++
				removed[ins] = true
				continue
			}
			kept = append(kept, ins)
		}
		b.Instrs = kept
	}
	if fused > 0 {
		f.reindex()
	}
	return fused, nil
}

func indexIn(b *Block, ins *Instr) int {
	for k, x := range b.Instrs {
		if x == ins {
			return k
		}
	}
	return -1
}

// sourceStable reports that the registers the producer reads are not
// written between it (exclusive) and the consumer (exclusive), so the
// fused instruction reads the same values the producer did.
func (f *Function) sourceStable(b *Block, i, j int, producer *Instr) bool {
	for _, u := range producer.Uses {
		for k := i + 1; k < j; k++ {
			for _, d := range b.Instrs[k].Defs {
				if d.Reg == u.Reg {
					return false
				}
			}
			if b.Instrs[k].Call {
				return false
			}
		}
	}
	return true
}

// fuseShift folds `lsl/lsr/asr wT, wS, #k` into the add or sub that reads
// wT as its second source: `add wD, wA, wS, <shift> #k`.
func (f *Function) fuseShift(producer *Instr, use site) bool {
	a := producer.Asm
	switch a.Mnemonic {
	case "lsl", "lsr", "asr":
	default:
		return false
	}
	if len(a.Operands) != 3 {
		return false
	}
	t, okT := a.Operands[0].(asm.Register)
	s, okS := a.Operands[1].(asm.Register)
	k, okK := a.Operands[2].(asm.Immediate)
	if !okT || !okS || !okK || t.Class != s.Class || k.Shift != 0 || k.Value <= 0 {
		return false
	}
	c := use.Instr.Asm
	if (c.Mnemonic != "add" && c.Mnemonic != "sub") || c.Cond != "" || len(c.Operands) != 3 || use.Access.Op != 2 {
		return false
	}
	d, okD := c.Operands[0].(asm.Register)
	x, okX := c.Operands[1].(asm.Register)
	y, okY := c.Operands[2].(asm.Register)
	if !okD || !okX || !okY || d.Class != t.Class || x.Class != t.Class || y.Num != t.Num || y.Class != t.Class || d.ZeroRegister() {
		return false
	}
	width := int64(32)
	if t.Class == asm.ClassX {
		width = 64
	}
	if t.Class != asm.ClassW && t.Class != asm.ClassX || k.Value >= width {
		return false
	}
	use.Instr.Asm.Operands[2] = asm.Shifted{Reg: s, Kind: a.Mnemonic, Amount: k.Value}
	return true
}

// fuseIncrement folds `add wT, wX, #1` into the csel that selects wT:
// `csel wD, wT, wB, c` becomes `csinc wD, wB, wX, !c`, and `csel wD, wA,
// wT, c` becomes `csinc wD, wA, wX, c`.
func (f *Function) fuseIncrement(producer *Instr, use site) bool {
	a := producer.Asm
	if a.Mnemonic != "add" || len(a.Operands) != 3 {
		return false
	}
	t, okT := a.Operands[0].(asm.Register)
	x, okX := a.Operands[1].(asm.Register)
	one, okOne := a.Operands[2].(asm.Immediate)
	if !okT || !okX || !okOne || one.Value != 1 || one.Shift != 0 || t.Class != x.Class || x.ZeroRegister() {
		return false
	}
	c := use.Instr.Asm
	if c.Mnemonic != "csel" || len(c.Operands) != 4 {
		return false
	}
	cond, okC := c.Operands[3].(asm.Condition)
	d, okD := c.Operands[0].(asm.Register)
	p, okP := c.Operands[1].(asm.Register)
	q, okQ := c.Operands[2].(asm.Register)
	if !okC || !okD || !okP || !okQ || d.Class != t.Class || p.Class != t.Class || q.Class != t.Class {
		return false
	}
	inverted, known := invertCondition[cond.Code]
	if !known {
		return false
	}
	switch use.Access.Op {
	case 1: // c ? T : q  →  csinc d, q, x, !c
		use.Instr.Asm = asm.Instruction{Mnemonic: "csinc", Operands: []asm.Operand{d, q, x, asm.Condition{Code: inverted}}, Line: c.Line, CheckedFacts: c.CheckedFacts}
	case 2: // c ? p : T  →  csinc d, p, x, c
		use.Instr.Asm = asm.Instruction{Mnemonic: "csinc", Operands: []asm.Operand{d, p, x, asm.Condition{Code: cond.Code}}, Line: c.Line, CheckedFacts: c.CheckedFacts}
	default:
		return false
	}
	return true
}

// Fuse lifts a body, fuses its pairs, and lowers it back; it reports the
// pairs fused. An error is the lift's; the caller keeps its body.
func Fuse(fn *asm.Function) (*asm.Function, int, error) {
	lifted, err := Lift(cloneFunction(fn))
	if err != nil {
		return nil, 0, err
	}
	fused, err := lifted.Fuse()
	if err != nil {
		return nil, 0, err
	}
	out := lifted.Asm
	out.Items = lifted.Items()
	return out, fused, nil
}
