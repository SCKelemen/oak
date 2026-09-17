package machine

import "github.com/SCKelemen/oak/asm"

// splitFramePairInitializers exposes four independently accessed W words
// hidden by one X-register pair store. The source loads stay in place: all
// source bytes have been read before the stores, just as before. Only dead,
// already-clobbered data registers may be shifted to expose their high halves.
// The returned word offsets let promotion discard this expansion when none
// of the exposed words actually obtains a register.
func splitFramePairInitializers(f *Function, objects []FrameObject) (*asm.Function, map[int64]bool, error) {
	if f.t.arch != asm.ArchArm64 || f.Asm.Frame <= 0 || len(objects) == 0 {
		return nil, nil, nil
	}
	// Most frame-bearing functions have no X-pair initializer. Avoid
	// computing another web/liveness graph for those ordinary candidates.
	hasPair := false
	for _, instruction := range f.Instrs {
		pair := instruction.Asm
		if pair.Mnemonic != "stp" || len(pair.Operands) != 3 {
			continue
		}
		a, aOK := pair.Operands[0].(asm.Register)
		b, bOK := pair.Operands[1].(asm.Register)
		m, mOK := pair.Operands[2].(asm.Memory)
		if aOK && bOK && mOK && a.Class == asm.ClassX && b.Class == asm.ClassX &&
			a.Num != b.Num && a.Num >= 0 && a.Num < 31 && b.Num >= 0 && b.Num < 31 &&
			!f.t.reserved(Reg{GPR, a.Num}) && !f.t.reserved(Reg{GPR, b.Num}) &&
			m.Base.Class == asm.ClassSP && m.Mode == asm.MemOffset && m.Index == nil {
			hasPair = true
			break
		}
	}
	if !hasPair {
		return nil, nil, nil
	}
	accesses, escaped, blocked := frameAccesses(f)
	if len(escaped) != 0 {
		return nil, nil, nil
	}
	// Unknown/out-of-frame ranges do not authorize this narrower path.
	for _, a := range accesses {
		if a.offset < 0 || a.offset > f.Asm.Frame-int64(a.bits/8) {
			return nil, nil, nil
		}
	}
	for _, b := range blocked {
		if b[0] < 0 || b[1] < b[0] || b[1] > f.Asm.Frame {
			return nil, nil, nil
		}
	}
	clobbered := map[Reg]bool{}
	for _, r := range f.Asm.Clobbers {
		if reg, _, _, ok, err := f.t.regOf(r); err == nil && ok {
			clobbered[reg] = true
		}
	}
	webs, err := f.Webs()
	if err != nil {
		return nil, nil, err
	}
	f.liveRanges(webs)
	replacements := map[int][]asm.Item{}
	words := map[int64]bool{}
	for _, instruction := range f.Instrs {
		pair := instruction.Asm
		if pair.Mnemonic != "stp" || len(pair.Operands) != 3 {
			continue
		}
		a, aOK := pair.Operands[0].(asm.Register)
		b, bOK := pair.Operands[1].(asm.Register)
		m, mOK := pair.Operands[2].(asm.Memory)
		if !aOK || !bOK || !mOK || a.Class != asm.ClassX || b.Class != asm.ClassX || a.Num == b.Num ||
			a.Num < 0 || a.Num >= 31 || b.Num < 0 || b.Num >= 31 ||
			f.t.reserved(Reg{GPR, a.Num}) || f.t.reserved(Reg{GPR, b.Num}) ||
			!clobbered[Reg{GPR, a.Num}] || !clobbered[Reg{GPR, b.Num}] ||
			m.Base.Class != asm.ClassSP || m.Mode != asm.MemOffset || m.Index != nil ||
			m.Offset < 0 || m.Offset > 504 || m.Offset%8 != 0 || m.Offset > f.Asm.Frame-16 {
			continue
		}
		inside := false
		for _, object := range objects {
			if object.Offset >= 0 && object.Size > 0 && object.Offset <= f.Asm.Frame && object.Size <= f.Asm.Frame-object.Offset &&
				object.Offset <= m.Offset && m.Offset+16 <= object.Offset+object.Size {
				inside = true
				break
			}
		}
		if !inside {
			continue
		}
		live := false
		for _, web := range webs {
			if web.Reg.Class == GPR && (web.Reg.Num == a.Num || web.Reg.Num == b.Num) && web.liveAt(defPos(instruction)) {
				live = true
				break
			}
		}
		if live || !pairHasOnlyWordAccesses(m.Offset, accesses, blocked) {
			continue
		}
		// Reuse the already-clobbered data registers only after their low
		// halves have been stored. W/X aliases were checked together above.
		wordA, wordB := a, b
		wordA.Class, wordA.Text = asm.ClassW, "w"+itoa(a.Num)
		wordB.Class, wordB.Text = asm.ClassW, "w"+itoa(b.Num)
		at := func(delta int64) asm.Memory { out := m; out.Offset += delta; return out }
		makeInstruction := func(mnemonic string, operands ...asm.Operand) asm.Item {
			return asm.Instruction{Mnemonic: mnemonic, Operands: operands, Line: pair.Line}
		}
		replacements[instruction.Index] = []asm.Item{
			makeInstruction("str", wordA, at(0)),
			makeInstruction("lsr", a, a, asm.Immediate{Value: 32}),
			makeInstruction("str", wordA, at(4)),
			makeInstruction("str", wordB, at(8)),
			makeInstruction("lsr", b, b, asm.Immediate{Value: 32}),
			makeInstruction("str", wordB, at(12)),
		}
		for delta := int64(0); delta < 16; delta += 4 {
			words[m.Offset+delta] = true
		}
	}
	if len(replacements) == 0 {
		return nil, nil, nil
	}
	out := cloneFunction(f.Asm)
	items := out.Items
	out.Items = nil
	index := 0
	for _, item := range items {
		if _, isInstruction := item.(asm.Instruction); isInstruction {
			if replacement, ok := replacements[index]; ok {
				out.Items = append(out.Items, replacement...)
			} else {
				out.Items = append(out.Items, item)
			}
			index++
		} else {
			out.Items = append(out.Items, item)
		}
	}
	return out, words, nil
}

func pairHasOnlyWordAccesses(offset int64, accesses []slotAccess, blocked [][2]int64) bool {
	read := [4]bool{}
	for _, access := range accesses {
		if access.offset >= offset+16 || access.offset+int64(access.bits/8) <= offset {
			continue
		}
		if access.class != GPR || access.bits != 32 || access.offset < offset || access.offset > offset+12 || (access.offset-offset)%4 != 0 {
			return false
		}
		if !access.store {
			read[(access.offset-offset)/4] = true
		}
	}
	ignoredPair := false
	for _, extent := range blocked {
		if !ignoredPair && extent == [2]int64{offset, offset + 16} {
			ignoredPair = true // exactly this pair store, not another overlap
			continue
		}
		if extent[0] < offset+16 && offset < extent[1] {
			return false
		}
	}
	return ignoredPair && read[0] && read[1] && read[2] && read[3]
}
