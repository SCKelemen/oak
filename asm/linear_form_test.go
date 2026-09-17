package asm

import (
	"strings"
	"testing"
)

// The linear normal form sees through a low mask that covers the operand's
// known bits: `u64(index)` over a u16 parameter (`index and 0xFFFF` on the
// Oak side, `and w1, w1, #65535` read at 64 bits on the machine's) is the
// parameter, so `pool_base + index * 4096` and `pool_base + (index << 12)`
// are one form (the OS pilot's page_pa, which exceeded the bit-level
// budget as a 64-bit sum of two unknowns). A mask that does not cover the
// operand keeps the form nonlinear.
func TestLinearFormSeesThroughLowMasks(t *testing.T) {
	index := &term{kind: termParam, width: 64, name: "index", declared: 16}
	base := paramTerm("pool_base", 64)
	oak := binaryTerm("add", base, binaryTerm("mul", binaryTerm("and", index, constTerm(0xFFFF, 64)), constTerm(4096, 64)))
	machine := binaryTerm("add", base, binaryTerm("shl", zeroExtend(binaryTerm("and", truncate(index, 32), constTerm(65535, 32)), 64), constTerm(12, 64)))
	l, r := oak.linearAt(64), machine.linearAt(64)
	if l == nil || r == nil {
		t.Fatalf("both forms must be linear: oak %v, machine %v", l, r)
	}
	if !l.equal(r) {
		t.Fatalf("the forms differ: oak %s, machine %s", l, r)
	}
	if c := l.coeffs["index"]; c != 4096 || l.coeffs["pool_base"] != 1 {
		t.Fatalf("unexpected coefficients: %s", l)
	}
	// The machine's read of the argument register: the unspecified upper
	// bits beside the u16 value, cleared by the mask.
	hi := paramTerm("index#hi", 32)
	read := binaryTerm("and", binaryTerm("or", binaryTerm("shl", hi, constTerm(16, 32)), truncate(index, 32)), constTerm(65535, 32))
	viaRegister := binaryTerm("add", base, binaryTerm("shl", zeroExtend(read, 64), constTerm(12, 64)))
	if v := viaRegister.linearAt(64); v == nil || !v.equal(l) {
		t.Fatalf("the register read must strip its upper bits: %v vs %s", v, l)
	}
	// A memory read at a symbolic index is an atom: the same read on both
	// sides (one memory, one index) is one unknown.
	dom := paramTerm("dom", 32)
	poolBase := selectTerm("s.pool_base", dom, 64)
	root := selectTerm("s.root", dom, 16)
	oakRead := binaryTerm("add", poolBase, binaryTerm("mul", zeroExtend(root, 64), constTerm(4096, 64)))
	machineRead := binaryTerm("add", selectTerm("s.pool_base", dom, 64), binaryTerm("shl", binaryTerm("and", zeroExtend(selectTerm("s.root", dom, 16), 64), constTerm(0xFFFF, 64)), constTerm(12, 64)))
	lr, rr := oakRead.linearAt(64), machineRead.linearAt(64)
	if lr == nil || rr == nil || !lr.equal(rr) {
		t.Fatalf("reads must be atoms of one form: %v vs %v", lr, rr)
	}
	other := binaryTerm("add", selectTerm("s.pool_base", paramTerm("k", 32), 64), constTerm(0, 64))
	if o := other.linearAt(64); o == nil || o.equal(poolBase.linearAt(64)) {
		t.Fatalf("reads at different indices must be different atoms")
	}
	// A mask narrower than the parameter is not the identity.
	narrow := binaryTerm("and", index, constTerm(0xFF, 64))
	if narrow.linearAt(64) != nil {
		t.Fatalf("a mask below the parameter's width must stay nonlinear")
	}
	// A mask that is not low ones is not the identity either.
	holes := binaryTerm("and", index, constTerm(0xFF00, 64))
	if holes.linearAt(64) != nil {
		t.Fatalf("a mask with holes must stay nonlinear")
	}
}

// A memory read is an atom of the form named by its memory and its
// index's own linear normal form, so two reads whose index terms are
// spelled differently but agree modulo the index width are one unknown:
// the OS pilot's get_page_entry, `s[dom].pages[cell(t, i)]`, reads at
// `49152 * dom + (t and 65535) shl 11 + i` on the Oak side and at
// `49152 * ((dom and 0xFFFFFFFF) and 0xFFFFFFFF) + (((t#hi shl 16) or t)
// and 65535) shl 11 + i` on the machine's.
func TestLinearFormNamesSelectsByIndexForm(t *testing.T) {
	dom, i := paramTerm("dom", 32), paramTerm("i", 32)
	tbl, hi := paramTerm("t", 16), paramTerm("t#hi", 32)
	oakIndex := binaryTerm("add", binaryTerm("mul", constTerm(49152, 32), dom),
		binaryTerm("add", binaryTerm("shl", binaryTerm("and", zeroExtend(tbl, 32), constTerm(65535, 32)), constTerm(11, 32)), i))
	wideDom := binaryTerm("and", binaryTerm("and", dom, constTerm(0xFFFFFFFF, 32)), constTerm(0xFFFFFFFF, 32))
	register := binaryTerm("and", binaryTerm("or", binaryTerm("shl", hi, constTerm(16, 32)), zeroExtend(tbl, 32)), constTerm(65535, 32))
	asmIndex := binaryTerm("add", binaryTerm("mul", constTerm(49152, 32), wideDom),
		binaryTerm("add", binaryTerm("shl", register, constTerm(11, 32)), i))
	oak, machine := selectTerm("s.pages", oakIndex, 64), selectTerm("s.pages", asmIndex, 64)
	l, r := oak.linearAt(64), machine.linearAt(64)
	if l == nil || r == nil || !l.equal(r) {
		t.Fatalf("reads at indices equal in linear normal form must be one atom:\n  oak %v\n  asm %v", l, r)
	}
	if !strings.Contains(l.String(), "s.pages[49152*dom + i + 2048*t]") {
		t.Fatalf("the atom is named by the index's form: %v", l)
	}
	// An index outside the form keeps its spelling, and a different
	// index is a different atom.
	other := selectTerm("s.pages", binaryTerm("add", oakIndex, constTerm(1, 32)), 64)
	if o := other.linearAt(64); o == nil || o.equal(l) {
		t.Fatalf("a read at another index must not merge: %v vs %v", o, l)
	}
}
