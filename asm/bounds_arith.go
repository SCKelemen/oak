package asm

import "sort"

// Bounds through arithmetic (docs/spec/94-assembler.md §7 "Bounds through
// arithmetic"): the checker follows a proven bound through the arithmetic
// the generator spells between the guard and the access — the binary
// search midpoint `lo + (hi - lo) / 2`, a bound narrowed by a copy (`hi =
// mid`), a length divided by a power of two and an index multiplied back
// (`keys[mid * 512]` under `mid < len / 512`).
//
//   - upperFact: `value(reg) <= value(ref) >> shift`. Recorded by `lsr wD,
//     wS, #k` (D <= S >> k), by a copy of a register that has one, and by
//     a narrowing copy `mov wHi, wMid` under the index fact `wMid < wHi`
//     (the new hi is below the old, which was below or equal to the
//     referent; Oak.Assembler.narrowed_upper). The referent is canonical:
//     a span's primary length register when the root holds a length, so
//     the fact states the same registers on every path into a label and
//     survives the meet (checker.canonical).
//   - midFact: `sub wT, wHi, wLo` under `wLo < wHi` records wT = hi - lo;
//     `lsr wT, wT, #k` (k >= 1) halves it at least once; `add wMid, wLo,
//     wT` then proves `wMid < wHi` (Oak.Assembler.midpoint_below). None of
//     the three wraps: lo < hi makes the difference exact, and the sum is
//     below hi.
//   - `lsl wD, wI, #k` under `wI < wB` with `wB <= wL >> s` and `k <= s`
//     proves the slack fact `wD + 2^k <= wL` (Oak.Assembler
//     .shifted_index_slack): the index scaled back to the length's units,
//     with the 2^k elements from it inside the span; `wI << k < 2^32`
//     because it is below wL.
//
// An access admits an index guarded below a register whose upper chain
// ends at a register holding the span's length (checker.boundsLen). The
// facts die like the other guard facts — with a write to a register they
// name (a referent that is rewritten is replaced by a register proven
// equal to it, checker.equalRegister, or the fact dies), at calls — and
// join the label fixpoint as every register-keyed fact does.

// upperFact: value(reg) <= value(ref) / div, with div >= 1. A shift of k
// is the divisor 2^k, which is how every rule here spelled it while the
// only divisions the checker followed were by powers of two; a `udiv` by a
// constant that is not one records that constant instead
// (Oak.Assembler.divided_upper, upper_chain_div).
type upperFact struct {
	ref int
	div int64
}

// maxUpperDiv caps a chain's divisor. Capping is sound because it weakens
// the fact: a smaller divisor is a larger quotient, so the bound still
// holds, and the product cannot wrap.
const maxUpperDiv = int64(1) << 31

// mkUpper normalizes a divisor, so the zero value and an explicit 1 are
// the same fact — these structs are compared for equality at the meet and
// a fact stated two ways would not survive it.
func mkUpper(ref int, div int64) upperFact {
	switch {
	case div < 1:
		div = 1
	case div > maxUpperDiv:
		div = maxUpperDiv
	}
	return upperFact{ref: ref, div: div}
}

// divisor reads a fact's divisor, normalizing the zero value to 1.
func (u upperFact) divisor() int64 {
	if u.div < 1 {
		return 1
	}
	return u.div
}

// midFact: reg = hi - lo (halved at least once when halved), under lo < hi.
type midFact struct {
	lo, hi int
	halved bool
}

// maxUpperDepth bounds the chain walk; chains are acyclic (a fact on D is
// recorded only after the write of D dropped every fact naming D).
const maxUpperDepth = 16

// resolveUpper follows the upper chain from n: value(n) <= value(root) /
// div, the divisors multiplied (saturating at maxUpperDiv, which weakens
// the bound rather than breaking it; Oak.Assembler.upper_chain_div).
func (c *checker) resolveUpper(n int) (root int, div int64) {
	root, div = n, 1
	for depth := 0; depth < maxUpperDepth; depth++ {
		u, has := c.upper[root]
		if !has {
			return
		}
		root = u.ref
		if d := u.divisor(); div > maxUpperDiv/d {
			div = maxUpperDiv
		} else {
			div *= d
		}
	}
	return
}

// lenLike reports whether w register n is at most the span's length by a
// direct fact: it holds the length, it is proven equal to a register that
// does (lenEqual), or it holds a constant no larger than a constant a
// length register holds.
func (c *checker) lenLike(f *spanFact, n int) bool {
	if f.holdsLen(n) {
		return true
	}
	if c.equalLenReg(f, n) >= 0 {
		return true
	}
	if k, isConst := c.constFacts[n]; isConst {
		for reg := range f.lenRegs {
			if kl, known := c.constFacts[reg]; known && k <= kl {
				return true
			}
		}
	}
	return false
}

// equalRegister returns a register proven to hold n's value — the
// smallest other length register of the first span (by base register) n
// measures, else the register lenEqual pairs it with, else another
// register holding the same constant — or -1. Used when n is rewritten,
// to keep the facts that named it (Oak.SpanAlias.equalRegister, whose
// transliteration test pins the choice).
func (c *checker) equalRegister(n int) int {
	bases := make([]int, 0, len(c.spans))
	for base := range c.spans {
		bases = append(bases, base)
	}
	sort.Ints(bases)
	for _, base := range bases {
		fact := c.spans[base]
		if !fact.holdsLen(n) {
			continue
		}
		best := -1
		for reg := range fact.lenRegs {
			if reg != n && (best < 0 || reg < best) {
				best = reg
			}
		}
		if best >= 0 {
			return best
		}
	}
	if other, equal := c.lenEqual[n]; equal && other != n {
		return other
	}
	if k, isConst := c.constFacts[n]; isConst {
		best := -1
		for reg, kr := range c.constFacts {
			if reg != n && kr == k && (best < 0 || reg < best) {
				best = reg
			}
		}
		return best
	}
	return -1
}

// canonical names the register an upper fact should refer to for the
// value of n, never `avoid` (the register being written): the primary
// length register of a span n holds the length of, else n itself, else a
// register proven equal to it; -1 when none.
func (c *checker) canonical(n, avoid int) int {
	for _, fact := range c.spans {
		if fact.holdsLen(n) && fact.lenReg != avoid && fact.holdsLen(fact.lenReg) {
			return fact.lenReg
		}
	}
	if n != avoid {
		return n
	}
	return c.equalRegister(n)
}

// rooted resolves the chain from reg and canonicalizes its root for a
// fact on dest.
func (c *checker) rooted(reg, dest int) (upperFact, bool) {
	root, div := c.resolveUpper(reg)
	return c.refFor(root, div, dest)
}

// refFor names the referent of the bound value <= root / div for a fact
// on dest: the primary length register of a span root holds the length
// of; else, when root holds a constant no larger than a constant a length
// register holds, that register (value <= root / div <= len / div); else
// root itself, or a register proven equal to it when root is dest. The
// choice is the same on every path into a label, so the fact survives the
// meet.
func (c *checker) refFor(root int, div int64, dest int) (upperFact, bool) {
	if ref := c.constBoundedLen(root, dest); ref >= 0 {
		return mkUpper(ref, div), true
	}
	ref := c.canonical(root, dest)
	if ref < 0 || ref == dest {
		return upperFact{}, false
	}
	return mkUpper(ref, div), true
}

// constBoundedLen returns the canonical length register whose constant is
// at least the constant n holds, -1 when n holds none or no length
// register holds a constant (`b = 512` against a 512-element page).
func (c *checker) constBoundedLen(n, dest int) int {
	k, isConst := c.constFacts[n]
	if !isConst {
		return -1
	}
	for _, fact := range c.spans {
		if fact.holdsLen(n) {
			return -1 // a length register itself: canonical names it
		}
	}
	best := -1
	for _, fact := range c.spans {
		for reg := range fact.lenRegs {
			if kl, known := c.constFacts[reg]; known && k <= kl && reg != dest {
				if ref := c.canonical(reg, dest); ref >= 0 && ref != dest && (best < 0 || ref < best) {
					best = ref
				}
			}
		}
	}
	return best
}

// atMostRef names, for a fact on dest, the canonical referent register n
// is at most: through its upper chain, through the bound of its index
// fact, or itself when it holds a span's length.
func (c *checker) atMostRef(n, dest int) (upperFact, bool) {
	if _, has := c.upper[n]; has {
		return c.rooted(n, dest)
	}
	if f, has := c.idxFacts[n]; has && atMost(f) {
		return c.rooted(f.boundReg, dest)
	}
	for _, fact := range c.spans {
		if fact.holdsLen(n) {
			if ref := c.canonical(n, dest); ref >= 0 && ref != dest {
				return mkUpper(ref, 1), true
			}
			return upperFact{}, false
		}
	}
	// A constant no larger than a constant a length register holds (the
	// bound `b = 512` of a search inside a 512-element page).
	if ref := c.constBoundedLen(n, dest); ref >= 0 {
		return mkUpper(ref, 1), true
	}
	return upperFact{}, false
}

// atMost reports whether an index fact bounds its register's value by the
// bound register's: wI < wB, or wI + K <= wB with K > 0 and no wrapped
// subtraction behind the bound (need == 0).
func atMost(f idxFact) bool {
	return f.boundReg >= 0 && (!f.slack || f.need == 0)
}

// arithmeticFacts reads, before the write of dest, the facts a w-register
// data-processing instruction derives from its sources; applyArithmeticFacts
// installs them after the write.
func (c *checker) arithmeticFacts(instr Instruction, dest Register, regs []Register) (newUpper *upperFact, newIdx *idxFact, newMid *midFact) {
	if dest.Class != ClassW {
		return
	}
	switch instr.Mnemonic {
	case "mov":
		if len(regs) != 2 || len(instr.Operands) != 2 || regs[1].Class != ClassW || regs[1].ZeroRegister() {
			return
		}
		src := regs[1].Num
		if _, has := c.upper[src]; has {
			if u, ok := c.rooted(src, dest.Num); ok {
				newUpper = &u
			}
			return
		}
		// A narrowing copy: the source is below a bound, so the destination
		// is at most the bound's referent (Oak.Assembler.narrowed_upper).
		if f, has := c.idxFacts[src]; has && atMost(f) {
			if u, ok := c.rooted(f.boundReg, dest.Num); ok {
				newUpper = &u
			}
		}
	case "lsr":
		if len(regs) != 2 || len(instr.Operands) != 3 || regs[1].Class != ClassW {
			return
		}
		k, isImm := instr.Operands[2].(Immediate)
		if !isImm || k.Shift != 0 || k.Value < 1 || k.Value > 31 {
			return
		}
		src := regs[1].Num
		if m, has := c.mid[src]; has && m.lo != dest.Num && m.hi != dest.Num {
			newMid = &midFact{lo: m.lo, hi: m.hi, halved: true}
		}
		root, div := c.resolveUpper(src)
		if scale := int64(1) << uint(k.Value); div <= maxUpperDiv/scale {
			if ref := c.canonical(root, dest.Num); ref >= 0 && ref != dest.Num {
				u := mkUpper(ref, div*scale)
				newUpper = &u
			}
		}
	case "udiv":
		// `udiv wE, wS, wK` with wK holding the constant d: the quotient is
		// the source's own bound divided by d as well
		// (Oak.Assembler.divided_upper). The divisor need not be a power of
		// two — `entries = len(table) / 3` before a binary search over a
		// three-word table — which is the whole point of carrying a divisor
		// rather than a shift.
		if len(regs) != 3 || len(instr.Operands) != 3 || regs[1].Class != ClassW || regs[2].Class != ClassW {
			return
		}
		d, isConst := c.constFacts[regs[2].Num]
		if !isConst || d < 1 {
			return
		}
		root, div := c.resolveUpper(regs[1].Num)
		if div > maxUpperDiv/d {
			return
		}
		if u, ok := c.refFor(root, div*d, dest.Num); ok {
			newUpper = &u
		}
	case "mul":
		// `mul wD, wI, wK` with wK holding the constant k: under wI < wB and
		// wB <= len / d with k <= d, the k elements from wI·k lie inside the
		// span (Oak.Assembler.scaled_index_slack) — the slack fact `wD + k
		// <= len`, which `add wJ, wD, #j` then carries down to the element
		// wI·k + j for j < k (scaled_index_element). This is the `lsl` rule
		// below for a scale that is not a power of two.
		if len(regs) != 3 || len(instr.Operands) != 3 || regs[1].Class != ClassW || regs[2].Class != ClassW {
			return
		}
		for _, pair := range [2][2]int{{regs[1].Num, regs[2].Num}, {regs[2].Num, regs[1].Num}} {
			index, scale := pair[0], pair[1]
			k, isConst := c.constFacts[scale]
			if !isConst || k < 1 {
				continue
			}
			f, has := c.idxFacts[index]
			if !has {
				continue
			}
			// A constant bound scaled by a constant: wI < U leaves
			// wI·k <= (U - 1)·k, so wI·k < (U - 1)·k + 1
			// (Oak.Extents.scaled_under_bound). This is the form a table
			// read through a global takes, where no register holds a
			// length and the entry count is itself a constant — the
			// binary search over `entries = len(table) / 3`.
			if f.boundReg < 0 && !f.slack && f.bound >= 1 {
				if f.bound-1 > (maxUpperDiv-1)/k {
					continue
				}
				newIdx = &idxFact{boundReg: -1, bound: (f.bound-1)*k + 1}
				return
			}
			if !atMost(f) {
				continue
			}
			root, div := c.resolveUpper(f.boundReg)
			if div < k {
				continue
			}
			lanes := int64(1)
			if f.slack {
				lanes = f.bound
			}
			if lanes <= 0 || lanes > maxUpperDiv/k {
				continue
			}
			u, ok := c.refFor(root, 1, dest.Num)
			if !ok {
				continue
			}
			newIdx = &idxFact{boundReg: u.ref, bound: lanes * k, slack: true}
			return
		}
	case "lsl":
		if len(regs) != 2 || len(instr.Operands) != 3 || regs[1].Class != ClassW {
			return
		}
		k, isImm := instr.Operands[2].(Immediate)
		if !isImm || k.Shift != 0 || k.Value < 1 || k.Value > 31 {
			return
		}
		f, has := c.idxFacts[regs[1].Num]
		if !has || !atMost(f) {
			return
		}
		root, div := c.resolveUpper(f.boundReg)
		if div < int64(1)<<uint(k.Value) {
			return
		}
		ref := c.canonical(root, dest.Num)
		if ref < 0 || ref == dest.Num {
			return
		}
		lanes := int64(1)
		if f.slack {
			lanes = f.bound
		}
		if lanes <= 0 || lanes > int64(1)<<uint(31-k.Value) {
			return
		}
		newIdx = &idxFact{boundReg: ref, bound: lanes << uint(k.Value), slack: true}
	case "sub":
		if len(regs) != 3 || len(instr.Operands) != 3 || regs[1].Class != ClassW || regs[2].Class != ClassW {
			return
		}
		hi, lo := regs[1].Num, regs[2].Num
		if dest.Num == hi || dest.Num == lo {
			return
		}
		// The bound is hi itself, or the constant hi holds (a compare
		// against a register holding a constant guards as an immediate
		// compare, cmpFact.imm).
		f, has := c.idxFacts[lo]
		if !has {
			return
		}
		belowHi := atMost(f) && f.boundReg == hi
		if k, isConst := c.constFacts[hi]; isConst && f.boundReg < 0 && !f.slack && f.bound == k {
			belowHi = true
		}
		if belowHi {
			newMid = &midFact{lo: lo, hi: hi}
		}
	case "csel":
		// A select of two bounded values is bounded (Oak.Assembler
		// .select_upper, select_index): the if-converted arms keep the
		// facts their variables had (nativegen/select.go).
		if len(regs) != 3 || regs[1].Class != ClassW || regs[2].Class != ClassW {
			return
		}
		a, b := regs[1].Num, regs[2].Num
		if ua, okA := c.atMostRef(a, dest.Num); okA {
			if ub, okB := c.atMostRef(b, dest.Num); okB && ua == ub {
				newUpper = &ua
			}
		}
		if fa, hasA := c.idxFacts[a]; hasA {
			if fb, hasB := c.idxFacts[b]; hasB && fa == fb && fa.boundReg != dest.Num {
				newIdx = &fa
			}
		}
	case "add":
		if len(instr.Operands) == 3 {
			// The halving folded into the add's operand: `add wMid, wLo,
			// wT, lsr #k` under wT = hi - lo is the midpoint in one
			// instruction (machine.Fuse), the same lemma
			// (Oak.Assembler.midpoint_below) as `lsr` then `add`.
			if sh, isShifted := instr.Operands[2].(Shifted); isShifted && sh.Kind == "lsr" && sh.Amount >= 1 && sh.Amount <= 31 && sh.Reg.Class == ClassW && len(regs) >= 2 && regs[1].Class == ClassW {
				if m, has := c.mid[sh.Reg.Num]; has && m.lo == regs[1].Num && m.hi != dest.Num && sh.Reg.Num != dest.Num {
					newIdx = &idxFact{boundReg: m.hi}
				}
				return
			}
		}
		if len(regs) != 3 || len(instr.Operands) != 3 || regs[1].Class != ClassW || regs[2].Class != ClassW {
			return
		}
		a, b := regs[1].Num, regs[2].Num
		for _, pair := range [2][2]int{{a, b}, {b, a}} {
			if m, has := c.mid[pair[1]]; has && m.halved && m.lo == pair[0] && m.hi != dest.Num {
				newIdx = &idxFact{boundReg: m.hi}
				return
			}
		}
	}
	return
}

// applyArithmeticFacts installs the facts arithmeticFacts derived, after
// the write of dest dropped what its old value supported.
func (c *checker) applyArithmeticFacts(dest Register, newUpper *upperFact, newIdx *idxFact, newMid *midFact) {
	if newUpper != nil {
		c.upper[dest.Num] = *newUpper
	}
	if newIdx != nil {
		c.idxFacts[dest.Num] = *newIdx
	}
	if newMid != nil {
		c.mid[dest.Num] = *newMid
	}
}

// forgetArithmeticFacts drops what a rewritten register supported among
// the arithmetic facts: its own, and the facts naming it as a referent
// or a midpoint operand — a referent is replaced by a register proven
// equal to the old value when there is one.
func (c *checker) forgetArithmeticFacts(num, equal int) {
	delete(c.upper, num)
	for reg, u := range c.upper {
		if u.ref != num {
			continue
		}
		if equal >= 0 && equal != reg {
			u.ref = equal
			c.upper[reg] = u
		} else {
			delete(c.upper, reg)
		}
	}
	delete(c.mid, num)
	for reg, m := range c.mid {
		if m.lo == num || m.hi == num {
			delete(c.mid, reg)
		}
	}
}

// Generic map helpers for the guard state.

func copyMap[K comparable, V any](m map[K]V) map[K]V {
	out := make(map[K]V, len(m))
	for k, v := range m {
		out[k] = v
	}
	return out
}

// meetMap keeps the entries both sides agree on.
func meetMap[K, V comparable](a, b map[K]V) map[K]V {
	out := map[K]V{}
	for k, va := range a {
		if vb, ok := b[k]; ok && va == vb {
			out[k] = va
		}
	}
	return out
}

func equalMap[K, V comparable](a, b map[K]V) bool {
	if len(a) != len(b) {
		return false
	}
	for k, va := range a {
		if vb, ok := b[k]; !ok || va != vb {
			return false
		}
	}
	return true
}

func equalSet(a, b map[int]bool) bool {
	if len(a) != len(b) {
		return false
	}
	for k := range a {
		if !b[k] {
			return false
		}
	}
	return true
}
