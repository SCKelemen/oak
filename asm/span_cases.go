package asm

// Two after-loop span memories decided by cases (docs/spec/94-assembler.md
// §9, "Loop invariants", the span memories after the loops). The OS
// pilot's map_page writes one descriptor whose bits depend on a two-bit
// permission: the Oak side writes one value with two small conditionals
// inside it, the machine branches four ways on the permission and writes a
// constant per branch, and both spell the leaf's index with different
// masks. The premise decides most of both memories through its facts
// (pruneUnderFacts), but its diagram is past every budget, so the remaining
// difference — the permission's cases and the index spelling — is settled
// here without a diagram: a case split on the small comparisons over
// parameters the facts leave open, and in each case the two memories
// pruned under the case's facts and respelled with every linear subterm in
// its normal form, until they are one term. A case that is not one term
// leaves the decision to the bit-level implication as before.

import (
	"fmt"
	"math/bits"
	"os"
	"sort"
)

// spanCaseSplitLimit bounds the comparisons split on: 2^n cases, each a
// fact pass and a canonical walk over both memories.
const spanCaseSplitLimit = 3

// spanCaseConditionNodes bounds a comparison split on: a permission test,
// a status test — not an index equality over memory reads.
const spanCaseConditionNodes = 8

// spanEqualByCases decides oak = machine under premise by the case split
// described above; decided is false when some case does not close.
func spanEqualByCases(fn string, name string, premise, oak, machine *term, implies func(premise, a, b *term) (bool, bool)) (equal, decided bool) {
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	conditions := spanSplitConditions(premise, []*term{oak, machine}, spanCaseSplitLimit)
	for assignment := 0; assignment < 1<<len(conditions); assignment++ {
		p := premise
		for i, c := range conditions {
			if assignment>>i&1 == 1 {
				p = binaryTerm("and", p, c)
			} else {
				p = binaryTerm("and", p, negatedCmp(c))
			}
		}
		pruned := pruneUnderFacts(p, []*term{oak, machine})
		cmemo, cbool := map[*term]*term{}, map[*term]bool{}
		a := respell(canonicalMemo(pruned[0], cmemo, cbool))
		b := respell(canonicalMemo(pruned[1], cmemo, cbool))
		if !equalTerms(a, b) {
			// Not one term: the case's respelled memories are still far
			// smaller than the originals (the facts settled the status
			// chains, the forms settled the indices), so the bit-level
			// implication is tried on them under the case before the
			// whole decision is given up.
			if implies != nil {
				if holds, known := implies(p, a, b); known && holds {
					continue
				}
			}
			if trace {
				fmt.Fprintf(os.Stderr, "verify %s: span %s by cases: case %d of %d over %v is not one term\n  oak: %s\n  asm: %s\n", fn, name, assignment, 1<<len(conditions), conditions, a, b)
			}
			return false, false
		}
	}
	if trace {
		fmt.Fprintf(os.Stderr, "verify %s: span %s decided by %d case(s) over %v\n", fn, name, 1<<len(conditions), conditions)
	}
	return true, true
}

// spanSplitConditions collects the comparisons to split on: small, over
// parameters alone (no memory read), not a constant once respelled
// (`(0 and 255) eq 0`), not already decided by the premise's facts, in a
// fixed order, at most limit of them.
func spanSplitConditions(premise *term, terms []*term, limit int) []*term {
	seen := map[*term]bool{}
	byText := map[string]*term{}
	// One size memo for the walk: termSize is a tree size memoized by
	// node, and a fresh memo at every comparison met re-walked the shared
	// graph below it (ap_certificate_after_proven hung here for an hour).
	sizes := map[*term]int{}
	linear := map[*term]*term{}
	var walk func(*term)
	walk = func(t *term) {
		if t == nil || seen[t] {
			return
		}
		seen[t] = true
		if t.kind == termCmp && termSize(t, sizes) <= spanCaseConditionNodes && !readsMemory(t) {
			// One canonical memo serves the walk just as one size memo does.
			// A comparison already proved constant is semantically dead here;
			// neither it nor comparisons below it need a case split.
			if canonicalLinear(t, linear).kind == termConst {
				return
			}
			text := t.String()
			if _, dup := byText[text]; !dup {
				byText[text] = t
			}
			return
		}
		walk(t.cond)
		walk(t.left)
		walk(t.right)
	}
	for _, t := range terms {
		walk(t)
	}
	texts := make([]string, 0, len(byText))
	for text := range byText {
		texts = append(texts, text)
	}
	sort.Strings(texts)
	var out []*term
	for _, text := range texts {
		c := byText[text]
		if negatedCmp(c) == nil {
			continue
		}
		if decided := pruneUnderFacts(premise, []*term{c}); decided[0].kind == termConst {
			continue
		}
		out = append(out, c)
		if len(out) == limit {
			break
		}
	}
	return out
}

// readsMemory reports whether a term contains a memory read.
func readsMemory(t *term) bool {
	seen := map[*term]bool{}
	var walk func(*term) bool
	walk = func(t *term) bool {
		if t == nil || seen[t] {
			return false
		}
		seen[t] = true
		if t.kind == termSelect {
			return true
		}
		return walk(t.cond) || walk(t.left) || walk(t.right)
	}
	return walk(t)
}

// respellPasses bounds the passes respell makes: one pass leaves the
// terms a stripped mask builds (stripAbove) with their own children not
// yet respelled, and the second settles them; a third is a guard.
const respellPasses = 3

// respell is canonicalLinear to a fixpoint, each pass over a fresh memo.
func respell(t *term) *term {
	for i := 0; i < respellPasses; i++ {
		next := canonicalLinear(t, map[*term]*term{})
		if equalTerms(next, t) {
			return next
		}
		t = next
	}
	return t
}

// canonicalLinear respells a term so that subterms equal modulo their
// width read the same: a linear subterm becomes its normal form written
// out in one fixed order over its atoms (each atom respelled first, a
// memory read's index included), and an equality or inequality of two
// terms with the same form is its constant. The result equals the input
// on every assignment — the form is exact modulo the width — so a
// decision over the respelled terms is a decision over the originals.
func canonicalLinear(t *term, memo map[*term]*term) *term {
	if t == nil {
		return nil
	}
	if done, seen := memo[t]; seen {
		return done
	}
	out := t
	switch t.kind {
	case termSelect:
		if index := canonicalLinear(t.left, memo); index != t.left {
			out = &term{kind: termSelect, width: t.width, name: t.name, left: index}
		}
	case termCmp:
		left, right := canonicalLinear(t.left, memo), canonicalLinear(t.right, memo)
		if left.kind == termConst && right.kind == termConst {
			// Two constants compare at once (`0 lo 128`, a loop's entry
			// test over its literal bounds, which reaches here unfolded).
			out = cmpTerm(t.op, left, right)
			break
		}
		if (t.op == "eq" || t.op == "ne") && left.width == right.width {
			// The same term on both sides, structurally or in one linear
			// form: the Oak side's read-after-write at the index it wrote,
			// `(X eq X) ? written : entry`.
			same := equalTerms(left, right)
			if !same {
				if l, r := left.linearAt(left.width), right.linearAt(right.width); l != nil && r != nil && l.equal(r) {
					same = true
				}
			}
			if same {
				value := uint64(0)
				if t.op == "eq" {
					value = 1
				}
				out = constTerm(value, 1)
				break
			}
		}
		if left != t.left || right != t.right {
			out = cmpTerm(t.op, left, right)
		}
	case termBinary:
		if form := t.linearAt(t.width); form != nil {
			if spelled := form.spell(memo); spelled != nil {
				out = spelled
				break
			}
		}
		left, right := canonicalLinear(t.left, memo), canonicalLinear(t.right, memo)
		if (t.op == "and" || t.op == "xor") && left.kind == termConst && right.kind != termConst {
			left, right = right, left // the constant on the right, as the rules below read it
		}
		if t.op == "sub" && right.kind == termBinary && (right.op == "shl" || right.op == "mul") {
			// `x - ((x shr k) shl k)` and `x - ((x shr k) * 2^k)` are the
			// low k bits of x, `x and (2^k - 1)`: the machine's remainder
			// by a power of two against the Oak side's mask.
			inner, count := right.left, right.right
			if right.op == "mul" && inner.kind == termConst {
				inner, count = count, inner
			}
			k := int64(-1)
			if count.kind == termConst {
				if right.op == "shl" {
					k = int64(count.value)
				} else if count.value != 0 && count.value&(count.value-1) == 0 {
					k = int64(bits.TrailingZeros64(count.value))
				}
			}
			if k > 0 && k < int64(t.width) && inner.kind == termBinary && inner.op == "shr" && inner.right.kind == termConst && int64(inner.right.value) == k && equalTerms(inner.left, left) {
				out = binaryTerm("and", left, constTerm(uint64(1)<<uint(k)-1, t.width))
				break
			}
		}
		if t.op == "xor" && right.kind == termConst && right.value&mask(t.width) == 1 && t.width == 1 && left.kind == termIte {
			// A negated one-bit conditional negates its arms: `not (c ? X :
			// Y)` is `c ? not X : not Y`, the shape a path's facts split on.
			out = iteTerm(left.cond, binaryTerm("xor", truncate(left.left, 1), constTerm(1, 1)), binaryTerm("xor", truncate(left.right, 1), constTerm(1, 1)))
			break
		}
		if t.op == "xor" && right.kind == termConst {
			// Two constant xors in a row are one (`(x xor 1) xor 1` is x):
			// a machine Bool negated back on its path is the Bool.
			if left.kind == termBinary && left.op == "xor" && left.right.kind == termConst && left.width == t.width {
				c := (left.right.value ^ right.value) & mask(t.width)
				if c == 0 {
					out = left.left
				} else {
					out = &term{kind: termBinary, width: t.width, op: "xor", left: left.left, right: constTerm(c, t.width)}
				}
				break
			}
			if right.value&mask(t.width) == 0 {
				out = left
				break
			}
		}
		if t.op == "and" && right.kind == termConst && left.kind == termBinary && left.op == "or" {
			// A mask every bit of which an or-constant sets is the constant:
			// `((d or 2) or 1) and 1` is 1 — a descriptor's valid bit read
			// back from the value that set it.
			m := right.value & mask(t.width)
			set := uint64(0)
			for x := left; x.kind == termBinary && x.op == "or"; x = x.left {
				if x.right.kind == termConst {
					set |= x.right.value
				} else if x.left.kind == termConst {
					set |= x.left.value
					break
				}
			}
			if m != 0 && set&m == m {
				out = constTerm(m, t.width)
				break
			}
		}
		if t.op == "and" && right.kind == termConst {
			// A mask of low ones strips what lies above it from an or, a
			// shift, or a constant on the left (stripAbove): the machine's
			// read of a u16 call result, `(r and 65535) or (hi shl 16)`,
			// under `and 65535` is `r and 65535`.
			k := lowOnes(right.value & mask(t.width))
			if k > 0 {
				if kept := stripAbove(left, k); kept != nil {
					left = kept
				}
			}
			// A mask covering every bit the operand can have set, at the
			// operand's own width, is the identity (`1 and c` over a
			// comparison c, `(x and 65535) and 65535`).
			known := left.knownBits()
			if left.kind == termCmp {
				known = 1 // a comparison is one bit whatever width it is read at
			}
			if k > 0 && known <= k {
				if left.width == t.width {
					out = left
					break
				}
				if left.kind == termCmp {
					out = truncate(left, t.width)
					break
				}
			}
			// Two constant masks in a row are one mask, the intersection:
			// the machine's `(x and 0xFFFFFFFF) and 65535` (a 32-bit
			// register read wide, then a u16 narrowing) and the Oak side's
			// `(x and 65535) and 65535` are both `x and 65535`. The widths
			// may differ: a truncation is an and-mask at the narrower width
			// over the wider term, an extension the reverse (truncate,
			// zeroExtend), and each node's value is masked to its own
			// width, so the fold keeps the bits every mask and width keeps,
			// at the outer width, over the innermost operand.
			if left.kind == termBinary && left.op == "and" {
				inner, innerMask := left.left, left.right
				if innerMask.kind != termConst && inner.kind == termConst {
					inner, innerMask = innerMask, inner
				}
				if innerMask.kind == termConst {
					kept := innerMask.value & mask(left.width) & right.value & mask(t.width)
					out = &term{kind: termBinary, width: t.width, op: "and", left: inner, right: constTerm(kept, t.width)}
					if inner.width == t.width && kept == mask(t.width) {
						out = inner
					}
					break
				}
			}
			if left != t.left || right != t.right {
				out = &term{kind: termBinary, width: t.width, op: "and", left: left, right: constTerm(right.value&mask(t.width), t.width)}
			}
			break
		}
		if left != t.left || right != t.right {
			out = binaryTerm(t.op, left, right)
		}
	case termIte:
		cond, left, right := canonicalLinear(t.cond, memo), canonicalLinear(t.left, memo), canonicalLinear(t.right, memo)
		if cond != t.cond || left != t.left || right != t.right {
			out = iteTerm(cond, left, right)
		}
	}
	memo[t] = out
	return out
}

// spell writes a linear form out as one term: the constant, then each
// atom in name order scaled by its coefficient, the atoms respelled
// canonically and brought to the form's width. nil when an atom is
// missing (a form built without atoms).
func (f *linearForm) spell(memo map[*term]*term) *term {
	names := make([]string, 0, len(f.coeffs))
	for name := range f.coeffs {
		if f.atoms[name] == nil {
			return nil
		}
		names = append(names, name)
	}
	sort.Strings(names)
	out := constTerm(f.constant, f.width)
	for _, name := range names {
		atom := adaptWidth(canonicalLinear(f.atoms[name], memo), f.width)
		if c := f.coeffs[name]; c != 1 {
			if c&(c-1) == 0 {
				// A power of two is a shift, the spelling the mask rules
				// read: `(x and 65535) or (hi shl 16)` under `and 65535`
				// strips the register's unspecified upper half
				// (stripAbove), where `65536 mul hi` would hide it.
				atom = binaryTerm("shl", atom, constTerm(uint64(bits.TrailingZeros64(c)), f.width))
			} else {
				atom = binaryTerm("mul", constTerm(c, f.width), atom)
			}
		}
		out = binaryTerm("add", out, atom)
	}
	return out
}
