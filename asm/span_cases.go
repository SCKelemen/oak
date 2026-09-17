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
func spanEqualByCases(fn string, name string, premise, oak, machine *term) (equal, decided bool) {
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
		memo := map[*term]*term{}
		a := canonicalLinear(canonicalMemo(pruned[0], cmemo, cbool), memo)
		b := canonicalLinear(canonicalMemo(pruned[1], cmemo, cbool), memo)
		if !equalTerms(a, b) {
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
		// Two constant masks in a row are one mask, the intersection: the
		// machine's `(x and 0xFFFFFFFF) and 65535` (a 32-bit register read
		// wide, then a u16 narrowing) and the Oak side's `(x and 65535) and
		// 65535` are both `x and 65535`.
		// The widths may differ: a truncation is an and-mask at the
		// narrower width over the wider term, an extension the reverse
		// (truncate, zeroExtend), and each node's value is masked to its
		// own width, so the fold keeps the bits every mask and width
		// keeps, at the outer width, over the innermost operand.
		if t.op == "and" && right.kind == termConst && left.kind == termBinary && left.op == "and" && left.right.kind == termConst {
			kept := left.right.value & mask(left.width) & right.value & mask(t.width)
			out = &term{kind: termBinary, width: t.width, op: "and", left: left.left, right: constTerm(kept, t.width)}
			if left.left.width == t.width && kept == mask(t.width) {
				out = left.left
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
			atom = binaryTerm("mul", constTerm(c, f.width), atom)
		}
		out = binaryTerm("add", out, atom)
	}
	return out
}
