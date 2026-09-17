package asm

import "testing"

// The facts pruner reads a comparison of a two-constant conditional as a
// fact about its condition, and a zero test as a fact about the one-bit
// value it tests: the machine's `((c ? 1 : 0) eq 0)` and the Oak side's
// `((c ? 4 : 0) ne 0)` are `not c` and `c`, and `((d and 1) eq 0)` decides
// `(d and 1) xor 1`.
func TestFactsOfConstantConditionals(t *testing.T) {
	c := cmpTerm("ne", binaryTerm("and", paramTerm("va", 64), constTerm(16383, 64)), constTerm(0, 64))
	machine := cmpTerm("eq", iteTerm(c, constTerm(1, 32), constTerm(0, 32)), constTerm(0, 32))
	oak := cmpTerm("eq", iteTerm(c, constTerm(4, 8), constTerm(0, 8)), constTerm(0, 8))
	if got := pruneUnderFacts(machine, []*term{oak})[0]; got.kind != termConst || got.value != 1 {
		t.Fatalf("the Oak status test must be true under the machine's fact: %s", got)
	}
	if got := pruneUnderFacts(machine, []*term{c})[0]; got.kind != termConst || got.value != 0 {
		t.Fatalf("the condition itself is false under the fact: %s", got)
	}
	d := binaryTerm("and", selectTerm("s.pages", paramTerm("i", 32), 64), constTerm(1, 64))
	already := cmpTerm("eq", d, constTerm(0, 64))
	guard := binaryTerm("xor", truncate(d, 1), constTerm(1, 1))
	if got := pruneUnderFacts(already, []*term{guard})[0]; got.kind != termConst || got.value != 1 {
		t.Fatalf("(d and 1) xor 1 is true where (d and 1) eq 0: %s", got)
	}
}

// sourceTrapOnPath: a source trap whose conjuncts are all on the machine
// end's path holds, spelled with the machine's masks or the Oak side's; a
// path that refutes itself traps nowhere; a bound the path does not carry
// is not proven.
func TestSourceTrapOnPath(t *testing.T) {
	dom, va := paramTerm("dom", 32), paramTerm("va", 64)
	valid := cmpTerm("ne", binaryTerm("and", selectTerm("s.pages", dom, 64), constTerm(1, 64)), constTerm(0, 64))
	notValid := cmpTerm("eq", iteTerm(valid, constTerm(1, 32), constTerm(0, 32)), constTerm(0, 32))
	leaf := binaryTerm("shr", binaryTerm("sub", selectTerm("s.pages", dom, 64), paramTerm("base", 64)), constTerm(14, 64))
	machineBound := cmpTerm("hs", &term{kind: termBinary, width: 32, op: "and", left: truncate(leaf, 32), right: constTerm(65535, 32)}, constTerm(4, 32))
	oakBound := cmpTerm("hs", zeroExtend(&term{kind: termBinary, width: 16, op: "and", left: leaf, right: constTerm(65535, 16)}, 32), constTerm(4, 32))
	path := binaryTerm("and", binaryTerm("and", notValid, cmpTerm("lo", va, constTerm(1<<32, 64))), machineBound)
	oakTrap := binaryTerm("or", cmpTerm("hs", dom, paramTerm("len(s)", 32)), binaryTerm("and", binaryTerm("xor", truncate(valid, 1), constTerm(1, 1)), oakBound))
	if !sourceTrapOnPath(path, oakTrap) {
		t.Fatal("the leaf bound with its guard is on the path once the masks are respelled")
	}
	unrelated := binaryTerm("or", cmpTerm("hs", dom, paramTerm("len(s)", 32)), cmpTerm("hs", paramTerm("k", 32), constTerm(4, 32)))
	if sourceTrapOnPath(path, unrelated) {
		t.Fatal("a bound the path does not carry is not proven")
	}
	contradictory := binaryTerm("and", path, valid)
	if !sourceTrapOnPath(contradictory, unrelated) {
		t.Fatal("a path asserting a fact and its complement is vacuous")
	}
}

// sameUnderFacts: a call summary's conditional result under the premise
// that holds its branch is the Oak side's plain value.
func TestSameUnderFacts(t *testing.T) {
	fc := selectTerm("s.free_count", paramTerm("dom", 32), 16)
	nonEmpty := cmpTerm("ne", fc, constTerm(0, 16))
	stack := selectTerm("s.free_stack", binaryTerm("add", binaryTerm("shl", paramTerm("dom", 32), constTerm(2, 32)), binaryTerm("add", constTerm(0xFFFFFFFF, 32), zeroExtend(fc, 32))), 16)
	oak := zeroExtend(stack, 32)
	machine := binaryTerm("and", binaryTerm("or", iteTerm(nonEmpty, zeroExtend(stack, 32), constTerm(0, 32)), binaryTerm("shl", paramTerm("call1#hi", 32), constTerm(16, 32))), constTerm(65535, 32))
	if !sameUnderFacts(nonEmpty, oak, machine) {
		t.Fatal("the summary's result is the stack element where the stack is not empty")
	}
	if sameUnderFacts(cmpTerm("eq", fc, constTerm(0, 16)), oak, machine) {
		t.Fatal("where the stack is empty the summary's result is zero, not the element")
	}
}
