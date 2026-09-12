package asm

import "github.com/SCKelemen/oak/ast"

// Problem is a theorem's bit-level decision serialized for the Oak solver
// (prove/solver/bdd.oak): a word table with an 8-word header (terms,
// leaves, roots, budget, select slots), the leaves — the parameter bits in
// the variable order chosen, 65 words each: the declared width and the
// variable of each of 64 bits — the terms in dependency order, 8 words
// each (kind, op, width, a, b, c, value low, value high), the roots (the
// trap obligations first, the claim last), and the select slots'
// variables. The Oak solver blasts the same terms under the same order as
// the Go decider did, so the two agree on the verdict and on the node
// count, or one of them is wrong.
type Problem struct {
	Words  []uint32
	Order  string // interleaved, blocks, or control: the variable order serialized
	Terms  int
	Leaves int
	// Owners maps a variable index back to its parameter bit, so an
	// assignment the Oak solver reports (the variables set on a path to a
	// failing root) reads as a counterexample over the parameters.
	Owners map[uint32]VariableOwner
	names  []string
}

// VariableOwner is the parameter bit a diagram variable stands for.
type VariableOwner struct {
	Param string
	Bit   int
}

// Counterexample renders the variables set on a failing path as the
// parameter assignment the decider would print (every unset bit zero).
func (p Problem) Counterexample(setVars []uint32) string {
	env := map[string]uint64{}
	for _, v := range setVars {
		if owner, isParam := p.Owners[v]; isParam {
			env[owner.Param] |= uint64(1) << uint(owner.Bit)
		}
	}
	return describeEnv(p.names, env)
}

// ExportProblems serializes the theorem under every variable order that
// applies to it (interleaved first), for the Oak solver to race. The
// witness pass is the caller's (WitnessRefutation); the reason names what
// keeps the theorem from the bit level.
func ExportProblems(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, guards map[string]Guard, decls Declarations, budget int) ([]Problem, string, bool) {
	lowered, undecided := lowerTheorem(sig, functions, guards, decls)
	if undecided != nil {
		return nil, undecided.Message, false
	}
	var problems []Problem
	for _, bl := range lowered.blasters() {
		problems = append(problems, serializeProblem(bl, lowered.claim, lowered.traps, budget, orderNames[bl.label]))
	}
	return problems, "", true
}

const problemSelectSlots = 16

const problemNone = ^uint32(0)

// Term kinds and operators as the Oak solver numbers them.
var problemBinaryOps = map[string]uint32{
	"and": 0, "or": 1, "xor": 2, "add": 3, "sub": 4, "shl": 5, "shr": 6, "sar": 7,
	"mul": 8, "ror": 9, "rev": 10, "rev16": 11, "rev32": 12, "rbit": 13, "clz": 14, "cnt": 15, "cls": 16,
}

var problemConditionCodes = map[string]uint32{
	"eq": 0, "ne": 1, "hs": 2, "cs": 2, "lo": 3, "cc": 3, "mi": 4, "pl": 5, "vs": 6, "vc": 7,
	"hi": 8, "ls": 9, "ge": 10, "lt": 11, "gt": 12, "le": 13,
}

var problemFlagKinds = map[string]uint32{"": 0, "add": 1, "and": 2}

// orderNames maps a blaster's label to the order name a Problem carries.
var orderNames = map[string]string{"": "interleaved", "parameters in blocks": "blocks", "control bits first": "control"}

// ExportProblem lowers the theorem exactly as DecideTheoremWith does and
// serializes its claim and trap obligations under the named variable
// order (interleaved by default). The reason names what kept the theorem
// from the bit level.
func ExportProblem(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, guards map[string]Guard, decls Declarations, order string, budget int) (Problem, string, bool) {
	lowered, undecided := lowerTheorem(sig, functions, guards, decls)
	if undecided != nil {
		return Problem{}, undecided.Message, false
	}
	var bl *blaster
	switch order {
	case "blocks":
		bl = newGroupedBlaster(lowered.names, lowered.widths)
	case "control":
		control := controlParams(append([]*term{lowered.claim}, lowered.traps...))
		bl = newControlFirstBlaster(lowered.names, lowered.widths, control)
	default:
		order = "interleaved"
		bl = newBlaster(lowered.names, lowered.widths)
	}
	return serializeProblem(bl, lowered.claim, lowered.traps, budget, order), "", true
}

func serializeProblem(bl *blaster, claim *term, traps []*term, budget int, order string) Problem {
	leafIndex := map[string]int{}
	for i, name := range bl.params {
		leafIndex[name] = i
	}
	// Terms in dependency order: every operand before the term that reads
	// it, each shared subterm once (the terms are DAGs).
	var terms []*term
	index := map[*term]int{}
	var number func(t *term)
	number = func(t *term) {
		if t == nil {
			return
		}
		if _, done := index[t]; done {
			return
		}
		number(t.cond)
		number(t.left)
		number(t.right)
		index[t] = len(terms)
		terms = append(terms, t)
	}
	for _, trap := range traps {
		number(trap)
	}
	number(claim)

	words := make([]uint32, 0, 8+len(bl.params)*65+len(terms)*8+len(traps)+1+problemSelectSlots*64)
	words = append(words, uint32(len(terms)), uint32(len(bl.params)), uint32(len(traps)+1), uint32(budget), problemSelectSlots, 0, 0, 0)
	for _, name := range bl.params {
		width := bl.widths[name]
		words = append(words, uint32(width))
		for bit := 0; bit < 64; bit++ {
			if bit < width {
				words = append(words, uint32(bl.variableIndex(name, bit)))
			} else {
				words = append(words, problemNone)
			}
		}
	}
	spans := map[string]uint32{}
	operand := func(t *term) uint32 {
		if t == nil {
			return problemNone
		}
		return uint32(index[t])
	}
	for _, t := range terms {
		var kind, op uint32
		a, b, c := problemNone, problemNone, problemNone
		var vlo, vhi uint32
		switch t.kind {
		case termParam:
			kind = 0
			a = uint32(leafIndex[t.name])
		case termConst:
			kind = 1
			vlo, vhi = uint32(t.value), uint32(t.value>>32)
		case termBinary:
			kind = 2
			code, known := problemBinaryOps[t.op]
			if !known {
				code = problemNone // outside the solver's subset: it reports unsupported
			}
			op = code
			a, b = operand(t.left), operand(t.right)
		case termCmp:
			kind = 3
			flags, bare := splitFlagsKind(t.op)
			op = problemFlagKinds[flags]*16 + problemConditionCodes[bare]
			a, b = operand(t.left), operand(t.right)
		case termIte:
			kind = 4
			c, a, b = operand(t.cond), operand(t.left), operand(t.right)
		case termSelect:
			kind = 5
			id, seen := spans[t.name]
			if !seen {
				id = uint32(len(spans))
				spans[t.name] = id
			}
			op = id
			a = operand(t.left)
		}
		words = append(words, kind, op, uint32(t.width), a, b, c, vlo, vhi)
	}
	for _, trap := range traps {
		words = append(words, uint32(index[trap]))
	}
	words = append(words, uint32(index[claim]))
	for slot := 0; slot < problemSelectSlots; slot++ {
		for bit := 0; bit < 64; bit++ {
			words = append(words, uint32(bl.selectVariable(slot, bit)))
		}
	}
	owners := make(map[uint32]VariableOwner, len(bl.owners))
	for v, owner := range bl.owners {
		owners[uint32(v)] = VariableOwner{Param: owner.param, Bit: owner.bit}
	}
	return Problem{Words: words, Order: order, Terms: len(terms), Leaves: len(bl.params), Owners: owners, names: bl.params}
}
