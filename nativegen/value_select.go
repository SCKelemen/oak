package nativegen

import (
	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// Value-position select forms (docs/spec/94-assembler.md §9 "Select
// forms"). A conditional in value position lowered to a branch over two
// moves:
//
//	pick: (a: u32, b: u32): u32 = a < b ? b | a
//
//	cmp w0, w1 ; b.hs else_4 ; mov w0, w1 ; b endif_5 ; else_4: ; endif_5:
//
// where AArch64 selects between two registers on the flags in one
// instruction:
//
//	cmp w0, w1 ; csel w0, w1, w0, lo
//
// Five instructions and two labels become two instructions and none. The
// branch is the point: a value conditional inside a loop body split the
// body into blocks, which the loop shape the verifier recognizes has to
// step around, and gave the predictor something to learn about data.
//
// Three arms are one instruction on their own, when both arms share an
// operand the machine can transform in the select itself:
//
//	c ? x + u32(1) | x   csinc  (cond ? Rn : Rm + 1)
//	c ? T(0) - x   | x   csneg  (cond ? Rn : -Rm)
//	c ? ^x         | x   csinv  (cond ? Rn : ~Rm)
//
// Each is spelled with the condition inverted, since the machine applies
// its increment, negation, or complement to the *false* operand. The
// verifier models all four (asm/isa_semantics.go), so the bodies are
// judged with no extension.
//
// Both arms are evaluated before the compare, as the statement form's
// if-conversion does (nativegen/select.go): the select has no untaken
// path, so an arm that reads memory through a guard, calls, or divides
// would run where the source never ran it. `speculable` decides, and the
// arms of an integer comparison are the only conditions taken — a float
// comparison sets the flags the same way, but its unordered case belongs
// with the branch form that already handles it.

// valueSelect is a recognized value-position select: the mnemonic, the
// comparison whose flags decide, and the operands to select between. For
// the csinc/csneg/csinv forms both operands are the shared one.
type valueSelect struct {
	mnemonic string
	compare  *ast.InfixExpression
	// whenTrue and whenFalse are the arms as the select reads them: for
	// csel the two arms, for the transforming forms the shared operand
	// twice. inverted spells the condition the other way round, which the
	// transforming forms need.
	whenTrue, whenFalse ast.Expression
	inverted            bool
}

// sharedSelectOperand recognizes `c ? f(x) | x` where f is one of the
// machine's own select transforms and x is a variable, and reports the
// mnemonic. A variable is the whole of it: the operand is read twice, and
// reading a larger expression twice is what the general csel already
// does once.
func sharedSelectOperand(whenTrue, whenFalse ast.Expression) (string, bool) {
	base, isIdent := whenFalse.(*ast.Identifier)
	if !isIdent {
		return "", false
	}
	same := func(e ast.Expression) bool {
		other, isIdent := e.(*ast.Identifier)
		return isIdent && other.Value == base.Value
	}
	switch arm := whenTrue.(type) {
	case *ast.PrefixExpression:
		// `^x`: the complement.
		if arm.Operator == "^" && same(arm.Right) {
			return "csinv", true
		}
	case *ast.InfixExpression:
		switch arm.Operator {
		case "+":
			// `x + 1` either way round.
			if same(arm.Left) && isOneLiteral(arm.Right) {
				return "csinc", true
			}
			if same(arm.Right) && isOneLiteral(arm.Left) {
				return "csinc", true
			}
		case "-":
			// `0 - x`: the negation.
			if value, isConst := constantValue(arm.Left); isConst && value == 0 && same(arm.Right) {
				return "csneg", true
			}
		}
	}
	return "", false
}

// isOneLiteral reports the constant one, bare or converted (`u32(1)`).
func isOneLiteral(e ast.Expression) bool {
	value, isConst := constantValue(e)
	return isConst && value == 1
}

// recognizeValueSelect reads a select form out of a value-position
// conditional, or reports that the branch form stands.
func (g *generator) recognizeValueSelect(e *ast.MatchExpression, typ scalar) (valueSelect, bool) {
	if typ.isFloat || typ.isVec || typ.bits > 64 {
		return valueSelect{}, false
	}
	whenTrue, whenFalse, isBool := boolConditional(e)
	if !isBool {
		return valueSelect{}, false
	}
	compare, isInfix := e.Scrutinee.(*ast.InfixExpression)
	if !isInfix {
		return valueSelect{}, false
	}
	if _, isComparison := conditionCodes[compare.Operator]; !isComparison {
		return valueSelect{}, false
	}
	operand, err := g.operandType(compare)
	if err != nil || operand.isFloat || operand.isVec {
		return valueSelect{}, false
	}
	// The transforming forms read one variable and let the machine do the
	// increment, negation, or complement, so there is nothing to
	// speculate beyond reading that variable — `^x` is not a speculable
	// expression to the general form, which would have to evaluate it.
	if mnemonic, isShared := sharedSelectOperand(whenTrue, whenFalse); isShared && g.speculable(whenFalse) {
		return valueSelect{mnemonic: mnemonic, compare: compare, whenTrue: whenFalse, whenFalse: whenFalse, inverted: true}, true
	}
	if !g.speculable(whenTrue) || !g.speculable(whenFalse) {
		return valueSelect{}, false
	}
	return valueSelect{mnemonic: "csel", compare: compare, whenTrue: whenTrue, whenFalse: whenFalse}, true
}

// valueSelectForm lowers a recognized select form and reports whether it
// did; nothing is emitted when it did not.
func (g *generator) valueSelectForm(e *ast.MatchExpression, typ scalar) (int, bool, error) {
	form, isSelect := g.recognizeValueSelect(e, typ)
	if !isSelect {
		return 0, false, nil
	}
	// The arms first, since the compare's flags must reach the select with
	// nothing between them.
	t, tfixed, err := g.operand(form.whenTrue, typ)
	if err != nil {
		return 0, false, err
	}
	f, ffixed := t, tfixed
	if form.whenFalse != form.whenTrue {
		if f, ffixed, err = g.operand(form.whenFalse, typ); err != nil {
			return 0, false, err
		}
	}
	operand, err := g.operandType(form.compare)
	if err != nil {
		return 0, false, err
	}
	l, lfixed, err := g.operand(form.compare.Left, operand)
	if err != nil {
		return 0, false, err
	}
	right, r, rfixed, err := g.sourceOperand(form.compare.Right, operand, "cmp")
	if err != nil {
		return 0, false, err
	}
	g.emit("cmp", reg(l, operand), right)
	if r >= 0 && !rfixed {
		g.release(r)
	}
	if !lfixed {
		g.release(l)
	}
	code := conditionCodes[form.compare.Operator][0]
	if operand.signed {
		code = conditionCodes[form.compare.Operator][1]
	}
	if form.inverted {
		code = inverseCondition[code]
	}
	out, err := g.alloc(typ)
	if err != nil {
		return 0, false, err
	}
	g.emit(form.mnemonic, reg(out, typ), reg(t, typ), reg(f, typ), asm.Condition{Code: code})
	if !tfixed {
		g.release(t)
	}
	if !ffixed && f != t {
		g.release(f)
	}
	// csinc, csneg, and csinv compute in the register's width; a narrow
	// type takes its mask after.
	g.normalize(out, typ)
	g.valueSelects++
	return out, true, nil
}

// ValueSelects reports how many value-position select forms a lowering
// emitted under Lane.ValueSelect.
func ValueSelects(fn *asm.Function) int { return valueSelects[fn] }

var valueSelects = map[*asm.Function]int{}
