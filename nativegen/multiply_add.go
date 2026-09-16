package nativegen

import (
	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// Multiply-add forms (docs/spec/94-assembler.md §9 "Multiply-add forms").
// AArch64 computes a product and an addend in one instruction, so the
// integer expressions
//
//	a + b * c    b * c + a    a - b * c    u32(0) - b * c
//
// are `madd dD, dB, dC, dA`, `msub dD, dB, dC, dA`, and `mneg dD, dB, dC`
// where the lowering emitted a `mul` and an `add`, a `sub`, or a zero and
// a `sub`. Every dot-product-shaped loop pays one instruction less an
// element (`acc = acc + x[i] * y[i]`).
//
// Integers only. Oak's `a + b * c` over floats is two roundings, the
// multiplication's and the addition's (`20-types.md` §11.3.3, and the C
// backend's `-ffp-contract=off`), where `fmla` is one: the fused form is
// a different function and is reached only by `simd.fma`.
//
// A product whose operand is a constant is left alone: the strength
// reduction lowers `b * 4` to a shift, and a shift and an add are two
// instructions where materializing the constant for a `madd` would be
// three.

// multiplyAdd is a recognized fused form: the product's operands, the
// addend (nil for `mneg`), and the mnemonic. productFirst records which
// side of the expression the product was, so the lowering evaluates the
// operands in the order the source writes them — `a + f() * g()` calls
// nothing before reading a, and `f() * g() + a` calls both before it.
type multiplyAdd struct {
	mnemonic     string
	left         ast.Expression // the product's left operand
	right        ast.Expression // the product's right operand
	addend       ast.Expression // the term added or subtracted; nil for mneg
	productFirst bool           // the product was the expression's left side
}

// recognizeMultiplyAdd reads a fused form out of `+` or `-` over an
// integer type.
func recognizeMultiplyAdd(e *ast.InfixExpression, typ scalar) (multiplyAdd, bool) {
	if typ.isFloat || typ.isVec || typ.isBool || typ.bits > 64 {
		return multiplyAdd{}, false
	}
	product := func(x ast.Expression) (*ast.InfixExpression, bool) {
		inner, isInfix := x.(*ast.InfixExpression)
		if !isInfix || inner.Operator != "*" {
			return nil, false
		}
		// A constant operand belongs to the strength reduction's shift.
		if _, isConst := constantValue(inner.Left); isConst {
			return nil, false
		}
		if _, isConst := constantValue(inner.Right); isConst {
			return nil, false
		}
		return inner, true
	}
	switch e.Operator {
	case "+":
		if inner, isProduct := product(e.Right); isProduct {
			return multiplyAdd{mnemonic: "madd", left: inner.Left, right: inner.Right, addend: e.Left}, true
		}
		if inner, isProduct := product(e.Left); isProduct {
			return multiplyAdd{mnemonic: "madd", left: inner.Left, right: inner.Right, addend: e.Right, productFirst: true}, true
		}
	case "-":
		inner, isProduct := product(e.Right)
		if !isProduct {
			return multiplyAdd{}, false
		}
		// `0 - b * c` is the negated product; anything else subtracts it.
		if zero, isConst := constantValue(e.Left); isConst && zero == 0 {
			return multiplyAdd{mnemonic: "mneg", left: inner.Left, right: inner.Right, productFirst: true}, true
		}
		return multiplyAdd{mnemonic: "msub", left: inner.Left, right: inner.Right, addend: e.Left}, true
	}
	return multiplyAdd{}, false
}

// multiplyAddForm lowers a recognized fused form and reports whether it
// did; nothing is emitted when it did not.
func (g *generator) multiplyAddForm(e *ast.InfixExpression, typ scalar) (int, bool, error) {
	form, isFused := recognizeMultiplyAdd(e, typ)
	if !isFused {
		return 0, false, nil
	}
	// Source order: the addend first when the source wrote it first, so
	// a call in one operand still runs when it ran before. The product's
	// left operand is read where it lies, and the result lands in its
	// scratch register, or a fresh one when it is a variable's home.
	a, b, c, bfixed := -1, 0, 0, false
	var err error
	if form.addend != nil && !form.productFirst {
		if a, err = g.expr(form.addend, &typ); err != nil {
			return 0, false, err
		}
	}
	if b, bfixed, err = g.operand(form.left, typ); err != nil {
		return 0, false, err
	}
	if c, err = g.expr(form.right, &typ); err != nil {
		return 0, false, err
	}
	if form.addend != nil && form.productFirst {
		if a, err = g.expr(form.addend, &typ); err != nil {
			return 0, false, err
		}
	}
	out := b
	if bfixed {
		if out, err = g.alloc(typ); err != nil {
			return 0, false, err
		}
	}
	if form.addend != nil {
		g.emit(form.mnemonic, reg(out, typ), reg(b, typ), reg(c, typ), reg(a, typ))
		g.release(a)
	} else {
		g.emit(form.mnemonic, reg(out, typ), reg(b, typ), reg(c, typ))
	}
	g.release(c)
	g.normalize(out, typ)
	g.fusedMultiplies++
	return out, true, nil
}

// FusedMultiplies reports how many multiply-add forms a lowering emitted
// under Lane.MultiplyAdd.
func FusedMultiplies(fn *asm.Function) int { return fusedMultiplies[fn] }

var fusedMultiplies = map[*asm.Function]int{}
