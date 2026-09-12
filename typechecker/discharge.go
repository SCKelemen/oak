package typechecker

import (
	"github.com/SCKelemen/oak/ast"
)

// Static discharge of a refinement's construction (docs/spec/20-types.md
// section 12, "Static discharge"). A construction `Name(e)` is emitted
// without its guard when the facts in scope prove the predicate of e —
// never by assumption, only by a law the extent facts already carry
// (Oak.Extents) or by evaluation. The predicate is read by shape:
//
//   - a constant argument: the predicate is evaluated at the base width;
//   - an argument already of a refinement with the same predicate;
//   - `a && b`: both discharged; `a || b`: either;
//   - `value < K`, `value <= K` (either order): the argument is proven
//     below the bound by the index laws;
//   - `value >= K`, `value > K` (either order): a live literal lower
//     bound on the binding, or a constant;
//   - `value % K == 0` with K a power of two: the argument's low bits are
//     zero by construction — a product or mask with a multiple of K, a
//     shift by at least log2 K, a sum, difference, or bitwise combination
//     of such terms, or a conversion of one. Wrapping arithmetic keeps a
//     power-of-two divisor's low bits, which is why K must be one.
//
// Anything else keeps its guard: a check that stays is a runtime check,
// never a silent assumption.

// dischargePredicate decides whether the live facts prove
// predicate[value := arg].
func (tc *TypeChecker) dischargePredicate(predicate, arg ast.Expression, argType Type, base string) bool {
	if constant, isConst := constantIndex(arg); isConst {
		if holds, ok := foldPredicate(predicate, constant, base); ok {
			return holds
		}
	}
	if prim, isPrim := argType.(*PrimitiveType); isPrim && prim.Refinement != "" {
		if info, ok := tc.refinements[prim.Refinement]; ok && info.predicate.String() == predicate.String() {
			return true
		}
	}
	infix, isInfix := predicate.(*ast.InfixExpression)
	if !isInfix {
		return false
	}
	switch infix.Operator {
	case "&&":
		return tc.dischargePredicate(infix.Left, arg, argType, base) && tc.dischargePredicate(infix.Right, arg, argType, base)
	case "||":
		return tc.dischargePredicate(infix.Left, arg, argType, base) || tc.dischargePredicate(infix.Right, arg, argType, base)
	}
	if bound, ok := upperBoundOf(infix); ok {
		return tc.provenBelow(arg, bound)
	}
	if bound, ok := lowerBoundOf(infix); ok {
		return tc.provenAtLeast(arg, bound, isSignedName(base))
	}
	if k, ok := divisibilityOf(infix); ok {
		return tc.provenDivisible(arg, k)
	}
	return false
}

// upperBoundOf reads `value < K`, `value <= K`, `K > value`, `K >= value`
// with a literal K as the exclusive bound.
func upperBoundOf(infix *ast.InfixExpression) (int64, bool) {
	if isValue(infix.Left) {
		k, isConst := constantIndex(infix.Right)
		if !isConst || k < 0 {
			return 0, false
		}
		switch infix.Operator {
		case "<":
			return k, true
		case "<=":
			return k + 1, true
		}
	}
	if isValue(infix.Right) {
		k, isConst := constantIndex(infix.Left)
		if !isConst || k < 0 {
			return 0, false
		}
		switch infix.Operator {
		case ">":
			return k, true
		case ">=":
			return k + 1, true
		}
	}
	return 0, false
}

// lowerBoundOf reads `value >= K`, `value > K`, `K <= value`, `K < value`
// with a literal K as the inclusive bound.
func lowerBoundOf(infix *ast.InfixExpression) (int64, bool) {
	if isValue(infix.Left) {
		k, isConst := constantIndex(infix.Right)
		if !isConst {
			return 0, false
		}
		switch infix.Operator {
		case ">=":
			return k, true
		case ">":
			return k + 1, true
		}
	}
	if isValue(infix.Right) {
		k, isConst := constantIndex(infix.Left)
		if !isConst {
			return 0, false
		}
		switch infix.Operator {
		case "<=":
			return k, true
		case "<":
			return k + 1, true
		}
	}
	return 0, false
}

// divisibilityOf reads `value % K == 0` (or `0 == value % K`) with a
// literal K > 0.
func divisibilityOf(infix *ast.InfixExpression) (int64, bool) {
	if infix.Operator != "==" {
		return 0, false
	}
	remainder := func(expr ast.Expression) (int64, bool) {
		inner, isInfix := expr.(*ast.InfixExpression)
		if !isInfix || inner.Operator != "%" || !isValue(inner.Left) {
			return 0, false
		}
		k, isConst := constantIndex(inner.Right)
		if !isConst || k <= 0 {
			return 0, false
		}
		return k, true
	}
	if zero, isConst := constantIndex(infix.Right); isConst && zero == 0 {
		if k, ok := remainder(infix.Left); ok {
			return k, true
		}
	}
	if zero, isConst := constantIndex(infix.Left); isConst && zero == 0 {
		if k, ok := remainder(infix.Right); ok {
			return k, true
		}
	}
	return 0, false
}

func isValue(expr ast.Expression) bool {
	ident, isIdent := expr.(*ast.Identifier)
	return isIdent && ident.Value == "value"
}

func isSignedName(name string) bool {
	return len(name) > 0 && name[0] == 'i'
}

// provenAtLeast decides whether the live facts prove arg >= bound: a
// constant, a local binding with a literal lower bound in scope, or, for
// an unsigned base, a bound at or below zero.
func (tc *TypeChecker) provenAtLeast(arg ast.Expression, bound int64, signed bool) bool {
	if bound <= 0 && !signed {
		return true
	}
	if constant, isConst := constantIndex(arg); isConst {
		return constant >= bound
	}
	binding, isPath := pathOf(arg)
	if !isPath || !tc.localBinding(binding) {
		return false
	}
	for _, fact := range tc.extentFacts {
		if !fact.dead && fact.kind == factLowerLit && fact.other == binding && fact.bound >= bound {
			return true
		}
	}
	return false
}

// provenDivisible decides whether arg's low bits are zero modulo k, a
// power of two, by the shape of the expression.
func (tc *TypeChecker) provenDivisible(arg ast.Expression, k int64) bool {
	if k <= 0 || k&(k-1) != 0 {
		return false
	}
	if constant, isConst := constantIndex(arg); isConst {
		return constant%k == 0
	}
	multipleOf := func(expr ast.Expression) bool {
		c, isConst := constantIndex(expr)
		return isConst && c%k == 0
	}
	switch e := arg.(type) {
	case *ast.InfixExpression:
		switch e.Operator {
		case "*", "&":
			return multipleOf(e.Left) || multipleOf(e.Right) || tc.provenDivisible(e.Left, k) || tc.provenDivisible(e.Right, k)
		case "<<":
			shift, isConst := constantIndex(e.Right)
			if isConst && shift >= 0 && shift < 63 && (int64(1)<<uint(shift))%k == 0 {
				return true
			}
			return tc.provenDivisible(e.Left, k)
		case "+", "-", "|", "^":
			return tc.provenDivisible(e.Left, k) && tc.provenDivisible(e.Right, k)
		}
	case *ast.InvocationExpression:
		// A conversion keeps the low bits, whichever way it goes.
		if fn, isIdent := e.Function.(*ast.Identifier); isIdent && len(e.Arguments) == 1 {
			if _, isConversion := conversionPrimitives[fn.Value]; isConversion && !IsFloatName(fn.Value) {
				return tc.provenDivisible(e.Arguments[0], k)
			}
		}
	}
	return false
}

// foldPredicate evaluates a predicate at a constant value of the base
// type, with the base's wrapping arithmetic. ok is false for a shape the
// folder does not cover or an operation that would trap.
func foldPredicate(predicate ast.Expression, value int64, base string) (holds bool, ok bool) {
	width, known := conversionPrimitives[base]
	if !known || IsFloatName(base) {
		return false, false
	}
	f := &folder{value: value, width: uint(width), signed: isSignedName(base)}
	return f.boolean(predicate)
}

type folder struct {
	value  int64
	width  uint
	signed bool
}

func (f *folder) wrap(v uint64) uint64 {
	if f.width >= 64 {
		return v
	}
	return v & (uint64(1)<<f.width - 1)
}

// signedOf reads wrapped bits as the base's signed value.
func (f *folder) signedOf(v uint64) int64 {
	if f.width >= 64 {
		return int64(v)
	}
	shift := 64 - f.width
	return int64(v<<shift) >> shift
}

func (f *folder) less(a, b uint64) bool {
	if f.signed {
		return f.signedOf(a) < f.signedOf(b)
	}
	return a < b
}

func (f *folder) integer(expr ast.Expression) (uint64, bool) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		if e.Wide {
			return 0, false
		}
		return f.wrap(uint64(e.Value)), true
	case *ast.Identifier:
		if e.Value == "value" {
			return f.wrap(uint64(f.value)), true
		}
	case *ast.InvocationExpression:
		fn, isIdent := e.Function.(*ast.Identifier)
		if !isIdent || len(e.Arguments) != 1 {
			return 0, false
		}
		if _, isConversion := conversionPrimitives[fn.Value]; !isConversion || IsFloatName(fn.Value) {
			return 0, false
		}
		return f.integer(e.Arguments[0])
	case *ast.PrefixExpression:
		if e.Operator != "-" {
			return 0, false
		}
		v, ok := f.integer(e.Right)
		if !ok {
			return 0, false
		}
		return f.wrap(-v), true
	case *ast.InfixExpression:
		a, okA := f.integer(e.Left)
		b, okB := f.integer(e.Right)
		if !okA || !okB {
			return 0, false
		}
		switch e.Operator {
		case "+":
			return f.wrap(a + b), true
		case "-":
			return f.wrap(a - b), true
		case "*":
			return f.wrap(a * b), true
		case "&":
			return a & b, true
		case "|":
			return a | b, true
		case "^":
			return a ^ b, true
		case "/", "%":
			if b == 0 {
				return 0, false
			}
			if f.signed {
				x, y := f.signedOf(a), f.signedOf(b)
				if y == -1 && x == f.signedOf(f.wrap(uint64(1)<<(f.width-1))) {
					return 0, false // the overflowing quotient traps
				}
				if e.Operator == "/" {
					return f.wrap(uint64(x / y)), true
				}
				return f.wrap(uint64(x % y)), true
			}
			if e.Operator == "/" {
				return a / b, true
			}
			return a % b, true
		case "<<", ">>":
			if b >= uint64(f.width) {
				return 0, false // out-of-range shifts trap
			}
			if e.Operator == "<<" {
				return f.wrap(a << b), true
			}
			if f.signed {
				return f.wrap(uint64(f.signedOf(a) >> b)), true
			}
			return a >> b, true
		}
	}
	return 0, false
}

func (f *folder) boolean(expr ast.Expression) (bool, bool) {
	switch e := expr.(type) {
	case *ast.Boolean:
		return e.Value, true
	case *ast.PrefixExpression:
		if e.Operator != "!" {
			return false, false
		}
		v, ok := f.boolean(e.Right)
		return !v, ok
	case *ast.InfixExpression:
		switch e.Operator {
		case "&&", "||":
			a, okA := f.boolean(e.Left)
			b, okB := f.boolean(e.Right)
			if !okA || !okB {
				return false, false
			}
			if e.Operator == "&&" {
				return a && b, true
			}
			return a || b, true
		case "<", "<=", ">", ">=", "==", "!=":
			a, okA := f.integer(e.Left)
			b, okB := f.integer(e.Right)
			if !okA || !okB {
				if e.Operator != "==" && e.Operator != "!=" {
					return false, false
				}
				p, okP := f.boolean(e.Left)
				q, okQ := f.boolean(e.Right)
				if !okP || !okQ {
					return false, false
				}
				return (p == q) == (e.Operator == "=="), true
			}
			switch e.Operator {
			case "<":
				return f.less(a, b), true
			case "<=":
				return !f.less(b, a), true
			case ">":
				return f.less(b, a), true
			case ">=":
				return !f.less(a, b), true
			case "==":
				return a == b, true
			default:
				return a != b, true
			}
		}
	}
	return false, false
}
