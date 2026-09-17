package nativegen

import "github.com/SCKelemen/oak/ast"

// extentQuotient folds a quotient/remainder of an exact local view length.
// This is deliberately not a general constant evaluator: it cannot erase a
// call, a checked conversion, or construction/checking of a derived span.
// The view declaration has already evaluated its address. Native span locals
// cannot be rebound; scope restoration restores their metadata as well.
func (g *generator) extentQuotient(e *ast.InfixExpression, typ scalar) (uint64, bool) {
	if !g.strength || typ != scalars["u32"] || (e.Operator != "/" && e.Operator != "%") {
		return 0, false
	}
	call, ok := e.Left.(*ast.InvocationExpression)
	if !ok || len(call.Arguments) != 1 {
		return 0, false
	}
	fn, ok := call.Function.(*ast.Identifier)
	if !ok || fn.Value != "len" {
		return 0, false
	}
	name, ok := call.Arguments[0].(*ast.Identifier)
	if !ok {
		return 0, false
	}
	sp, ok := g.spans[name.Value]
	if !ok || sp.array == nil || sp.frameLen != sp.array.length || sp.frameLen < 0 || uint64(sp.frameLen) > mask64(32) {
		return 0, false
	}
	// A subslice has no array/constant-length metadata. In particular, its
	// backing array's length must never stand in for its own length.
	right := e.Right
	if cast, ok := right.(*ast.InvocationExpression); ok {
		ctor, ok := cast.Function.(*ast.Identifier)
		if !ok || ctor.Value != "u32" || len(cast.Arguments) != 1 {
			return 0, false
		}
		// Only a literal constructor, not u32(u8(...)) or u32(f()).
		if _, ok := cast.Arguments[0].(*ast.IntegerLiteral); !ok {
			return 0, false
		}
		right = cast.Arguments[0]
	}
	var divisor uint64
	switch x := right.(type) {
	case *ast.IntegerLiteral:
		if x.Value <= 0 || uint64(x.Value) > mask64(32) {
			return 0, false
		}
		divisor = uint64(x.Value)
	case *ast.Identifier:
		c, ok := g.constantOf(x.Value)
		if !ok || c.Type != "u32" || c.Value == 0 || c.Value > mask64(32) {
			return 0, false
		}
		divisor = c.Value
	default:
		return 0, false
	}
	if e.Operator == "%" {
		return uint64(sp.frameLen) % divisor, true
	}
	return uint64(sp.frameLen) / divisor, true
}
