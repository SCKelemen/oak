package nativegen

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Lexer token kinds are nonnegative. This private, clone-stable marker cannot
// arise from source spelling; it licenses recognition, never proof admission.
const horizontalReductionToken token.TokenKind = -1
const horizontalReductionContext = "oak.native.horizontal.unsigned"

func markHorizontalReduction(tok token.Token) token.Token {
	tok.TokenKind = horizontalReductionToken
	tok.SemanticContext = horizontalReductionContext
	tok.Synthetic = true
	return tok
}

type horizontalCombine struct {
	vector *ast.Identifier
	acc    *ast.Identifier
	elem   scalar
}

// horizontalReduction recognizes only the compiler-generated three-statement
// private-array combine. The array must have no other references anywhere in
// the function: not even an escaping span or a later same-named declaration.
// No source AST is changed; asm.Verify still compares against its array store
// and scalar lane reads. ADDV/ADDP are wrapping integer sums, not FP reassociation.
func (g *generator) horizontalReduction(stmts []ast.Statement) (horizontalCombine, bool) {
	no := horizontalCombine{}
	if g.rvLane || g.fn == nil || len(stmts) < 3 {
		return no, false
	}
	decl, ok := stmts[0].(*ast.VariableDeclaration)
	if !ok || decl.Name == nil || decl.Token.TokenKind != horizontalReductionToken ||
		decl.Token.SemanticContext != horizontalReductionContext || !decl.Token.Synthetic ||
		decl.Exported || decl.Opaque || decl.NativeAddressed || decl.Section != "" || decl.Measured != nil || decl.Threadgroup {
		return no, false
	}
	elem, count, ok := arrayOf(decl.Type)
	if !ok || !((elem == scalars["u32"] && count == 4) || (elem == scalars["u64"] && count == 2)) {
		return no, false
	}
	shape, memberName := vecShapes["U32x4"], "store_u32x4"
	if elem == scalars["u64"] {
		shape, memberName = vecShapes["U64x2"], "store_u64x2"
	}
	init, ok := decl.Value.(*ast.ArrayLiteral)
	if !ok || int64(len(init.Elements)) != count {
		return no, false
	}
	initElem, initCount, ok := arrayOf(init.Type)
	if !ok || initElem != elem || initCount != count {
		return no, false
	}
	for _, expr := range init.Elements {
		zero, ok := expr.(*ast.IntegerLiteral)
		if !ok || zero.Value != 0 {
			return no, false
		}
	}
	effect, ok := stmts[1].(*ast.ExpressionStatement)
	if !ok {
		return no, false
	}
	store, ok := effect.Expression.(*ast.InvocationExpression)
	if !ok || len(store.Arguments) != 3 {
		return no, false
	}
	member, ok := simdCallee(store.Function)
	if !ok || member != memberName || !isHorizontalZero(store.Arguments[1]) {
		return no, false
	}
	span, ok := store.Arguments[0].(*ast.InvocationExpression)
	if !ok || !isName(span.Function, "span") || len(span.Arguments) != 1 {
		return no, false
	}
	borrow, ok := span.Arguments[0].(*ast.PrefixExpression)
	if !ok || borrow.Operator != "&" || !isName(borrow.Right, decl.Name.Value) {
		return no, false
	}
	vector, ok := store.Arguments[2].(*ast.Identifier)
	if !ok || g.types[vector.Value] != shape {
		return no, false
	}
	assign, ok := stmts[2].(*ast.AssignmentStatement)
	if !ok || assign.Name == nil || g.types[assign.Name.Value] != elem {
		return no, false
	}
	sum, ok := assign.Value.(*ast.InfixExpression)
	if !ok || sum.Operator != "+" || !isName(sum.Left, assign.Name.Value) {
		return no, false
	}
	lane := int64(0)
	var tree func(ast.Expression) bool
	tree = func(expr ast.Expression) bool {
		if plus, ok := expr.(*ast.InfixExpression); ok {
			return plus.Operator == "+" && tree(plus.Left) && tree(plus.Right)
		}
		index, ok := expr.(*ast.IndexExpression)
		if !ok || index.Dot || !isName(index.Left, decl.Name.Value) {
			return false
		}
		at, ok := index.Index.(*ast.IntegerLiteral)
		if !ok || at.Value != lane || lane >= count {
			return false
		}
		lane++
		return true
	}
	if !tree(sum.Right) || lane != count {
		return no, false
	}
	for _, param := range g.fn.Parameters {
		if param != nil && param.Name != nil && param.Name.Value == decl.Name.Value {
			return no, false
		}
	}
	owned := 0
	walk(g.fn.Body, func(node ast.Node) {
		if node == stmts[0] || node == stmts[1] || node == stmts[2] {
			owned++
		}
	})
	if owned != 3 {
		return no, false
	}
	// The exact group accounts for a declaration, borrow, and each lane. The identifier
	// walk includes binding positions, callees, types, and nested syntax;
	// any additional occurrence (even a shared AST pointer) refuses fusion.
	uses := 0
	mentionIdents(g.fn.Body, func(name string) {
		if name == decl.Name.Value {
			uses++
		}
	})
	if int64(uses) != count+2 {
		return no, false
	}
	return horizontalCombine{vector: vector, acc: assign.Name, elem: elem}, true
}

func isHorizontalZero(expr ast.Expression) bool {
	if cast, ok := expr.(*ast.InvocationExpression); ok {
		if !isName(cast.Function, "u32") || len(cast.Arguments) != 1 {
			return false
		}
		expr = cast.Arguments[0]
	}
	zero, ok := expr.(*ast.IntegerLiteral)
	return ok && zero.Value == 0
}

func (g *generator) lowerHorizontalReduction(combine horizontalCombine) error {
	elem := combine.elem
	shape, view, mnemonic := vecShapes["U32x4"], scalars["f32"], "addv"
	if elem == scalars["u64"] {
		shape, view, mnemonic = vecShapes["U64x2"], scalars["f64"], "addp"
	} else if elem != scalars["u32"] {
		return Unsupported{"horizontal reduction requires u32 or u64"}
	}
	source, fixed, err := g.vecOperand(combine.vector, shape)
	if err != nil {
		return err
	}
	defer g.vecRelease(source, fixed)
	// Never reduce into the source home: ADDV/ADDP zero their remaining lanes,
	// and the vector may remain live after the scalar accumulator update.
	tmp, err := g.alloc(view)
	if err != nil {
		return err
	}
	defer g.release(tmp)
	result, err := g.alloc(elem)
	if err != nil {
		return err
	}
	seed, seedFixed, err := g.operand(combine.acc, elem)
	if err != nil {
		g.release(result)
		return err
	}
	if !seedFixed {
		defer g.release(seed)
	}
	g.emit(mnemonic, vr(tmp-vecBase, view), vreg(source-vecBase, shape.arr()))
	lane := "s"
	if elem == scalars["u64"] {
		lane = "d"
	}
	g.emit("umov", reg(result, elem), laneReg(tmp-vecBase, lane, 0))
	g.emit("add", reg(result, elem), reg(seed, elem), reg(result, elem))
	g.assignVar(combine.acc.Value, result) // releases result, as ordinary assignment does
	g.killLoopFacts(combine.acc.Value)
	return nil
}
