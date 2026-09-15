package nativegen

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Verified reduction vectorization (docs/spec/94-assembler.md §9
// "Reductions"; docs/notes/optimizer-search-2026-09.md Phase D item 23;
// spec/lean/Oak/Reduction.lean vector4_eq). The integer reduction the
// unrolling recognizes,
//
//	while i < len(v) { acc = acc + v[i]; i = i + 1 }
//
// is rewritten, before lowering, into a main loop of eight elements an
// iteration whose accumulators are fixed vectors — four simd.U64x2 for a
// u64 accumulator, two simd.U32x4 for a u32 one — under the slack guard
// the vector kernels spell, the remainder loop as written, and the
// lane-wise combine through an eight-element frame array:
//
//	acc_v0: simd.U32x4 = simd.splat_u32x4(u32(0))   acc_v1: simd.U32x4 = simd.splat_u32x4(u32(0))
//	while len(v) >= u32(8) && i <= len(v) - u32(8) {
//	  acc_v0 = simd.add_u32x4(acc_v0, simd.load_u32x4(v, i))
//	  acc_v1 = simd.add_u32x4(acc_v1, simd.load_u32x4(v, i + u32(4)))
//	  i = i + u32(8)
//	}
//	while i < len(v) { acc = acc + v[i]; i = i + u32(1) }
//	acc_vs: simd.U32x4 = simd.add_u32x4(acc_v0, acc_v1)
//	acc_vl: [4]u32 = [4]u32{ 0, 0, 0, 0 }
//	simd.store_u32x4(span(&acc_vl), u32(0), acc_vs)
//	acc = acc + ((acc_vl[0] + acc_vl[1]) + (acc_vl[2] + acc_vl[3]))
//
// Eight elements an iteration, not four: with one vector accumulator the
// loop-carried chain is a single lane-wise add and the form is slower than
// the scalar unrolling's four independent chains (measured: 0.18 against
// 0.14 ns an element over 2^20 u32 elements), where two or four vector
// accumulators break the chain and win (0.10; benchmarks/native/README.md).
// The lanes reach the scalar through the frame array because the integer
// vectors have no lane `extract` in v1 (docs/spec/93-simd.md §1.2a
// reserves it with the comparison masks), and the round trip runs once
// after the loops, not per iteration.
//
// The lowering sees the rewritten body — two `ldr q` and two `add v.2d`
// per four elements — and the verifier proves the assembly against it,
// the vector accumulators coupled lane by lane as the vector kernels'
// are. The rewrite is the theorem: each simd operation is lane-wise by
// its specification (docs/spec/93-simd.md §1: `add` wraps per lane,
// `load` reads consecutive elements, `extract` reads a lane), so the
// loop is the four-accumulator fold with the lanes as the accumulators
// from zero, and the scalar accumulator folds the remainder — the fold
// `vector4` of Oak.Reduction, equal to the sequential fold from the
// accumulator's initial value (vector4_eq). Recognized where the
// unrolling recognizes (recognizeReduction); a u16 or u8 accumulator
// stays with the scalar unrolling in this increment.

// vectorizeReductions returns the body with its plain u64 and u32
// reductions vectorized, and whether any was.
func vectorizeReductions(fn *ast.FunctionStatement, body ast.Expression) (ast.Expression, bool) {
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil {
		return body, false
	}
	types := declaredScalarTypes(block.Block.Statements)
	changed := false
	var rewrite func(stmts []ast.Statement) []ast.Statement
	rewrite = func(stmts []ast.Statement) []ast.Statement {
		var out []ast.Statement
		for _, stmt := range stmts {
			switch s := stmt.(type) {
			case *ast.WhileStatement:
				if red, ok := recognizeReduction(s, types, body); ok {
					if shape, lanes, ok := vectorShapeFor(red.accType); ok && freshVectorNames(body, red.acc) {
						out = append(out, vectorizedReduction(red, shape, lanes)...)
						changed = true
						continue
					}
				}
				if s.Body != nil {
					s.Body.Statements = rewrite(s.Body.Statements)
				}
			case *ast.ExpressionStatement:
				if inner, isBlock := s.Expression.(*ast.BlockExpression); isBlock && inner.Block != nil {
					inner.Block.Statements = rewrite(inner.Block.Statements)
				}
				if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
					for _, arm := range match.Arms {
						if armBlock, isBlock := arm.Body.(*ast.BlockExpression); isBlock && armBlock.Block != nil {
							armBlock.Block.Statements = rewrite(armBlock.Block.Statements)
						}
					}
				}
			case *ast.BlockStatement:
				s.Statements = rewrite(s.Statements)
			}
			out = append(out, stmt)
		}
		return out
	}
	clone := cloneNode(body).(*ast.BlockExpression)
	clone.Block.Statements = rewrite(clone.Block.Statements)
	if !changed {
		return body, false
	}
	return clone, true
}

// vectorShapeFor names the vector shape whose lanes hold an accumulator
// type — the suffix of the simd operations (`u64x2`, `u32x4`) — and the
// lane count; false for the widths this increment leaves to the unrolling.
func vectorShapeFor(accType ast.Expression) (suffix string, lanes int64, ok bool) {
	switch accType.String() {
	case "u64":
		return "u64x2", 2, true
	case "u32":
		return "u32x4", 4, true
	}
	return "", 0, false
}

func vectorName(acc string, k int) string { return acc + "_v" + string(rune('0'+k)) }

// freshVectorNames reports that the names the rewrite declares — the lane
// accumulators and the combine's array — appear nowhere in the body.
func freshVectorNames(body ast.Expression, acc string) bool {
	for _, k := range []int{0, 1, 2, 3, 'l' - '0', 's' - '0'} {
		if mentionsName(body, vectorName(acc, k)) {
			return false
		}
	}
	return true
}

// vectorizedReduction spells the rewrite for one recognized loop: step
// elements an iteration over step/lanes vector accumulators.
func vectorizedReduction(red reductionLoop, suffix string, lanes int64) []ast.Statement {
	const step = 8
	tok := red.loop.Token
	ident := func(name string) *ast.Identifier { return &ast.Identifier{Token: tok, Value: name} }
	literal := func(v int64) ast.Expression { return &ast.IntegerLiteral{Token: tok, Value: v} }
	typed := func(typ string, v int64) ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident(typ), Arguments: []ast.Expression{literal(v)}}
	}
	u32 := func(v int64) ast.Expression { return typed("u32", v) }
	infix := func(l ast.Expression, op string, r ast.Expression) ast.Expression {
		return &ast.InfixExpression{Token: token.Token{Line: tok.Line, Literal: op}, Left: l, Operator: op, Right: r}
	}
	simd := func(member string, args ...ast.Expression) ast.Expression {
		callee := &ast.IndexExpression{Token: tok, Left: ident("simd"), Index: ident(member + "_" + suffix), Dot: true}
		return &ast.InvocationExpression{Token: tok, Function: callee, Arguments: args}
	}
	// A dotted type is one identifier, as the parser spells it (parser.go,
	// qualified library types): `simd.U64x2`.
	vecType := func() ast.Expression {
		if suffix == "u32x4" {
			return ident("simd.U32x4")
		}
		return ident("simd.U64x2")
	}
	length := func() ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("len"), Arguments: []ast.Expression{ident(red.span)}}
	}
	index := func(offset int64) ast.Expression {
		if offset == 0 {
			return ident(red.idx)
		}
		return infix(ident(red.idx), "+", u32(offset))
	}
	assign := func(name string, value ast.Expression) ast.Statement {
		return &ast.AssignmentStatement{Token: tok, Name: ident(name), Value: value}
	}
	vectors := int64(step) / lanes
	var out []ast.Statement
	for k := int64(0); k < vectors; k++ {
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: ident(vectorName(red.acc, int(k))), Type: vecType(), Value: simd("splat", typed(red.accType.String(), 0))})
	}
	guard := infix(infix(length(), ">=", u32(step)), "&&", infix(ident(red.idx), "<=", infix(length(), "-", u32(step))))
	main := &ast.WhileStatement{Token: tok, Condition: guard, Body: &ast.BlockStatement{Token: tok}}
	for k := int64(0); k < vectors; k++ {
		name := vectorName(red.acc, int(k))
		main.Body.Statements = append(main.Body.Statements, assign(name, simd("add", ident(name), simd("load", ident(red.span), index(k*lanes)))))
	}
	main.Body.Statements = append(main.Body.Statements, assign(red.idx, infix(ident(red.idx), "+", u32(step))))
	out = append(out, main, red.loop)
	// The combine: the vector accumulators folded pairwise into one vector
	// (lane-wise addition, the same law), that vector's lanes stored into
	// a frame array of one vector's lanes, read back as a balanced tree
	// and added to the scalar accumulator after the remainder loop. The
	// vector fold costs log2(vectors) adds where storing every accumulator
	// costs a store and lanes loads each.
	folded := ident(vectorName(red.acc, 0))
	if vectors > 1 {
		names := make([]ast.Expression, vectors)
		for k := int64(0); k < vectors; k++ {
			names[k] = ident(vectorName(red.acc, int(k)))
		}
		var fold func(v []ast.Expression) ast.Expression
		fold = func(v []ast.Expression) ast.Expression {
			if len(v) == 1 {
				return v[0]
			}
			mid := len(v) / 2
			return simd("add", fold(v[:mid]), fold(v[mid:]))
		}
		sum := ident(vectorName(red.acc, 's'-'0'))
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: sum, Type: vecType(), Value: fold(names)})
		folded = sum
	}
	elemName := red.accType.String()
	arrayType := func() ast.Expression {
		return &ast.IndexExpression{Token: tok, Left: ident(elemName), Index: literal(lanes)}
	}
	zeros := make([]ast.Expression, lanes)
	for k := range zeros {
		zeros[k] = literal(0)
	}
	array := vectorName(red.acc, 'l'-'0')
	out = append(out, &ast.VariableDeclaration{
		Token: tok, Name: ident(array), Type: arrayType(),
		Value: &ast.ArrayLiteral{Token: tok, Type: arrayType(), Elements: zeros},
	})
	spanOf := func() ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("span"), Arguments: []ast.Expression{
			&ast.PrefixExpression{Token: token.Token{Line: tok.Line, Literal: "&"}, Operator: "&", Right: ident(array)},
		}}
	}
	out = append(out, &ast.ExpressionStatement{Token: tok, Expression: simd("store", spanOf(), u32(0), folded)})
	lane := func(k int64) ast.Expression {
		// The read is inside the step-element array: its guard is elided as
		// a typechecker-proven one is.
		at := token.Token{SemanticContext: rewriteContext, Line: tok.Line, Column: int(k) + 1, Literal: "["}
		markRewriteProven(at)
		return &ast.IndexExpression{Token: at, Left: ident(array), Index: literal(k)}
	}
	// A balanced tree over the lanes: the grouping is immaterial to the
	// value (integer addition reassociates) and shortest for the machine.
	var tree func(lo, hi int64) ast.Expression
	tree = func(lo, hi int64) ast.Expression {
		if hi-lo == 1 {
			return lane(lo)
		}
		mid := (lo + hi) / 2
		return infix(tree(lo, mid), "+", tree(mid, hi))
	}
	out = append(out, assign(red.acc, infix(ident(red.acc), "+", tree(0, lanes))))
	return out
}
