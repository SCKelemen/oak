package nativegen

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Verified fold vectorization (docs/spec/94-assembler.md §9 "Fold
// vectorization"; spec/lean/Oak/Fold.lean blocked_eq). A reduction whose
// element expression is lane-wise over span parameters of one length,
//
//	while i < len(a) { acc = acc + a[i] * b[i]; i = i + u32(1) }
//
// is rewritten, before lowering, into a main loop that computes the
// expression over one vector of elements — the loads, the lane-wise
// operations, the invariant scalars and constants splatted before the
// loop as the map vectorization spells them — and then adds the vector's
// lanes to the accumulator one at a time, in element order, under the
// slack guard the vector kernels spell, and the remainder loop as written:
//
//	while len(a) >= u32(4) && i <= len(a) - u32(4) {
//	  acc_p: simd.F32x4 = simd.mul_f32x4(simd.load_f32x4(a, i), simd.load_f32x4(b, i))
//	  acc = acc + simd.extract_f32x4(acc_p, u32(0))
//	  acc = acc + simd.extract_f32x4(acc_p, u32(1))
//	  acc = acc + simd.extract_f32x4(acc_p, u32(2))
//	  acc = acc + simd.extract_f32x4(acc_p, u32(3))
//	  i = i + u32(4)
//	}
//	while i < len(a) { acc = acc + a[i] * b[i]; i = i + u32(1) }
//
// The accumulator is a float: the additions keep their order, so the
// result rounds as the scalar loop's did and the rewrite reassociates
// nothing — which is why it needs no law of the element type where the
// reduction vectorization (nativegen/vector_reduction.go) takes integers
// only. What it saves is the element work: one vector load per span and
// one lane-wise operation per operator for every lane, where the scalar
// loop spends a load per span and an operation per operator for every
// element; the accumulator's chain is the same one addition an element
// either way. An expression that is a bare element (`acc = acc + v[i]`)
// saves nothing and is left to the scalar loop.
//
// Recognized like the maps (recognizeMap): the loop's span and every span
// the expression reads are parameters of the accumulator's element type
// known to have one length where the loop stands, and the expression
// reads them at the loop's index only.

// foldLoop is one recognized reduction: the map reading of its element
// expression (dst names the accumulator, for the splats' names) and the
// accumulator's side of the addition.
type foldLoop struct {
	mapLoop
	acc      string
	accFirst bool // acc = acc + E (true) or acc = E + acc
}

// vectorizeFolds returns the body with its lane-wise float reductions
// vectorized, and whether any was. With unroll, the main loop takes two
// vectors of elements a trip, a one-vector loop cleaning up before the
// scalar remainder (Lane.UnrollVectorFolds).
func vectorizeFolds(fn *ast.FunctionStatement, body ast.Expression, unroll bool) (ast.Expression, bool) {
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil {
		return body, false
	}
	types := declaredScalarTypes(block.Block.Statements)
	spans := map[string]span{}
	for _, p := range fn.Parameters {
		if p == nil || p.Name == nil || p.Variadic {
			continue
		}
		if sp, ok := spanOf(p.Type); ok {
			if !sp.atomic {
				spans[p.Name.Value] = sp
			}
			continue
		}
		if _, declared := types[p.Name.Value]; !declared {
			if s, ok := scalarOf(p.Type); ok && !s.isVec {
				types[p.Name.Value] = p.Type
			}
		}
	}
	if len(spans) == 0 {
		return body, false
	}
	changed := false
	var rewrite func(stmts []ast.Statement, equal lengthClasses) []ast.Statement
	rewrite = func(stmts []ast.Statement, equal lengthClasses) []ast.Statement {
		var out []ast.Statement
		var prev ast.Statement
		for _, stmt := range stmts {
			switch s := stmt.(type) {
			case *ast.WhileStatement:
				if f, ok := recognizeFold(s, prev, types, spans, equal, body); ok {
					out = append(out, vectorizedFold(f, unroll)...)
					changed = true
					prev = stmt
					continue
				}
				if s.Body != nil {
					s.Body.Statements = rewrite(s.Body.Statements, equal)
				}
			case *ast.ExpressionStatement:
				if inner, isBlock := s.Expression.(*ast.BlockExpression); isBlock && inner.Block != nil {
					inner.Block.Statements = rewrite(inner.Block.Statements, equal)
				}
				if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
					for _, arm := range match.Arms {
						if armBlock, isBlock := arm.Body.(*ast.BlockExpression); isBlock && armBlock.Block != nil {
							armBlock.Block.Statements = rewrite(armBlock.Block.Statements, armFacts(match, arm, equal))
						}
					}
				}
			case *ast.BlockStatement:
				s.Statements = rewrite(s.Statements, equal)
			}
			out = append(out, stmt)
			prev = stmt
		}
		return out
	}
	clone := cloneNode(body).(*ast.BlockExpression)
	clone.Block.Statements = rewrite(clone.Block.Statements, nil)
	if !changed {
		return body, false
	}
	return clone, true
}

// foldVectorName names the vector of one block's element values.
func foldVectorName(acc string) string { return acc + "_p" }

// recognizeFold reads a loop as a lane-wise float reduction over span
// parameters: `while i < len(a) { acc = acc + E; i = i + 1 }`, acc a
// declared f32 or f64 local, E a lane-wise expression (mapLoop.laneWise)
// with at least one operation that reads neither acc nor the index
// outside an element.
func recognizeFold(loop *ast.WhileStatement, prev ast.Statement, types map[string]ast.Expression, spans map[string]span, equal lengthClasses, body ast.Expression) (foldLoop, bool) {
	cond, isInfix := loop.Condition.(*ast.InfixExpression)
	if !isInfix || cond.Operator != "<" || loop.Body == nil || len(loop.Body.Statements) != 2 {
		return foldLoop{}, false
	}
	idx, isIdent := cond.Left.(*ast.Identifier)
	if !isIdent {
		return foldLoop{}, false
	}
	src, isLen := lenOf(cond.Right)
	if !isLen {
		return foldLoop{}, false
	}
	accum, isAssign := loop.Body.Statements[0].(*ast.AssignmentStatement)
	step, isStep := loop.Body.Statements[1].(*ast.AssignmentStatement)
	if !isAssign || !isStep || accum.Name == nil || step.Name == nil || step.Name.Value != idx.Value {
		return foldLoop{}, false
	}
	acc := accum.Name.Value
	if acc == idx.Value || acc == src {
		return foldLoop{}, false
	}
	// acc = acc + E (either order); E an operation, not a bare element.
	sum, isSum := accum.Value.(*ast.InfixExpression)
	if !isSum || sum.Operator != "+" {
		return foldLoop{}, false
	}
	var elem ast.Expression
	accFirst := false
	switch {
	case isName(sum.Left, acc):
		elem, accFirst = sum.Right, true
	case isName(sum.Right, acc):
		elem = sum.Left
	default:
		return foldLoop{}, false
	}
	if _, isOp := elem.(*ast.InfixExpression); !isOp || mentionsName(elem, acc) {
		return foldLoop{}, false
	}
	// i = i + 1, the index a u32.
	inc, isInc := step.Value.(*ast.InfixExpression)
	if !isInc || inc.Operator != "+" || !isName(inc.Left, idx.Value) {
		return foldLoop{}, false
	}
	if one, isConst := constantValue(inc.Right); !isConst || one != 1 {
		return foldLoop{}, false
	}
	if idxType, declared := types[idx.Value]; !declared || idxType.String() != "u32" {
		return foldLoop{}, false
	}
	// The accumulator: a declared float local of the spans' element type.
	accType, declared := types[acc]
	if !declared {
		return foldLoop{}, false
	}
	typ, isScalar := scalarOf(accType)
	if !isScalar || !typ.isFloat {
		return foldLoop{}, false
	}
	s, hasSrc := spans[src]
	if !hasSrc || s.elemLayout != nil || s.elem.name != typ.name {
		return foldLoop{}, false
	}
	suffix, vecType, lanes, ok := mapShapeFor(s.elem)
	if !ok {
		return foldLoop{}, false
	}
	m := mapLoop{loop: loop, idx: idx.Value, src: src, dst: acc, elem: s.elem, suffix: suffix, vecType: vecType, lanes: lanes, value: elem, spans: spans, sameLength: equal.same}
	if !m.laneWise(elem, types) {
		return foldLoop{}, false
	}
	// Fresh names for the splats and the blocks' vectors.
	for _, name := range []string{foldVectorName(acc), foldVectorName(acc) + "0", foldVectorName(acc) + "1"} {
		if mentionsName(body, name) {
			return foldLoop{}, false
		}
	}
	for _, name := range m.scalars {
		if mentionsName(body, name+"_v") {
			return foldLoop{}, false
		}
	}
	for k := range m.constants {
		if mentionsName(body, m.constantName(k)) {
			return foldLoop{}, false
		}
	}
	// Not the remainder loop of a fold this rewrite made: that follows a
	// loop under the slack guard over the same span and index.
	if prevLoop, isLoop := prev.(*ast.WhileStatement); isLoop {
		for _, fact := range loopFactsOf(prevLoop.Condition) {
			if fact.span == src && fact.index == idx.Value && fact.slack == lanes {
				return foldLoop{}, false
			}
		}
	}
	return foldLoop{mapLoop: m, acc: acc, accFirst: accFirst}, true
}

// vectorizedFold spells the rewrite for one recognized loop: with unroll,
// a two-vector loop first, then the one-vector loop, then the remainder —
// each loop the blocked fold of Oak.Fold.blocked_eq over what the loops
// before it left, the lanes added in element order throughout.
func vectorizedFold(f foldLoop, unroll bool) []ast.Statement {
	m := f.mapLoop
	tok := m.loop.Token
	ident := func(name string) *ast.Identifier { return &ast.Identifier{Token: tok, Value: name} }
	literal := func(v int64) ast.Expression { return &ast.IntegerLiteral{Token: tok, Value: v} }
	u32 := func(v int64) ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("u32"), Arguments: []ast.Expression{literal(v)}}
	}
	infix := func(l ast.Expression, op string, r ast.Expression) ast.Expression {
		return &ast.InfixExpression{Token: token.Token{Line: tok.Line, Literal: op}, Left: l, Operator: op, Right: r}
	}
	simd := func(member string, args ...ast.Expression) ast.Expression {
		callee := &ast.IndexExpression{Token: tok, Left: ident("simd"), Index: ident(member + "_" + m.suffix), Dot: true}
		return &ast.InvocationExpression{Token: tok, Function: callee, Arguments: args}
	}
	vecType := func() ast.Expression { return ident(m.vecType) }
	length := func() ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("len"), Arguments: []ast.Expression{ident(m.src)}}
	}
	var out []ast.Statement
	for _, s := range m.scalars {
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: ident(s + "_v"), Type: vecType(), Value: simd("splat", ident(s))})
	}
	for k, c := range m.constants {
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: ident(m.constantName(k)), Type: vecType(), Value: simd("splat", c.arg)})
	}
	vectorLoop := func(groups int64) *ast.WhileStatement {
		stride := groups * m.lanes
		guard := infix(infix(length(), ">=", u32(stride)), "&&", infix(ident(m.idx), "<=", infix(length(), "-", u32(stride))))
		loop := &ast.WhileStatement{Token: tok, Condition: guard, Body: &ast.BlockStatement{Token: tok}}
		for group := int64(0); group < groups; group++ {
			var at ast.Expression = ident(m.idx)
			if group != 0 {
				at = infix(ident(m.idx), "+", u32(group*m.lanes))
			}
			block := foldVectorName(f.acc)
			if groups > 1 {
				block += itoa(int(group))
			}
			loop.Body.Statements = append(loop.Body.Statements, &ast.VariableDeclaration{Token: tok, Name: ident(block), Type: vecType(), Value: m.vectorExprAt(m.value, tok, at)})
			for k := int64(0); k < m.lanes; k++ {
				lane := simd("extract", ident(block), u32(k))
				value := infix(ident(f.acc), "+", lane)
				if !f.accFirst {
					value = infix(lane, "+", ident(f.acc))
				}
				loop.Body.Statements = append(loop.Body.Statements, &ast.AssignmentStatement{Token: tok, Name: ident(f.acc), Value: value})
			}
		}
		loop.Body.Statements = append(loop.Body.Statements, &ast.AssignmentStatement{Token: tok, Name: ident(m.idx), Value: infix(ident(m.idx), "+", u32(stride))})
		return loop
	}
	if unroll {
		out = append(out, vectorLoop(2))
	}
	return append(out, vectorLoop(1), m.loop)
}
