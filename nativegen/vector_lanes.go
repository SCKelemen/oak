package nativegen

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Lane-wise accumulators (docs/spec/94-assembler.md §9 "Lane-wise
// accumulators"; spec/lean/Oak/Lanes.lean blocks_eq). A loop under the
// slack guard whose body updates L independent accumulators, one per
// element of the block, with one lane-wise expression shifted along the
// block,
//
//	acc: [8]f32 = [8]f32{ 0.0, … }
//	while len(a) >= u32(8) && i <= len(a) - u32(8) {
//	  acc[0] = acc[0] + a[i] * a[i]
//	  acc[1] = acc[1] + a[i + u32(1)] * a[i + u32(1)]
//	  …
//	  acc[7] = acc[7] + a[i + u32(7)] * a[i + u32(7)]
//	  i = i + u32(8)
//	}
//
// is rewritten, before lowering, into the same loop over vector
// accumulators: each vector's lanes gathered from acc before the loop
// (splat and insert), the block's elements loaded as vectors, the
// expression applied lane-wise, each lane added to its accumulator, and
// the lanes stored back into acc after the loop (extract), before the
// remainder loop and whatever reads acc:
//
//	acc_v0: simd.F32x4 = simd.insert_f32x4(… simd.splat_f32x4(acc[0]) …, u32(3), acc[3])
//	acc_v1: simd.F32x4 = …
//	while len(a) >= u32(8) && i <= len(a) - u32(8) {
//	  acc_v0 = simd.add_f32x4(acc_v0, simd.mul_f32x4(simd.load_f32x4(a, i), simd.load_f32x4(a, i)))
//	  acc_v1 = simd.add_f32x4(acc_v1, simd.mul_f32x4(simd.load_f32x4(a, i + u32(4)), simd.load_f32x4(a, i + u32(4))))
//	  i = i + u32(8)
//	}
//	acc[0] = simd.extract_f32x4(acc_v0, u32(0))
//	…
//
// Lane k of the vectors meets exactly the values acc[k] met, in the same
// order, so a float accumulator rounds as before; the L statements of a
// block touch L different lanes, so one lane-wise step is all of them
// (Oak.Lanes.blocks_eq). Recognized for float lanes (f32x4, f64x2 —
// their lanes extract), the accumulator an owned array of L = lanes ×
// {1, 2, 4} elements the body indexes by constants (so its elements are
// scalars, nativegen/scalar_arrays.go), the expression lane-wise over
// span parameters of one length read at the lane's own offset
// (mapLoop.laneWise), and the step the block's length.

// laneLoop is one recognized loop: the map reading of lane 0's
// expression (dst names the accumulator array) and the accumulators.
type laneLoop struct {
	mapLoop
	acc     string
	count   int64 // L: accumulators, elements a trip
	vectors int64 // L / lanes
	value   ast.Expression
}

// vectorizeLanes returns the body with its lane-wise accumulator loops
// vectorized, and whether any was.
func vectorizeLanes(fn *ast.FunctionStatement, body ast.Expression) (ast.Expression, bool) {
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil {
		return body, false
	}
	types := declaredScalarTypes(block.Block.Statements)
	spans := map[string]span{}
	arrays := map[string]ast.Expression{} // owned array locals by name: their element type
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
	walk(body, func(n ast.Node) {
		if d, isDecl := n.(*ast.VariableDeclaration); isDecl && d.Name != nil && d.Type != nil && isArraySyntax(d.Type) {
			arrays[d.Name.Value] = d.Type
		}
	})
	if len(spans) == 0 || len(arrays) == 0 {
		return body, false
	}
	changed := false
	var rewrite func(stmts []ast.Statement, equal lengthClasses) []ast.Statement
	rewrite = func(stmts []ast.Statement, equal lengthClasses) []ast.Statement {
		var out []ast.Statement
		for _, stmt := range stmts {
			switch s := stmt.(type) {
			case *ast.WhileStatement:
				if l, ok := recognizeLanes(s, types, spans, arrays, equal, body); ok {
					out = append(out, vectorizedLanes(l)...)
					changed = true
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

// laneVectorName names accumulator vector v.
func laneVectorName(acc string, v int64) string { return acc + "_v" + itoa(int(v)) }

// recognizeLanes reads a while statement as a lane-wise accumulator loop.
func recognizeLanes(loop *ast.WhileStatement, types map[string]ast.Expression, spans map[string]span, arrays map[string]ast.Expression, equal lengthClasses, body ast.Expression) (laneLoop, bool) {
	// The slack guard over one span and one index, the step the slack.
	facts := loopFactsOf(loop.Condition)
	if len(facts) != 1 || loop.Body == nil {
		return laneLoop{}, false
	}
	src, idx, count := facts[0].span, facts[0].index, facts[0].slack
	stmts := loop.Body.Statements
	if int64(len(stmts)) != count+1 || count < 2 {
		return laneLoop{}, false
	}
	step, isStep := stmts[count].(*ast.AssignmentStatement)
	if !isStep || step.Name == nil || step.Name.Value != idx {
		return laneLoop{}, false
	}
	inc, isInc := step.Value.(*ast.InfixExpression)
	if !isInc || inc.Operator != "+" || !isName(inc.Left, idx) {
		return laneLoop{}, false
	}
	if by, isConst := constantValue(inc.Right); !isConst || by != count {
		return laneLoop{}, false
	}
	if idxType, declared := types[idx]; !declared || idxType.String() != "u32" {
		return laneLoop{}, false
	}
	s, hasSrc := spans[src]
	if !hasSrc || s.elemLayout != nil || !s.elem.isFloat {
		return laneLoop{}, false
	}
	suffix, vecType, lanes, ok := mapShapeFor(s.elem)
	if !ok || count%lanes != 0 || count/lanes > 4 {
		return laneLoop{}, false
	}
	// The statements: acc[k] = acc[k] + E_k, k in order, E_k lane 0's
	// expression shifted by k along the index.
	var acc string
	var lane0 ast.Expression
	for k := int64(0); k < count; k++ {
		store, isStore := stmts[k].(*ast.IndexAssignmentStatement)
		if !isStore || store.Target == nil || store.Target.Dot {
			return laneLoop{}, false
		}
		base, isIdent := store.Target.Left.(*ast.Identifier)
		at, isConst := constantValue(store.Target.Index)
		if !isIdent || !isConst || at != k {
			return laneLoop{}, false
		}
		if k == 0 {
			acc = base.Value
		} else if base.Value != acc {
			return laneLoop{}, false
		}
		sum, isSum := store.Value.(*ast.InfixExpression)
		if !isSum || sum.Operator != "+" {
			return laneLoop{}, false
		}
		var elem ast.Expression
		switch {
		case accumulatorRead(sum.Left, acc, k):
			elem = sum.Right
		case accumulatorRead(sum.Right, acc, k):
			elem = sum.Left
		default:
			return laneLoop{}, false
		}
		if mentionsName(elem, acc) {
			return laneLoop{}, false
		}
		if k == 0 {
			lane0 = elem
		} else if !shiftedBy(lane0, elem, idx, k) {
			return laneLoop{}, false
		}
	}
	// The accumulator: an owned array of count elements of the lane type.
	accType, isArray := arrays[acc]
	if !isArray {
		return laneLoop{}, false
	}
	arrayType, isIndex := accType.(*ast.IndexExpression)
	if !isIndex {
		return laneLoop{}, false
	}
	length, isLit := arrayType.Index.(*ast.IntegerLiteral)
	if !isLit || length.Value != count {
		return laneLoop{}, false
	}
	if elemType, isScalar := scalarOf(arrayType.Left); !isScalar || elemType.name != s.elem.name {
		return laneLoop{}, false
	}
	if _, isSpan := spans[acc]; isSpan {
		return laneLoop{}, false
	}
	m := mapLoop{loop: loop, idx: idx, src: src, dst: acc, elem: s.elem, suffix: suffix, vecType: vecType, lanes: lanes, value: lane0, spans: spans, sameLength: equal.same}
	if !m.laneWise(lane0, types) {
		return laneLoop{}, false
	}
	for v := int64(0); v < count/lanes; v++ {
		if mentionsName(body, laneVectorName(acc, v)) || mentionsName(body, laneVectorName(acc, v)+"_x") {
			return laneLoop{}, false
		}
	}
	for _, name := range m.scalars {
		if mentionsName(body, name+"_v") {
			return laneLoop{}, false
		}
	}
	for k := range m.constants {
		if mentionsName(body, m.constantName(k)) {
			return laneLoop{}, false
		}
	}
	return laneLoop{mapLoop: m, acc: acc, count: count, vectors: count / lanes, value: lane0}, true
}

// accumulatorRead reports `acc[k]` at the constant index k.
func accumulatorRead(e ast.Expression, acc string, k int64) bool {
	index, isIndex := e.(*ast.IndexExpression)
	if !isIndex || index.Dot || !isName(index.Left, acc) {
		return false
	}
	at, isConst := constantValue(index.Index)
	return isConst && at == k
}

// shiftedBy reports that shifted is base with every read at the loop's
// index moved by k: the same expression tree, the index of each element
// read `i + c` against `i + c + k`.
func shiftedBy(base, shifted ast.Expression, idx string, k int64) bool {
	switch b := base.(type) {
	case *ast.IndexExpression:
		s, isIndex := shifted.(*ast.IndexExpression)
		if !isIndex || b.Dot != s.Dot || b.Left.String() != s.Left.String() {
			return false
		}
		offsetB, okB := indexOffset(b.Index, idx)
		offsetS, okS := indexOffset(s.Index, idx)
		return okB && okS && offsetB+k == offsetS
	case *ast.InfixExpression:
		s, isInfix := shifted.(*ast.InfixExpression)
		return isInfix && b.Operator == s.Operator && shiftedBy(b.Left, s.Left, idx, k) && shiftedBy(b.Right, s.Right, idx, k)
	case *ast.PrefixExpression:
		s, isPrefix := shifted.(*ast.PrefixExpression)
		return isPrefix && b.Operator == s.Operator && shiftedBy(b.Right, s.Right, idx, k)
	}
	return base.String() == shifted.String()
}

// indexOffset reads an index `i` or `i + c` over the loop's index i.
func indexOffset(e ast.Expression, idx string) (int64, bool) {
	if isName(e, idx) {
		return 0, true
	}
	sum, isSum := e.(*ast.InfixExpression)
	if !isSum || sum.Operator != "+" || !isName(sum.Left, idx) {
		return 0, false
	}
	return constantValue(sum.Right)
}

// vectorizedLanes spells the rewrite for one recognized loop.
func vectorizedLanes(l laneLoop) []ast.Statement {
	m := l.mapLoop
	tok := m.loop.Token
	ident := func(name string) *ast.Identifier { return &ast.Identifier{Token: tok, Value: name} }
	literal := func(v int64) ast.Expression { return &ast.IntegerLiteral{Token: tok, Value: v} }
	u32 := func(v int64) ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("u32"), Arguments: []ast.Expression{literal(v)}}
	}
	infix := func(left ast.Expression, op string, right ast.Expression) ast.Expression {
		return &ast.InfixExpression{Token: token.Token{Line: tok.Line, Literal: op}, Left: left, Operator: op, Right: right}
	}
	simd := func(member string, args ...ast.Expression) ast.Expression {
		callee := &ast.IndexExpression{Token: tok, Left: ident("simd"), Index: ident(member + "_" + m.suffix), Dot: true}
		return &ast.InvocationExpression{Token: tok, Function: callee, Arguments: args}
	}
	vecType := func() ast.Expression { return ident(m.vecType) }
	element := func(k int64) ast.Expression {
		at := token.Token{SemanticContext: rewriteContext, Line: tok.Line, Column: int(k) + 1, Literal: "["}
		markRewriteProven(at)
		return &ast.IndexExpression{Token: at, Left: ident(l.acc), Index: literal(k)}
	}
	var out []ast.Statement
	for _, s := range m.scalars {
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: ident(s + "_v"), Type: vecType(), Value: simd("splat", ident(s))})
	}
	for k, c := range m.constants {
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: ident(m.constantName(k)), Type: vecType(), Value: simd("splat", c.arg)})
	}
	// The vectors gathered from the accumulators: a splat of the first
	// lane, the rest inserted.
	for v := int64(0); v < l.vectors; v++ {
		first := v * m.lanes
		var gathered ast.Expression = simd("splat", element(first))
		for lane := int64(1); lane < m.lanes; lane++ {
			gathered = simd("insert", gathered, u32(lane), element(first+lane))
		}
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: ident(laneVectorName(l.acc, v)), Type: vecType(), Value: gathered})
	}
	main := &ast.WhileStatement{Token: tok, Condition: m.loop.Condition, Body: &ast.BlockStatement{Token: tok}}
	for v := int64(0); v < l.vectors; v++ {
		// Lane 0's expression with every read at the vector's first lane:
		// the loads then read the vector's block (vectorExprAt).
		var at ast.Expression = ident(m.idx)
		if v > 0 {
			at = infix(ident(m.idx), "+", u32(v*m.lanes))
		}
		name := laneVectorName(l.acc, v)
		var value ast.Expression
		if square, isSquare := l.value.(*ast.InfixExpression); isSquare && square.Left.String() == square.Right.String() {
			// `a[i] * a[i]`: the block loaded once, multiplied by itself.
			op, _ := laneWiseOp(square.Operator, m.elem)
			once := laneVectorName(l.acc, v) + "_x"
			main.Body.Statements = append(main.Body.Statements, &ast.VariableDeclaration{Token: tok, Name: ident(once), Type: vecType(), Value: m.vectorExprAt(square.Left, tok, at)})
			value = simd(op, ident(once), ident(once))
		} else {
			value = m.vectorExprAt(l.value, tok, at)
		}
		main.Body.Statements = append(main.Body.Statements, &ast.AssignmentStatement{Token: tok, Name: ident(name), Value: simd("add", ident(name), value)})
	}
	main.Body.Statements = append(main.Body.Statements, m.loop.Body.Statements[l.count])
	out = append(out, main)
	// The lanes back into the accumulators, before the remainder loop
	// and whatever reads them.
	for k := int64(0); k < l.count; k++ {
		out = append(out, &ast.IndexAssignmentStatement{Token: tok, Target: element(k).(*ast.IndexExpression), Value: simd("extract", ident(laneVectorName(l.acc, k/m.lanes)), u32(k%m.lanes))})
	}
	return out
}
