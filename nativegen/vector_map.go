package nativegen

import (
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Verified map vectorization (docs/spec/94-assembler.md §9 "Map
// vectorization"; docs/notes/optimizer-search-2026-09.md Phase D item 24;
// spec/lean/Oak/Map.lean blocked_eq). An element-wise map over spans,
//
//	while i < len(a) { dst[i] = E(a[i]); i = i + u32(1) }
//
// — E built from the element, loop-invariant scalars, and constants with
// the lane-wise integer operators (+, -, &, |, ^); dst and a span
// parameters of one integer element width, u32 or u64; either one span in
// place or two under an enclosing `len(dst) == len(a)` — is rewritten,
// before lowering, into a main loop over one vector a trip under the
// slack guard the vector kernels spell, and the remainder loop as written:
//
//	k_v: simd.U32x4 = simd.splat_u32x4(k)
//	while len(a) >= u32(4) && i <= len(a) - u32(4) {
//	  simd.store_u32x4(dst, i, simd.add_u32x4(simd.load_u32x4(a, i), k_v))
//	  i = i + u32(4)
//	}
//	while i < len(a) { dst[i] = a[i] + k; i = i + u32(1) }
//
// The rewrite is the theorem: each simd operation is lane-wise by its
// specification (docs/spec/93-simd.md §1: `load` reads consecutive
// elements, `add`/`sub` wrap per lane as the scalar operators do,
// docs/spec/20-types.md, `store` writes consecutive elements), so the
// vector store writes E(a[i + k]) to dst[i + k] for each lane k, and the
// blocked map equals the element-wise map (Oak.Map.blocked_eq). No law of
// the element type is used — unlike the reduction, nothing reassociates —
// which is why the rewrite needs no fact of the body. The lowering sees
// the rewritten body and the verifier proves the assembly against it, the
// two loops coupled inductively with the span memory of dst (§9 "Span
// memories through loops", the split that proves store loops). One
// vector a trip, not four: a map carries nothing across trips, so there
// is no chain to break.
//
// Not rewritten: a map whose value reads any other element (dst[i], a[j])
// or a non-invariant scalar, one over spans bound in the body rather
// than parameters, one over spans of different widths or without the
// equal-length guard, a float or narrow lane, a multiplication or shift
// (not in this increment), and the remainder loop of a map this rewrite
// made.

// mapLoop is a recognized `while i < len(src) { dst[i] = E; i = i + u32(1) }`.
type mapLoop struct {
	loop          *ast.WhileStatement
	idx, src, dst string
	elem          scalar
	suffix        string // the simd operations' suffix, `u32x4` or `u64x2`
	lanes         int64
	value         ast.Expression
	// scalars are the invariant scalars the value reads, first use first;
	// constants the constants, likewise. Each gets one splat before the
	// main loop.
	scalars   []string
	constants []int64
}

// laneWiseOps maps the operators the rewrite vectorizes to their simd
// operations, each lane-wise by docs/spec/93-simd.md §1.
var laneWiseOps = map[string]string{"+": "add", "-": "sub", "&": "and", "|": "or", "^": "xor"}

// vectorizeMaps returns the body with its element-wise span maps
// vectorized, and whether any was.
func vectorizeMaps(fn *ast.FunctionStatement, body ast.Expression) (ast.Expression, bool) {
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
	var rewrite func(stmts []ast.Statement, equal map[string]string) []ast.Statement
	rewrite = func(stmts []ast.Statement, equal map[string]string) []ast.Statement {
		var out []ast.Statement
		var prev ast.Statement
		for _, stmt := range stmts {
			switch s := stmt.(type) {
			case *ast.WhileStatement:
				if m, ok := recognizeMap(s, prev, types, spans, equal, body); ok {
					out = append(out, vectorizedMap(m)...)
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
	// Rewrite a copy: the source body stays the typechecker's.
	clone := cloneNode(body).(*ast.BlockExpression)
	clone.Block.Statements = rewrite(clone.Block.Statements, nil)
	if !changed {
		return body, false
	}
	return clone, true
}

// armFacts extends the equal-length facts with the one a conditional's
// true arm holds: `len(x) == len(y) ? { ... }` — the condition sugar's
// first arm, its pattern the literal true (parser.go,
// parseConditionSugarArms).
func armFacts(match *ast.MatchExpression, arm *ast.MatchArm, equal map[string]string) map[string]string {
	lit, isLit := arm.Pattern.(*ast.LiteralPattern)
	if !isLit {
		return equal
	}
	b, isBool := lit.Value.(*ast.Boolean)
	if !isBool || !b.Value {
		return equal
	}
	cond, isInfix := match.Scrutinee.(*ast.InfixExpression)
	if !isInfix || cond.Operator != "==" {
		return equal
	}
	x, okX := lenOf(cond.Left)
	y, okY := lenOf(cond.Right)
	if !okX || !okY || x == y {
		return equal
	}
	out := map[string]string{}
	for k, v := range equal {
		out[k] = v
	}
	out[x], out[y] = y, x
	return out
}

// recognizeMap reads a while statement as an element-wise map over span
// parameters; prev is the statement before it, equal the spans known to
// have the same length where it stands.
func recognizeMap(loop *ast.WhileStatement, prev ast.Statement, types map[string]ast.Expression, spans map[string]span, equal map[string]string, body ast.Expression) (mapLoop, bool) {
	cond, isInfix := loop.Condition.(*ast.InfixExpression)
	if !isInfix || cond.Operator != "<" || loop.Body == nil || len(loop.Body.Statements) != 2 {
		return mapLoop{}, false
	}
	idx, isIdent := cond.Left.(*ast.Identifier)
	if !isIdent {
		return mapLoop{}, false
	}
	src, isLen := lenOf(cond.Right)
	if !isLen {
		return mapLoop{}, false
	}
	store, isStore := loop.Body.Statements[0].(*ast.IndexAssignmentStatement)
	step, isStep := loop.Body.Statements[1].(*ast.AssignmentStatement)
	if !isStore || !isStep || store.Target == nil || step.Name == nil || step.Name.Value != idx.Value {
		return mapLoop{}, false
	}
	if store.Target.Dot || !isName(store.Target.Index, idx.Value) {
		return mapLoop{}, false
	}
	dstIdent, isIdent := store.Target.Left.(*ast.Identifier)
	if !isIdent {
		return mapLoop{}, false
	}
	dst := dstIdent.Value
	// i = i + 1, the index a u32.
	inc, isInc := step.Value.(*ast.InfixExpression)
	if !isInc || inc.Operator != "+" || !isName(inc.Left, idx.Value) {
		return mapLoop{}, false
	}
	if one, isConst := constantValue(inc.Right); !isConst || one != 1 {
		return mapLoop{}, false
	}
	if idxType, declared := types[idx.Value]; !declared || idxType.String() != "u32" {
		return mapLoop{}, false
	}
	// The spans: parameters of one integer element width, dst writable,
	// one span or two of equal length.
	d, hasDst := spans[dst]
	s, hasSrc := spans[src]
	if !hasDst || !hasSrc || !d.writable || d.elemLayout != nil || s.elemLayout != nil || d.elem.name != s.elem.name {
		return mapLoop{}, false
	}
	if dst != src && equal[dst] != src {
		return mapLoop{}, false
	}
	suffix, lanes, ok := vectorShapeFor(&ast.Identifier{Value: d.elem.name})
	if !ok {
		return mapLoop{}, false
	}
	m := mapLoop{loop: loop, idx: idx.Value, src: src, dst: dst, elem: d.elem, suffix: suffix, lanes: lanes, value: store.Value}
	if !m.laneWise(store.Value, types) {
		return mapLoop{}, false
	}
	// Fresh names for the splats.
	for _, name := range m.scalars {
		if mentionsName(body, name+"_v") {
			return mapLoop{}, false
		}
	}
	for k := range m.constants {
		if mentionsName(body, m.constantName(k)) {
			return mapLoop{}, false
		}
	}
	// Not the remainder loop of a map this rewrite made: that follows a
	// loop under the slack guard over the same span and index.
	if prevLoop, isLoop := prev.(*ast.WhileStatement); isLoop {
		for _, fact := range loopFactsOf(prevLoop.Condition) {
			if fact.span == src && fact.index == idx.Value && fact.slack == lanes {
				return mapLoop{}, false
			}
		}
	}
	return m, true
}

// laneWise reads the stored value as a lane-wise expression over the
// element, recording the invariant scalars and constants it reads.
func (m *mapLoop) laneWise(e ast.Expression, types map[string]ast.Expression) bool {
	switch x := e.(type) {
	case *ast.IndexExpression:
		return isElement(x, m.src, m.idx)
	case *ast.Identifier:
		if x.Value == m.idx || x.Value == m.src || x.Value == m.dst {
			return false
		}
		if t, declared := types[x.Value]; !declared || t.String() != m.elem.name {
			return false
		}
		for _, s := range m.scalars {
			if s == x.Value {
				return true
			}
		}
		m.scalars = append(m.scalars, x.Value)
		return true
	case *ast.InfixExpression:
		if _, ok := laneWiseOps[x.Operator]; !ok {
			return false
		}
		return m.laneWise(x.Left, types) && m.laneWise(x.Right, types)
	}
	// A constant of the element type (the typechecker's), `u32(3)`: the
	// value is what is splatted.
	v, isConst := constantValue(e)
	if !isConst || v < 0 {
		return false
	}
	for _, c := range m.constants {
		if c == v {
			return true
		}
	}
	m.constants = append(m.constants, v)
	return true
}

func (m mapLoop) constantName(k int) string { return m.dst + "_c" + strconv.Itoa(k) }

// vectorizedMap spells the rewrite for one recognized loop.
func vectorizedMap(m mapLoop) []ast.Statement {
	tok := m.loop.Token
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
		callee := &ast.IndexExpression{Token: tok, Left: ident("simd"), Index: ident(member + "_" + m.suffix), Dot: true}
		return &ast.InvocationExpression{Token: tok, Function: callee, Arguments: args}
	}
	vecType := func() ast.Expression {
		if m.suffix == "u32x4" {
			return ident("simd.U32x4")
		}
		return ident("simd.U64x2")
	}
	length := func() ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("len"), Arguments: []ast.Expression{ident(m.src)}}
	}
	var vector func(e ast.Expression) ast.Expression
	vector = func(e ast.Expression) ast.Expression {
		switch x := e.(type) {
		case *ast.IndexExpression:
			return simd("load", ident(m.src), ident(m.idx))
		case *ast.Identifier:
			return ident(x.Value + "_v")
		case *ast.InfixExpression:
			return simd(laneWiseOps[x.Operator], vector(x.Left), vector(x.Right))
		}
		v, _ := constantValue(e)
		for k, c := range m.constants {
			if c == v {
				return ident(m.constantName(k))
			}
		}
		return e
	}
	var out []ast.Statement
	for _, s := range m.scalars {
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: ident(s + "_v"), Type: vecType(), Value: simd("splat", ident(s))})
	}
	for k, c := range m.constants {
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: ident(m.constantName(k)), Type: vecType(), Value: simd("splat", typed(m.elem.name, c))})
	}
	guard := infix(infix(length(), ">=", u32(m.lanes)), "&&", infix(ident(m.idx), "<=", infix(length(), "-", u32(m.lanes))))
	main := &ast.WhileStatement{Token: tok, Condition: guard, Body: &ast.BlockStatement{Token: tok}}
	main.Body.Statements = append(main.Body.Statements,
		&ast.ExpressionStatement{Token: tok, Expression: simd("store", ident(m.dst), ident(m.idx), vector(m.value))},
		&ast.AssignmentStatement{Token: tok, Name: ident(m.idx), Value: infix(ident(m.idx), "+", u32(m.lanes))},
	)
	return append(out, main, m.loop)
}
