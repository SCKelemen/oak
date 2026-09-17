package nativegen

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// Scalar blocked fills (docs/spec/94-assembler.md §9 "Scalar blocked
// fills"; Oak.BlockedFill.blocked_fill_eq). A checked u64 zero-fill loop
//
//	while i < bound {
//	  dst[f(i)] = u64(0)
//	  i = i + u32(1)
//	}
//
// becomes a four-word main loop and the original scalar remainder. The four
// stores remain scalar and in source order: this optimization deliberately
// claims no authority for STP through a span, whose use additionally needs
// private, unpublished ordinary-memory custody.
type fillLoop struct {
	loop    *ast.WhileStatement
	idx     string
	bound   ast.Expression
	address *ast.VariableDeclaration
	store   *ast.IndexAssignmentStatement
	idxTyp  ast.Expression
}

// fillBlockIndex is private rewrite provenance for one of the four scalar
// stores made by unrolledFill. It is never authority at the assembler seam:
// the generator may use it to spell one shared slack guard, but asm.Check must
// still derive every store's bound from that guard and the emitted adds.
type fillBlockIndex struct {
	group  string
	offset int64
	width  int64
}

var fillBlockIndices = map[token.Token]fillBlockIndex{}

func markFillBlockIndex(tok token.Token, info fillBlockIndex) {
	rewriteProvenMu.Lock()
	fillBlockIndices[tok] = info
	rewriteProvenMu.Unlock()
}

func rewriteFillBlockIndex(tok token.Token) (fillBlockIndex, bool) {
	if tok.SemanticContext != rewriteContext {
		return fillBlockIndex{}, false
	}
	rewriteProvenMu.Lock()
	defer rewriteProvenMu.Unlock()
	info, ok := fillBlockIndices[tok]
	return info, ok
}

// unrollFills returns a copy of body with every admitted scalar zero fill
// blocked four ways. The checked source tree is never mutated.
func unrollFills(fn *ast.FunctionStatement, body ast.Expression, tc *typechecker.TypeChecker, constants map[string]asm.Constant) (ast.Expression, bool) {
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil || fn == nil || tc == nil {
		return body, false
	}
	types := declaredScalarTypes(block.Block.Statements)
	allowed := make(map[string]bool, len(types)+len(fn.Parameters)+len(constants))
	foldedConstants := make(map[string]asm.Constant, len(constants))
	for name, constant := range constants {
		foldedConstants[name] = constant
	}
	for name := range types {
		allowed[name] = true
		delete(foldedConstants, name)
	}
	for _, parameter := range fn.Parameters {
		if parameter != nil && parameter.Name != nil {
			allowed[parameter.Name.Value] = true
			delete(foldedConstants, parameter.Name.Value)
		}
	}
	for name := range constants {
		allowed[name] = true
	}
	names := newFillNames(body)
	changed := false
	var rewrite func([]ast.Statement) []ast.Statement
	rewrite = func(stmts []ast.Statement) []ast.Statement {
		out := make([]ast.Statement, 0, len(stmts))
		for _, stmt := range stmts {
			switch s := stmt.(type) {
			case *ast.WhileStatement:
				if fill, ok := recognizeFill(s, types, allowed, tc); ok {
					if bound, known := constantFillBound(fill.bound, foldedConstants); known && bound < 4 {
						break
					}
					out = append(out, unrolledFill(fill, names, foldedConstants)...)
					changed = true
					continue
				}
				if s.Body != nil {
					s.Body.Statements = rewrite(s.Body.Statements)
				}
			case *ast.ExpressionStatement:
				if inner, ok := s.Expression.(*ast.BlockExpression); ok && inner.Block != nil {
					inner.Block.Statements = rewrite(inner.Block.Statements)
				}
				if match, ok := s.Expression.(*ast.MatchExpression); ok {
					for _, arm := range match.Arms {
						if inner, ok := arm.Body.(*ast.BlockExpression); ok && inner.Block != nil {
							inner.Block.Statements = rewrite(inner.Block.Statements)
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

// constantFillBound reads only the compiler's checked u32 constants (or a
// literal that exactly fits u32). It is used to remove the main loop's
// otherwise repeated underflow guard, never as memory-bound authority.
func constantFillBound(expr ast.Expression, constants map[string]asm.Constant) (uint64, bool) {
	const maxU32 = uint64(1<<32 - 1)
	if value, isConstant := constantValue(expr); isConstant && value >= 0 && uint64(value) <= maxU32 {
		return uint64(value), true
	}
	name, isName := expr.(*ast.Identifier)
	if !isName {
		return 0, false
	}
	value, known := constants[name.Value]
	return value.Value, known && value.Type == "u32" && value.Value <= maxU32
}

func recognizeFill(loop *ast.WhileStatement, types map[string]ast.Expression, allowed map[string]bool, tc *typechecker.TypeChecker) (fillLoop, bool) {
	cond, ok := loop.Condition.(*ast.InfixExpression)
	if !ok || cond.Operator != "<" || loop.Body == nil || (len(loop.Body.Statements) != 2 && len(loop.Body.Statements) != 3) {
		return fillLoop{}, false
	}
	idx, ok := cond.Left.(*ast.Identifier)
	if !ok || mentionsName(cond.Right, idx.Value) {
		return fillLoop{}, false
	}
	idxTyp, declared := types[idx.Value]
	if !declared || idxTyp.String() != "u32" {
		return fillLoop{}, false
	}
	last := len(loop.Body.Statements) - 1
	storeAt := last - 1
	store, isStore := loop.Body.Statements[storeAt].(*ast.IndexAssignmentStatement)
	step, isStep := loop.Body.Statements[last].(*ast.AssignmentStatement)
	if !isStore || !isStep || store.Target == nil || step.Name == nil || step.Name.Value != idx.Value {
		return fillLoop{}, false
	}
	boundNames := make(map[string]bool, len(allowed)+1)
	for name, admitted := range allowed {
		boundNames[name] = admitted
	}
	var address *ast.VariableDeclaration
	indexName := idx.Value
	if storeAt == 1 {
		decl, isDecl := loop.Body.Statements[0].(*ast.VariableDeclaration)
		if !isDecl || decl.Name == nil || decl.Type == nil || decl.Value == nil {
			return fillLoop{}, false
		}
		// declaredScalarTypes sees the whole function; the address binding is
		// not available to its own initializer.
		delete(boundNames, decl.Name.Value)
		if decl.Type.String() != "u32" || boundNames[decl.Name.Value] || !pureFillExpr(decl.Value, boundNames) || !unitStrideAddress(decl.Value, idx.Value) {
			return fillLoop{}, false
		}
		valueToken, positioned := ast.ExpressionToken(decl.Value)
		valueType, checked := tc.ExpressionTypeAt(valueToken)
		if !positioned || !checked || valueType == nil || valueType.String() != decl.Type.String() {
			return fillLoop{}, false
		}
		address = decl
		indexName = decl.Name.Value
	}
	if mentionsName(store.Target.Left, idx.Value) || (address != nil && mentionsName(store.Target.Left, address.Name.Value)) || !isName(store.Target.Index, indexName) {
		return fillLoop{}, false
	}
	value, isZero := constantValue(store.Value)
	if !isZero || value != 0 || !fillTargetPure(store.Target) {
		return fillLoop{}, false
	}
	valueToken, positioned := ast.ExpressionToken(store.Value)
	typ, checked := tc.ExpressionTypeAt(valueToken)
	if !positioned || !checked || typ == nil || typ.String() != "u64" {
		return fillLoop{}, false
	}
	inc, isInc := step.Value.(*ast.InfixExpression)
	if !isInc || inc.Operator != "+" || !isName(inc.Left, idx.Value) {
		return fillLoop{}, false
	}
	one, isOne := constantValue(inc.Right)
	if !isOne || one != 1 {
		return fillLoop{}, false
	}
	return fillLoop{loop: loop, idx: idx.Value, bound: cond.Right, address: address, store: store, idxTyp: idxTyp}, true
}

// unitStrideAddress recognizes the one affine address spelling produced by
// source-level helper expansion. Blocking may amortize the test only when
// consecutive induction values denote consecutive word indexes.
func unitStrideAddress(expr ast.Expression, idx string) bool {
	add, ok := expr.(*ast.InfixExpression)
	if !ok || add.Operator != "+" {
		return false
	}
	if isName(add.Left, idx) {
		return !mentionsName(add.Right, idx)
	}
	if isName(add.Right, idx) {
		return !mentionsName(add.Left, idx)
	}
	return false
}

func integerFillType(typ ast.Expression) bool {
	scalar, ok := scalarOf(typ)
	return ok && !scalar.isBool && !scalar.isFloat && !scalar.isVec
}

// pureFillExpr is the closed arithmetic vocabulary admitted in an inlined
// address prelude. In particular, no call, memory read, or control flow can
// be multiplied by blocking the loop.
func pureFillExpr(expr ast.Expression, allowed map[string]bool) bool {
	switch e := expr.(type) {
	case *ast.Identifier:
		return allowed[e.Value]
	case *ast.IntegerLiteral:
		return true
	case *ast.PrefixExpression:
		return pureFillExpr(e.Right, allowed)
	case *ast.InfixExpression:
		return pureFillExpr(e.Left, allowed) && pureFillExpr(e.Right, allowed)
	case *ast.InvocationExpression:
		name, named := e.Function.(*ast.Identifier)
		if !named || len(e.Arguments) != 1 || !integerFillType(name) {
			return false
		}
		return pureFillExpr(e.Arguments[0], allowed)
	default:
		return false
	}
}

// fillTargetPure excludes a call hidden in address computation. Casts are
// admitted because helper expansion leaves u32(idx) in the OS page-table
// index; every other invocation could carry effects or trap differently when
// loop tests are amortized.
func fillTargetPure(target *ast.IndexExpression) bool {
	pure := true
	walk(target, func(node ast.Node) {
		call, ok := node.(*ast.InvocationExpression)
		if !ok {
			return
		}
		name, named := call.Function.(*ast.Identifier)
		if !named || len(call.Arguments) != 1 {
			pure = false
			return
		}
		if _, scalar := scalars[name.Value]; !scalar {
			pure = false
		}
	})
	return pure
}

type fillNames struct {
	used map[string]bool
	next int
}

func newFillNames(body ast.Expression) *fillNames {
	names := &fillNames{used: map[string]bool{}}
	walk(body, func(node ast.Node) {
		if id, ok := node.(*ast.Identifier); ok {
			names.used[id.Value] = true
		}
	})
	return names
}

func (names *fillNames) fresh(base string) string {
	for {
		candidate := fmt.Sprintf("%s_fill%d", base, names.next)
		names.next++
		if !names.used[candidate] {
			names.used[candidate] = true
			return candidate
		}
	}
}

func unrolledFill(fill fillLoop, names *fillNames, constants map[string]asm.Constant) []ast.Statement {
	tok := fill.loop.Token
	ident := func(name string) *ast.Identifier { return &ast.Identifier{Token: tok, Value: name} }
	literal := func(value int64) ast.Expression {
		return &ast.IntegerLiteral{Token: token.Token{SemanticContext: rewriteContext, Line: tok.Line, Literal: fmt.Sprint(value)}, Value: value}
	}
	u32 := func(value int64) ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("u32"), Arguments: []ast.Expression{literal(value)}}
	}
	infix := func(left ast.Expression, op string, right ast.Expression) ast.Expression {
		return &ast.InfixExpression{Token: token.Token{Line: tok.Line, Literal: op}, Left: left, Operator: op, Right: right}
	}
	condition := infix(
		infix(cloneNode(fill.bound).(ast.Expression), ">=", u32(4)),
		"&&",
		infix(ident(fill.idx), "<=", infix(cloneNode(fill.bound).(ast.Expression), "-", u32(4))),
	)
	if bound, known := constantFillBound(fill.bound, constants); known {
		condition = infix(ident(fill.idx), "<=", u32(int64(bound-4)))
	}
	main := &ast.WhileStatement{Token: tok, Condition: condition, Body: &ast.BlockStatement{Token: tok}}
	spanName := ""
	if _, alreadyNamed := fill.store.Target.Left.(*ast.Identifier); !alreadyNamed {
		spanName = names.fresh("__oak_fill_span")
		spanType := &ast.IndexExpression{
			Token: token.Token{SemanticContext: rewriteContext, Line: tok.Line, Literal: "["},
			Left:  ident("u64"),
			Index: ident("*"),
		}
		borrow := &ast.PrefixExpression{
			Token:    token.Token{SemanticContext: rewriteContext, Line: tok.Line, Literal: "&"},
			Operator: "&",
			Right:    cloneNode(fill.store.Target.Left).(ast.Expression),
		}
		main.Body.Statements = append(main.Body.Statements, &ast.VariableDeclaration{
			Token: token.Token{SemanticContext: rewriteContext, Line: tok.Line, Literal: spanName},
			Name:  ident(spanName),
			Type:  spanType,
			Value: &ast.InvocationExpression{
				Token:     token.Token{SemanticContext: rewriteContext, Line: tok.Line, Literal: "span"},
				Function:  ident("span"),
				Arguments: []ast.Expression{borrow},
			},
		})
	}
	indexName := fill.idx
	if fill.address != nil {
		address := cloneNode(fill.address).(*ast.VariableDeclaration)
		fresh := names.fresh(fill.address.Name.Value)
		address.Name.Value = fresh
		indexName = fresh
		main.Body.Statements = append(main.Body.Statements, address)
	}
	group := names.fresh("__oak_fill_group")
	for offset := int64(0); offset < 4; offset++ {
		var index ast.Expression = ident(indexName)
		if offset != 0 {
			index = infix(ident(indexName), "+", u32(offset))
		}
		store := cloneNode(fill.store).(*ast.IndexAssignmentStatement)
		if spanName != "" {
			store.Target.Left = ident(spanName)
		}
		originalIndex := fill.idx
		if fill.address != nil {
			originalIndex = fill.address.Name.Value
		}
		substituteBound(store.Target, map[string]ast.Expression{originalIndex: index})
		store.Target.Token.SemanticContext = rewriteContext
		store.Target.Token.Column += int(offset) + 1
		markFillBlockIndex(store.Target.Token, fillBlockIndex{group: group, offset: offset, width: 4})
		main.Body.Statements = append(main.Body.Statements, store)
	}
	main.Body.Statements = append(main.Body.Statements, &ast.AssignmentStatement{
		Token: tok,
		Name:  ident(fill.idx),
		Value: infix(ident(fill.idx), "+", u32(4)),
	})
	return []ast.Statement{main, fill.loop}
}
