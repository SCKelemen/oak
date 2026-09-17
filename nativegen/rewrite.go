package nativegen

// Layer A of the optimization system (docs/spec/90-backend.md §16,
// docs/spec/94-assembler.md §9.ag): rewrites of the checked Oak body, done
// once for every lane before the lowering. Each rewrite carries its
// obligation. A *decided* rewrite proves, per site, that the new
// expression equals the old on every input, with the bit-level decider
// (asm.DecideTheoremWith) over the site's free variables; a site the
// decider cannot prove is left as written. A *law-backed* rewrite is a
// schema proved once in Lean and instantiated by a matcher (the reduction
// unrolling under Oak.Reduction.unrolled4_eq; helper expansion as
// substitution). The lowering lowers the rewritten body and the verifier
// judges the machine code against it, so the chain from source to
// instructions is: source equals rewritten body (layer A's obligations),
// rewritten body equals instructions (layer B's verifier). The compiler
// reports every site with its obligation.

import (
	"fmt"
	"math/bits"
	"sync"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// RewriteSite is one application of a layer-A rewrite in a body.
type RewriteSite struct {
	Rewrite string // "helper expansion", "reduction unrolling", "strength reduction"
	Law     string // the Lean law of a law-backed rewrite, or "" when decided per site
	Decided bool   // proven per site by the bit-level decider
	Detail  string // the decider's message, or what the law says
	Line    int
}

// RewriteSites reports the layer-A rewrites a lowering applied to a body.
func RewriteSites(fn *asm.Function) []RewriteSite { return rewriteSitesOf[fn] }

var rewriteSitesOf = map[*asm.Function][]RewriteSite{}

// Unrolled reports how many reductions layer A unrolled in a body (the
// unroll transform's count).
func Unrolled(fn *asm.Function) int { return countSites(fn, "reduction unrolling", false) }

// Vectorized reports how many reductions a lowering vectorized under
// Lane.VectorReductions (nativegen/vector_reduction.go).
func Vectorized(fn *asm.Function) int { return countSites(fn, "reduction vectorization", false) }

// VectorizedMaps reports how many bodies' element-wise maps a lowering
// vectorized under Lane.VectorMaps (nativegen/vector_map.go).
func VectorizedMaps(fn *asm.Function) int { return countSites(fn, "map vectorization", false) }

// UnrolledMaps counts maps processed as two consecutive vectors per trip.
func UnrolledMaps(fn *asm.Function) int { return countSites(fn, "map unrolling", false) }

// VectorizedFolds reports how many bodies' lane-wise float reductions a
// lowering vectorized under Lane.VectorFolds (nativegen/vector_fold.go).
func VectorizedFolds(fn *asm.Function) int { return countSites(fn, "fold vectorization", false) }

// UnrolledConstant reports how many constant-trip loops a lowering
// unrolled under Lane.UnrollConstant (nativegen/unroll_constant.go).
func UnrolledConstant(fn *asm.Function) int { return countSites(fn, "constant unrolling", false) }

// StrengthReduced reports how many sites layer A strength-reduced in a
// body, each decided at the bit level (the strength transform's count,
// beside the emitter's own).
func StrengthReduced(fn *asm.Function) int { return countSites(fn, "strength reduction", true) }

func countSites(fn *asm.Function, rewrite string, decidedOnly bool) int {
	n := 0
	for _, s := range rewriteSitesOf[fn] {
		if s.Rewrite == rewrite && (!decidedOnly || s.Decided) {
			n++
		}
	}
	return n
}

// stageKey memoizes rewriteStages per source function and switches: the
// candidate search lowers a body under several configurations, and the
// per-site theorems are proved once, not once per candidate.
type stageKey struct {
	fn                                                                     *ast.FunctionStatement
	tc                                                                     *typechecker.TypeChecker
	expand, unroll, vectorize, maps, unrollMaps, folds, constant, strength bool
}

var (
	stagesMu   sync.Mutex
	stagesMemo = map[stageKey][]rewriteStage{}
)

// rewriteStage is a body to lower with the rewrites applied so far.
type rewriteStage struct {
	body  ast.Expression
	sites []RewriteSite
	// judged marks a stage whose body the verifier must judge in place of
	// the source: a rewrite beyond substitution changed what the
	// instructions compute the same value from.
	judged bool
}

// rewriteStages returns the bodies to try lowering, the most rewritten
// first and the source last: a lowering the rewritten shape makes
// unsupported falls back to the shape before it.
func rewriteStages(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, tc *typechecker.TypeChecker, expand, unroll, vectorize, maps, unrollMaps, folds, constant, strength bool) []rewriteStage {
	key := stageKey{fn: fn, tc: tc, expand: expand, unroll: unroll, vectorize: vectorize, maps: maps, unrollMaps: unrollMaps, folds: folds, constant: constant, strength: strength}
	stagesMu.Lock()
	memo, seen := stagesMemo[key]
	stagesMu.Unlock()
	if seen {
		return memo
	}
	stages := computeStages(fn, functions, tc, expand, unroll, vectorize, maps, unrollMaps, folds, constant, strength)
	stagesMu.Lock()
	stagesMemo[key] = stages
	stagesMu.Unlock()
	return stages
}

func computeStages(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, tc *typechecker.TypeChecker, expand, unroll, vectorize, maps, unrollMaps, folds, constant, strength bool) []rewriteStage {
	var stages []rewriteStage
	var sites []RewriteSite
	body := fn.Body
	// judged: a stage is the verifier's reference once a rewrite beyond
	// substitution changed what the instructions compute the same value
	// from; an expansion alone leaves the source as the reference (the
	// verifier takes callees at their bodies).
	judged := false
	push := func() {
		copied := append([]RewriteSite(nil), sites...)
		stages = append([]rewriteStage{{body: body, sites: copied, judged: judged}}, stages...)
	}
	if expand {
		if inlined := inlineBody(fn, functions); inlined != body {
			sites = append(sites, RewriteSite{Rewrite: "helper expansion", Law: "substitution", Detail: "the callee's body in place of the call, its parameters bound to the arguments", Line: fn.Token.Line})
			body = inlined
			push()
		}
	}
	// Single-use span locals fold into the call that uses them
	// (nativegen/span_forward.go): a substitution, so the source stays the
	// verifier's reference.
	if forwarded, changed := forwardSingleUseSpans(cloneNode(body).(ast.Expression)); changed {
		sites = append(sites, RewriteSite{Rewrite: "span forwarding", Law: "Oak.SpanForward.let_forward", Detail: "a span local used once, in the next statement, as a call argument stands for its expression"})
		body = forwarded
		push()
	}
	// The constant-trip loops as their trips (nativegen/unroll_constant.go):
	// the loop from zero is the unrolled sequence, whatever the body.
	if constant {
		if unrolled, changed := unrollConstantLoops(fn, body); changed {
			sites = append(sites, RewriteSite{Rewrite: "constant unrolling", Law: "Oak.ConstantUnroll.loop_eq_unrolled", Detail: "a loop from zero to a literal bound, its index written by its step alone, is its trips in order with the index a literal in each; nothing is assumed of the body", Line: fn.Token.Line})
			body = unrolled
			judged = true
			push()
		}
	}
	// The element-wise maps over spans as one vector a trip
	// (nativegen/vector_map.go): lane-wise semantics alone license it.
	if maps {
		mapSource := body
		if vectorized, changed := vectorizeMaps(fn, mapSource, tc, false); changed {
			sites = append(sites, RewriteSite{Rewrite: "map vectorization", Law: "Oak.Map.blocked_eq", Detail: "each block of a vector's lanes mapped as one vector load, the lane-wise operations, and one vector store, the remainder one element at a time; the simd operations are lane-wise by their specification, so the blocked map is the element-wise map", Line: fn.Token.Line})
			body = vectorized
			judged = true
			push()
			if unrollMaps {
				if grouped, changed := vectorizeMaps(fn, mapSource, tc, true); changed {
					sites = append(sites, RewriteSite{Rewrite: "map unrolling", Law: "Oak.Map.grouped_eq", Detail: "two consecutive vector blocks per trip, preserving each lane's operations and element order; single-vector cleanup and the unchanged scalar remainder", Line: fn.Token.Line})
					body = grouped
					push()
				}
			}
		}
	}
	// The lane-wise float reductions as one vector of element values a
	// trip, the lanes added in order (nativegen/vector_fold.go): lane-wise
	// semantics and the kept order license it.
	if folds {
		if vectorized, changed := vectorizeFolds(fn, body); changed {
			sites = append(sites, RewriteSite{Rewrite: "fold vectorization", Law: "Oak.Fold.blocked_eq", Detail: "each block of a vector's lanes computed as one vector load per span and the lane-wise operations, its lanes added to the accumulator in element order, the remainder one element at a time; the simd operations are lane-wise by their specification and the additions keep their order, so the blocked fold is the sequential fold", Line: fn.Token.Line})
			body = vectorized
			judged = true
			push()
		}
	}
	// The vector form of the reduction (nativegen/vector_reduction.go)
	// takes the loop when asked; the scalar unrolling otherwise.
	if vectorize {
		if vectorized, changed := vectorizeReductions(fn, body); changed {
			sites = append(sites, RewriteSite{Rewrite: "reduction vectorization", Law: "Oak.Reduction.vector16_eq, vector8_eq", Detail: "the lanes of four fixed vectors as sixteen strided accumulators over u32 lanes, eight over u64 ones, the remainder into the scalar; integer addition reassociates at every width", Line: fn.Token.Line})
			body = vectorized
			judged = true
			push()
		}
	}
	if unroll {
		if unrolled, changed := unrollReductions(fn, body); changed {
			sites = append(sites, RewriteSite{Rewrite: "reduction unrolling", Law: "Oak.Reduction.unrolled4_eq", Detail: "the strided four-way fold equals the sequential fold; integer addition reassociates at every width", Line: fn.Token.Line})
			body = unrolled
			judged = true
			push()
		}
	}
	if strength {
		if reduced, applied := strengthReduce(fn, functions, body); reduced != body {
			sites = append(sites, applied...)
			body = reduced
			judged = true
			push()
		} else if len(applied) > 0 && len(stages) > 0 {
			// Every site left as written: reported on the last stage.
			stages[0].sites = append(stages[0].sites, applied...)
		}
	}
	stages = append(stages, rewriteStage{body: fn.Body})
	return stages
}

// strengthReduce rewrites, in a copy of the body, every multiplication,
// unsigned division, and unsigned remainder whose right operand is a
// constant power of two above one into the shift or mask — after the
// bit-level decider proves the site's equality over its free variables.
// Sites the decider does not prove are left as written; every site is
// reported either way.
func strengthReduce(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, body ast.Expression) (ast.Expression, []RewriteSite) {
	if body == nil {
		return body, nil
	}
	// The declared type of every named variable and parameter: scalars
	// for the sites' operands, spans and arrays for the element reads
	// among them.
	types := map[string]ast.Expression{}
	walk(body, func(n ast.Node) {
		if d, isDecl := n.(*ast.VariableDeclaration); isDecl && d.Name != nil && d.Type != nil {
			types[d.Name.Value] = d.Type
		}
	})
	for _, p := range fn.Parameters {
		if p != nil && p.Name != nil && p.Type != nil {
			types[p.Name.Value] = p.Type
		}
	}
	copied := cloneNode(body).(ast.Expression)
	var sites []RewriteSite
	site := 0
	walk(copied, func(n ast.Node) {
		e, isInfix := n.(*ast.InfixExpression)
		if !isInfix || (e.Operator != "*" && e.Operator != "/" && e.Operator != "%") {
			return
		}
		typ, known := scalarTypeIn(e.Left, types)
		if !known || typ.isFloat || typ.isVec || typ.isBool {
			return
		}
		value, isConst := constantValue(e.Right)
		if !isConst || value <= 1 {
			return
		}
		c := uint64(value) & mask64(typ.bits)
		if c <= 1 || c&(c-1) != 0 {
			return
		}
		if (e.Operator == "/" || e.Operator == "%") && typ.signed {
			return
		}
		k := int64(bits.TrailingZeros64(c))
		replacement := &ast.InfixExpression{Token: e.Token, Left: e.Left}
		switch e.Operator {
		case "*":
			replacement.Operator, replacement.Right = "<<", literal(e.Token, k)
		case "/":
			replacement.Operator, replacement.Right = ">>", literal(e.Token, k)
		case "%":
			replacement.Operator, replacement.Right = "&", literal(e.Token, int64(c-1))
		}
		site++
		// The site's theorem over its free variables, an element read
		// abstracted as a fresh parameter of its element type: the read
		// is the same value on both sides, so the equality is of the
		// arithmetic alone.
		abstracted, elems, abstractable := abstractReads(e.Left, types, nil)
		line := e.Token.Line
		if !abstractable {
			sites = append(sites, RewriteSite{Rewrite: "strength reduction", Detail: "left as written: an operand the theorem cannot abstract", Line: line})
			return
		}
		oldAbstract := &ast.InfixExpression{Token: e.Token, Operator: e.Operator, Left: abstracted, Right: e.Right}
		newAbstract := &ast.InfixExpression{Token: e.Token, Operator: replacement.Operator, Left: abstracted, Right: replacement.Right}
		for name, typ := range elems {
			types[name] = typ
		}
		theorem, ok := equalityTheorem(fmt.Sprintf("%s__rewrite_%d", fn.Name.Value, site), oldAbstract, newAbstract, types)
		for name := range elems {
			delete(types, name)
		}
		if !ok {
			sites = append(sites, RewriteSite{Rewrite: "strength reduction", Detail: "left as written: a free variable of the site has no scalar type", Line: line})
			return
		}
		decision := asm.DecideTheoremWith(theorem, functions, nil, asm.Declarations{})
		if decision.Kind != asm.DecisionProven {
			sites = append(sites, RewriteSite{Rewrite: "strength reduction", Detail: "left as written: " + decision.Message, Line: line})
			return
		}
		e.Operator, e.Right = replacement.Operator, replacement.Right
		sites = append(sites, RewriteSite{Rewrite: "strength reduction", Decided: true, Detail: decision.Message, Line: line})
	})
	applied := 0
	for _, s := range sites {
		if s.Decided {
			applied++
		}
	}
	if applied == 0 {
		return body, sites
	}
	return copied, sites
}

// abstractReads rebuilds an operand expression with every element read
// (`v[i]`, a span's or array's element) replaced by a fresh identifier of
// the element type, returning the new expression and the identifiers'
// types; false when the expression has a shape the site theorem does not
// take (a call other than a conversion, a field, a nested read).
func abstractReads(e ast.Expression, types map[string]ast.Expression, elems map[string]ast.Expression) (ast.Expression, map[string]ast.Expression, bool) {
	if elems == nil {
		elems = map[string]ast.Expression{}
	}
	switch x := e.(type) {
	case *ast.Identifier, *ast.IntegerLiteral:
		return e, elems, true
	case *ast.InvocationExpression:
		ident, isIdent := x.Function.(*ast.Identifier)
		if !isIdent || len(x.Arguments) != 1 {
			return nil, elems, false
		}
		if _, isConv := scalars[ident.Value]; !isConv {
			return nil, elems, false
		}
		arg, elems, ok := abstractReads(x.Arguments[0], types, elems)
		if !ok {
			return nil, elems, false
		}
		return &ast.InvocationExpression{Token: x.Token, Function: x.Function, Arguments: []ast.Expression{arg}}, elems, true
	case *ast.InfixExpression:
		left, elems, okL := abstractReads(x.Left, types, elems)
		if !okL {
			return nil, elems, false
		}
		right, elems, okR := abstractReads(x.Right, types, elems)
		if !okR {
			return nil, elems, false
		}
		return &ast.InfixExpression{Token: x.Token, Operator: x.Operator, Left: left, Right: right}, elems, true
	case *ast.IndexExpression:
		typ, known := scalarTypeIn(x, types)
		if !known {
			return nil, elems, false
		}
		name := fmt.Sprintf("_elem%d", len(elems))
		tok := x.Token
		tok.TokenKind, tok.Literal = token.IDENT, name
		elems[name] = &ast.Identifier{Token: tok, Value: typ.name}
		return &ast.Identifier{Token: tok, Value: name}, elems, true
	}
	return nil, elems, false
}

// scalarTypeIn infers the scalar type of an expression over the declared
// types: an identifier's declaration, a scalar constructor's type, an
// arithmetic operator's left operand; unknown otherwise.
func scalarTypeIn(e ast.Expression, types map[string]ast.Expression) (scalar, bool) {
	switch x := e.(type) {
	case *ast.Identifier:
		if typ, ok := types[x.Value]; ok {
			return scalarOf(typ)
		}
	case *ast.IndexExpression:
		// An element read: the span's or array's element type.
		if base, isIdent := x.Left.(*ast.Identifier); isIdent && !x.Dot {
			if typ, ok := types[base.Value]; ok {
				if sp, isSpan := spanOf(typ); isSpan && sp.elemLayout == nil {
					return sp.elem, true
				}
			}
		}
	case *ast.InvocationExpression:
		if ident, ok := x.Function.(*ast.Identifier); ok && len(x.Arguments) == 1 {
			if s, isConv := scalars[ident.Value]; isConv {
				return s, true
			}
		}
	case *ast.InfixExpression:
		switch x.Operator {
		case "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>":
			return scalarTypeIn(x.Left, types)
		}
	}
	return scalar{}, false
}

// literal is an integer literal at the site's position.
func literal(at token.Token, value int64) ast.Expression {
	tok := at
	tok.Literal = fmt.Sprintf("%d", value)
	return &ast.IntegerLiteral{Token: tok, Value: value}
}

// equalityTheorem states `old == new` over the site's free variables as a
// theorem the bit-level decider takes: each free identifier a parameter of
// its declared scalar type. False when a free variable has no scalar type.
func equalityTheorem(name string, old, replacement ast.Expression, types map[string]ast.Expression) (*ast.FunctionStatement, bool) {
	var params []*ast.FunctionParameter
	seen := map[string]bool{}
	ok := true
	mentionIdents(old, func(ident string) {
		if seen[ident] {
			return
		}
		seen[ident] = true
		if _, isConstructor := scalars[ident]; isConstructor {
			return // the type constructor of a literal, u32(2), not a variable
		}
		typ, known := types[ident]
		if !known {
			ok = false
			return
		}
		tok := token.Token{TokenKind: token.IDENT, Literal: ident}
		params = append(params, &ast.FunctionParameter{Name: &ast.Identifier{Token: tok, Value: ident}, Type: typ})
	})
	if !ok {
		return nil, false
	}
	tok := token.Token{TokenKind: token.IDENT, Literal: name}
	claim := &ast.InfixExpression{Token: tok, Operator: "==", Left: old, Right: replacement}
	body := &ast.BlockExpression{Token: tok, Block: &ast.BlockStatement{Token: tok, Statements: []ast.Statement{&ast.ExpressionStatement{Token: tok, Expression: claim}}}}
	return &ast.FunctionStatement{Token: tok, Name: &ast.Identifier{Token: tok, Value: name}, Parameters: params, ReturnType: &ast.Identifier{Token: tok, Value: "Bool"}, Body: body}, true
}
