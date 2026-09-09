package typechecker

// Extent facts and proof-based bounds-check elision (docs/spec/50-borrowing.md
// extent propositions; roadmap milestone 8, first increment). A runtime
// check the program already performs — `len(v) >= 4 ? { ... }`,
// `while i < len(v) { ... }`, `len(a) == len(b) ? { ... }` — establishes a
// FACT for exactly the scope it dominates. An element access inside that
// scope whose index the fact bounds is recorded as PROVEN (position-keyed,
// the resolution pattern of typechecker/mono.go), and the backend emits it
// as direct element access instead of the checked helper. Every access the
// checker cannot prove stays checked; facts are never derived from anything
// a callee could invalidate (globals are excluded), and a scope that
// reassigns a participating binding receives no facts at all.
//
// Discharge laws are Oak.Extents (Lean): a constant below a min-length
// bound is in range; an index bound transfers across a same-length fact; a
// constant below a static extent is in range.

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

type extentFactKind int

const (
	factMinLen     extentFactKind = iota // len(container) >= bound
	factIndexBound                       // index < len(container)
	factSameLen                          // len(container) == len(other)
)

type extentFact struct {
	kind      extentFactKind
	container string
	other     string // factIndexBound: the index binding; factSameLen: the other container
	bound     int64  // factMinLen
	offset    int64  // factIndexBound: i + offset < len(container) (0 for a plain bound)
}

// IndexProven reports whether the element access at tok was proven in range.
func (tc *TypeChecker) IndexProven(tok token.Token) bool {
	return tc.provenIndices[positionKey(tok)]
}

func (tc *TypeChecker) pushExtentFacts(facts []extentFact) int {
	mark := len(tc.extentFacts)
	tc.extentFacts = append(tc.extentFacts, facts...)
	return mark
}

func (tc *TypeChecker) popExtentFacts(mark int) {
	tc.extentFacts = tc.extentFacts[:mark]
}

// localBinding reports whether name is a binding no callee can reassign:
// not a global (Oak forbids shadowing, so a global name is the global).
func (tc *TypeChecker) localBinding(name string) bool {
	if tc.globalEnv == nil || tc.env == tc.globalEnv {
		return false
	}
	_, isGlobal := tc.globalEnv.Get(name)
	return !isGlobal
}

// constantIndex recognizes a literal or a primitive constructor over one:
// v[3], v[u32(3)].
func constantIndex(expr ast.Expression) (int64, bool) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return e.Value, true
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent || len(e.Arguments) != 1 {
			return 0, false
		}
		if _, isPrim := conversionPrimitives[ident.Value]; !isPrim {
			return 0, false
		}
		return constantIndex(e.Arguments[0])
	}
	return 0, false
}

// lenOf recognizes len(name) over an identifier.
func lenOf(expr ast.Expression) (string, bool) {
	call, ok := expr.(*ast.InvocationExpression)
	if !ok || len(call.Arguments) != 1 {
		return "", false
	}
	fn, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || fn.Value != "len" {
		return "", false
	}
	arg, isIdent := call.Arguments[0].(*ast.Identifier)
	if !isIdent {
		return "", false
	}
	return arg.Value, true
}

// offsetIndex recognizes `i` or `i + K` (either order) with K a literal.
func offsetIndex(expr ast.Expression) (name string, offset int64, ok bool) {
	if ident, isIdent := expr.(*ast.Identifier); isIdent {
		return ident.Value, 0, true
	}
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix || infix.Operator != "+" {
		return "", 0, false
	}
	if ident, isIdent := infix.Left.(*ast.Identifier); isIdent {
		if k, isConst := constantIndex(infix.Right); isConst && k >= 0 {
			return ident.Value, k, true
		}
	}
	if ident, isIdent := infix.Right.(*ast.Identifier); isIdent {
		if k, isConst := constantIndex(infix.Left); isConst && k >= 0 {
			return ident.Value, k, true
		}
	}
	return "", 0, false
}

// factsFromCondition derives the facts a TRUE condition establishes:
// len(v) >= K, len(v) > K, K <= len(v), K < len(v); i < len(v), len(v) > i;
// len(a) == len(b); conjunctions of these.
func (tc *TypeChecker) factsFromCondition(cond ast.Expression) []extentFact {
	infix, ok := cond.(*ast.InfixExpression)
	if !ok {
		return nil
	}
	if infix.Operator == "&&" {
		return append(tc.factsFromCondition(infix.Left), tc.factsFromCondition(infix.Right)...)
	}
	leftLen, leftIsLen := lenOf(infix.Left)
	rightLen, rightIsLen := lenOf(infix.Right)
	leftConst, leftIsConst := constantIndex(infix.Left)
	rightConst, rightIsConst := constantIndex(infix.Right)
	leftIndex, leftOffset, leftIsIndex := offsetIndex(infix.Left)
	rightIndex, rightOffset, rightIsIndex := offsetIndex(infix.Right)

	local := func(names ...string) bool {
		for _, name := range names {
			if !tc.localBinding(name) {
				return false
			}
		}
		return true
	}

	switch infix.Operator {
	case ">=":
		if leftIsLen && rightIsConst && rightConst >= 0 && local(leftLen) {
			return []extentFact{{kind: factMinLen, container: leftLen, bound: rightConst}}
		}
	case ">":
		if leftIsLen && rightIsConst && rightConst >= 0 && local(leftLen) {
			return []extentFact{{kind: factMinLen, container: leftLen, bound: rightConst + 1}}
		}
		if leftIsLen && rightIsIndex && !rightIsConst && local(leftLen, rightIndex) {
			return []extentFact{{kind: factIndexBound, container: leftLen, other: rightIndex, offset: rightOffset}}
		}
	case "<=":
		if leftIsConst && rightIsLen && leftConst >= 0 && local(rightLen) {
			return []extentFact{{kind: factMinLen, container: rightLen, bound: leftConst}}
		}
	case "<":
		if leftIsConst && rightIsLen && leftConst >= 0 && local(rightLen) {
			return []extentFact{{kind: factMinLen, container: rightLen, bound: leftConst + 1}}
		}
		if leftIsIndex && !leftIsConst && rightIsLen && local(leftIndex, rightLen) {
			return []extentFact{{kind: factIndexBound, container: rightLen, other: leftIndex, offset: leftOffset}}
		}
	case "==":
		if leftIsLen && rightIsLen && local(leftLen, rightLen) {
			return []extentFact{{kind: factSameLen, container: leftLen, other: rightLen}}
		}
	}
	return nil
}

// factNames lists every binding a fact set depends on.
func factNames(facts []extentFact) map[string]bool {
	names := map[string]bool{}
	for _, fact := range facts {
		names[fact.container] = true
		if fact.other != "" {
			names[fact.other] = true
		}
	}
	return names
}

// assignsAny reports whether the node (recursively) assigns to any of the
// names. exceptLast skips a trailing assignment statement of the top-level
// block (the loop's canonical increment).
func assignsAny(node ast.Node, names map[string]bool, exceptLast bool) bool {
	switch n := node.(type) {
	case nil:
		return false
	case *ast.BlockStatement:
		for i, stmt := range n.Statements {
			if exceptLast && i == len(n.Statements)-1 {
				if _, isAssign := stmt.(*ast.AssignmentStatement); isAssign {
					continue
				}
			}
			if assignsAny(stmt, names, false) {
				return true
			}
		}
		return false
	case *ast.BlockExpression:
		return assignsAny(n.Block, names, exceptLast)
	case *ast.AssignmentStatement:
		return n.Name != nil && names[n.Name.Value]
	case *ast.VariableDeclaration:
		return n.Name != nil && names[n.Name.Value]
	case *ast.WhileStatement:
		return assignsAny(n.Condition, names, false) || assignsAny(n.Body, names, false)
	case *ast.ExpressionStatement:
		return assignsAny(n.Expression, names, false)
	case *ast.IndexAssignmentStatement:
		return assignsAny(n.Value, names, false)
	case *ast.MatchExpression:
		for _, arm := range n.Arms {
			if assignsAny(arm.Body, names, false) {
				return true
			}
		}
		return assignsAny(n.Scrutinee, names, false)
	case *ast.InvocationExpression:
		for _, arg := range n.Arguments {
			if assignsAny(arg, names, false) {
				return true
			}
		}
		return false
	case *ast.InfixExpression:
		return assignsAny(n.Left, names, false) || assignsAny(n.Right, names, false)
	case *ast.PrefixExpression:
		return assignsAny(n.Right, names, false)
	}
	return false
}

// enterFactScope pushes the facts a dominating condition establishes for a
// scope, unless the scope reassigns a participating binding (then none).
func (tc *TypeChecker) enterFactScope(cond ast.Expression, scope ast.Node, loopIncrement bool) int {
	facts := tc.factsFromCondition(cond)
	if len(facts) == 0 {
		return len(tc.extentFacts)
	}
	if assignsAny(scope, factNames(facts), loopIncrement) {
		return len(tc.extentFacts)
	}
	return tc.pushExtentFacts(facts)
}

// recordIndexProof marks v[index] proven when a fact or a static extent
// bounds it; the backend then elides the check.
func (tc *TypeChecker) recordIndexProof(expr *ast.IndexExpression, arr *ArrayType) {
	container, isIdent := expr.Left.(*ast.Identifier)
	if !isIdent || arr == nil {
		return
	}
	name := container.Value
	proven := false
	if constant, isConst := constantIndex(expr.Index); isConst && constant >= 0 {
		if arr.Length >= 0 && !arr.IsSlice && !arr.IsSpan && constant < arr.Length {
			proven = true // static extent (Oak.Extents.static_extent)
		}
		for _, fact := range tc.extentFacts {
			if fact.kind == factMinLen && fact.container == name && constant < fact.bound {
				proven = true // Oak.Extents.constant_under_min_length
			}
		}
	} else if index, offset, isIndex := offsetIndex(expr.Index); isIndex {
		for _, fact := range tc.extentFacts {
			// i + K < len(c) bounds v[i + j] for every j <= K
			// (Oak.Extents.offset_under_bound).
			if fact.kind != factIndexBound || fact.other != index || offset > fact.offset {
				continue
			}
			if fact.container == name {
				proven = true
				continue
			}
			for _, same := range tc.extentFacts {
				if same.kind == factSameLen && ((same.container == fact.container && same.other == name) || (same.other == fact.container && same.container == name)) {
					proven = true // Oak.Extents.bound_transfers
				}
			}
		}
	}
	if !proven {
		return
	}
	if tc.provenIndices == nil {
		tc.provenIndices = make(map[string]bool)
	}
	tc.provenIndices[positionKey(expr.Token)] = true
}

// declarationFacts derives the fact a local view/span declaration
// establishes for the rest of its block: `s: []T = subslice(v, lo, hi)` or
// `s: []T = v[lo:hi]` with literal bounds has exactly hi - lo elements once
// the (bounds-checked) construction succeeds (Oak.Extents.subslice_extent).
func (tc *TypeChecker) declarationFacts(decl *ast.VariableDeclaration) []extentFact {
	if decl == nil || decl.Name == nil || decl.Value == nil || !tc.localBinding(decl.Name.Value) {
		return nil
	}
	var low, high ast.Expression
	switch value := decl.Value.(type) {
	case *ast.InvocationExpression:
		fn, isIdent := value.Function.(*ast.Identifier)
		if !isIdent || fn.Value != "subslice" || len(value.Arguments) != 3 {
			return nil
		}
		low, high = value.Arguments[1], value.Arguments[2]
	case *ast.SliceExpression:
		low, high = value.Low, value.High
	default:
		return nil
	}
	lo, loConst := constantIndex(low)
	hi, hiConst := constantIndex(high)
	if !loConst || !hiConst || lo < 0 || hi < lo {
		return nil
	}
	return []extentFact{{kind: factMinLen, container: decl.Name.Value, bound: hi - lo}}
}

// enterDeclarationFacts pushes a declaration's fact when the remaining
// statements of the block never reassign the binding.
func (tc *TypeChecker) enterDeclarationFacts(decl *ast.VariableDeclaration, rest []ast.Statement) {
	facts := tc.declarationFacts(decl)
	if len(facts) == 0 {
		return
	}
	for _, stmt := range rest {
		if assignsAny(stmt, factNames(facts), false) {
			return
		}
	}
	tc.pushExtentFacts(facts)
}

// enterArmFacts gives the TRUE arm of a Bool ?-match the facts its
// condition establishes (the sugar lowers `cond ? a | b` to true/false
// literal arms, so the true arm is the fall-through under the check).
func (tc *TypeChecker) enterArmFacts(match *ast.MatchExpression, arm *ast.MatchArm) int {
	literal, isLiteral := arm.Pattern.(*ast.LiteralPattern)
	if !isLiteral {
		return len(tc.extentFacts)
	}
	flag, isBool := literal.Value.(*ast.Boolean)
	if !isBool || !flag.Value {
		return len(tc.extentFacts)
	}
	return tc.enterFactScope(match.Scrutinee, arm.Body, false)
}
