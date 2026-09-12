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
// a callee could invalidate (globals are excluded).
//
// Facts are flow-sensitive (third increment): an assignment to a
// participating binding kills the fact from that statement on, for the
// rest of every enclosing scope; a loop that assigns a participating
// binding anywhere kills the fact before its condition is even evaluated
// (an earlier statement of its body runs again after the assignment);
// kills inside one match arm reach the statements after the match but not
// the sibling arms. The right operand of `&&` and the consequence of `if`
// see the facts their guard establishes. Offset bounds come only from the
// wrap-free spelling `i < len(v) - K` (or `<=`) under a known
// `len(v) >= K`: fixed-width `i + K` wraps, so `i + K < len(v)` proves
// nothing about `i`.
//
// Discharge laws are Oak.Extents (Lean): a constant below a min-length
// bound is in range; an index bound transfers across a same-length fact; a
// constant below a static extent is in range.

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
	"strings"
)

type extentFactKind int

const (
	factMinLen     extentFactKind = iota // len(container) >= bound
	factIndexBound                       // index < len(container)
	factSameLen                          // len(container) == len(other)
	factUpperBound                       // other <= len(container), other a local binding
	factIndexLit                         // other < bound, a literal bound on a local binding
	factLowerLit                         // bound <= other, a literal lower bound on a local binding
	factBelow                            // other < via, a guard between two local bindings
	factDivUpper                         // other <= len(container) / bound, a quotient binding
	factDivIndex                         // other < len(container) / bound
)

type extentFact struct {
	kind      extentFactKind
	container string
	other     string // factIndexBound: the index binding; factSameLen: the other container
	bound     int64  // factMinLen
	offset    int64  // factIndexBound: i + offset < len(container) (0 for a plain bound)
	// dead marks a fact invalidated by a later assignment to one of its
	// bindings (flow-sensitive kill); a dead fact proves nothing but keeps
	// its stack position so scope marks stay valid.
	dead bool
	// via names the intermediate binding a bound was composed through
	// (`i < n` with `n <= len(v)`): an assignment to it kills the fact.
	via string
	// indexDirect marks a composed index bound whose index comes from the
	// guard's own comparison (`i < n`), so a loop re-checks the index each
	// iteration even though the upper bound came through a binding.
	indexDirect bool
	// viaBinding marks a fact recovered through a Bool binding's remembered
	// condition rather than from the guard's own comparisons. A loop that
	// assigns one of its participants cannot carry it into the body: the
	// re-evaluated binding does not re-check the remembered condition.
	viaBinding bool
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

// localBinding reports whether name (a binding or a field path) is rooted
// at a binding no callee can reassign: one the current scope resolves and
// that is not a global (Oak forbids shadowing, so a global name is the
// global). A package qualifier (`hash.TABLE`) is not a binding at all and
// is refused.
func (tc *TypeChecker) localBinding(name string) bool {
	if tc.globalEnv == nil || tc.env == tc.globalEnv {
		return false
	}
	root := pathRoot(name)
	if _, isGlobal := tc.globalEnv.Get(root); isGlobal {
		return false
	}
	_, bound := tc.env.Get(root)
	return bound
}

// globalStaticArray reports whether name is a top-level owned array of
// static extent: its length is a fact of the program, so it may stand in a
// fact's container position (docs/spec/50-borrowing.md, elision over
// top-level tables; the OS pilot's R3).
func (tc *TypeChecker) globalStaticArray(name string) bool {
	if tc.globalEnv == nil || strings.Contains(name, ".") {
		return false
	}
	scheme, isGlobal := tc.globalEnv.Get(name)
	if !isGlobal || scheme == nil {
		return false
	}
	arr, isArray := scheme.Type.(*ArrayType)
	return isArray && arr.Length >= 0 && !arr.IsSlice && !arr.IsSpan
}

// pathOf renders a binding or a record field path rooted at a binding
// (`t`, `t.block`, `t.state.filled`) as the dotted name the facts use.
func pathOf(expr ast.Expression) (string, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e.Value, true
	case *ast.IndexExpression:
		if !e.Dot {
			return "", false
		}
		base, ok := pathOf(e.Left)
		if !ok {
			return "", false
		}
		field, isIdent := e.Index.(*ast.Identifier)
		if !isIdent {
			return "", false
		}
		return base + "." + field.Value, true
	}
	return "", false
}

// pathRoot is the binding a path is rooted at.
func pathRoot(path string) string {
	if dot := strings.IndexByte(path, '.'); dot >= 0 {
		return path[:dot]
	}
	return path
}

// pathTouches reports whether assigning `assigned` can change the value
// named by `watched`: the same path, a prefix of it (the record holding
// the field), or a field under it (part of the record's value).
func pathTouches(assigned, watched string) bool {
	return assigned == watched || strings.HasPrefix(watched, assigned+".") || strings.HasPrefix(assigned, watched+".")
}

// touchedBy reports whether any assigned name can change the path.
func touchedBy(assigned map[string]bool, path string) bool {
	for name := range assigned {
		if pathTouches(name, path) {
			return true
		}
	}
	return false
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
	return pathOf(call.Arguments[0])
}

// lenMinus recognizes `len(name) - K` with K a literal.
func lenMinus(expr ast.Expression) (name string, k int64, ok bool) {
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix || infix.Operator != "-" {
		return "", 0, false
	}
	name, isLen := lenOf(infix.Left)
	if !isLen {
		return "", 0, false
	}
	k, isConst := constantIndex(infix.Right)
	if !isConst || k < 0 {
		return "", 0, false
	}
	return name, k, true
}

// offsetIndex recognizes `i` or `i + K` (either order) with K a literal.
func offsetIndex(expr ast.Expression) (name string, offset int64, ok bool) {
	if path, isPath := pathOf(expr); isPath {
		return path, 0, true
	}
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix || infix.Operator != "+" {
		return "", 0, false
	}
	if path, isPath := pathOf(infix.Left); isPath {
		if k, isConst := constantIndex(infix.Right); isConst && k >= 0 {
			return path, k, true
		}
	}
	if path, isPath := pathOf(infix.Right); isPath {
		if k, isConst := constantIndex(infix.Left); isConst && k >= 0 {
			return path, k, true
		}
	}
	return "", 0, false
}

// minusIndex recognizes `i - K` with K a literal.
func minusIndex(expr ast.Expression) (name string, k int64, ok bool) {
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix || infix.Operator != "-" {
		return "", 0, false
	}
	name, isPath := pathOf(infix.Left)
	if !isPath {
		return "", 0, false
	}
	k, isConst := constantIndex(infix.Right)
	if !isConst || k < 0 {
		return "", 0, false
	}
	return name, k, true
}

// scaledIndex recognizes `i * K`, `K * i`, and either plus a literal `j`
// (in either order): the word loads of a block.
func scaledIndex(expr ast.Expression) (name string, scale int64, offset int64, ok bool) {
	product := func(e ast.Expression) (string, int64, bool) {
		infix, isInfix := e.(*ast.InfixExpression)
		if !isInfix || infix.Operator != "*" {
			return "", 0, false
		}
		if name, isPath := pathOf(infix.Left); isPath {
			if k, isConst := constantIndex(infix.Right); isConst && k >= 0 {
				return name, k, true
			}
		}
		if name, isPath := pathOf(infix.Right); isPath {
			if k, isConst := constantIndex(infix.Left); isConst && k >= 0 {
				return name, k, true
			}
		}
		return "", 0, false
	}
	if name, scale, isProduct := product(expr); isProduct {
		return name, scale, 0, true
	}
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix || infix.Operator != "+" {
		return "", 0, 0, false
	}
	if name, scale, isProduct := product(infix.Left); isProduct {
		if j, isConst := constantIndex(infix.Right); isConst && j >= 0 {
			return name, scale, j, true
		}
	}
	if name, scale, isProduct := product(infix.Right); isProduct {
		if j, isConst := constantIndex(infix.Left); isConst && j >= 0 {
			return name, scale, j, true
		}
	}
	return "", 0, 0, false
}

// maskedIndex recognizes `e & M` (either order) with M a literal mask.
func maskedIndex(expr ast.Expression) (mask int64, ok bool) {
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix || infix.Operator != "&" {
		return 0, false
	}
	if m, isConst := constantIndex(infix.Right); isConst && m >= 0 {
		return m, true
	}
	if m, isConst := constantIndex(infix.Left); isConst && m >= 0 {
		return m, true
	}
	return 0, false
}

// factsFromCondition derives the facts a TRUE condition establishes:
// len(v) >= K, len(v) > K, K <= len(v), K < len(v); i < len(v), len(v) > i;
// len(a) == len(b); conjunctions of these.
func (tc *TypeChecker) factsFromCondition(cond ast.Expression) []extentFact {
	facts, pairs := tc.factsFromConditionWith(cond, nil)
	return tc.resolveIndexPairs(facts, pairs)
}

// indexPair is a guard `i < n` between two local bindings, resolved against
// upper-bound facts once the whole condition is known.
type indexPair struct{ index, bound string }

// resolveIndexPairs turns each `i < n` into `i < len(v)` for every live or
// just-derived fact `n <= len(v)` (Oak.Extents.bound_through_upper).
func (tc *TypeChecker) resolveIndexPairs(facts []extentFact, pairs []indexPair) []extentFact {
	for _, pair := range pairs {
		for _, source := range [][]extentFact{tc.extentFacts, facts} {
			for _, fact := range source {
				if fact.dead || fact.other != pair.bound {
					continue
				}
				switch fact.kind {
				case factUpperBound:
					facts = append(facts, extentFact{kind: factIndexBound, container: fact.container, other: pair.index, via: pair.bound, viaBinding: fact.viaBinding, indexDirect: true})
				case factDivUpper:
					// i < n with n <= len(v) / K: i < len(v) / K
					// (Oak.Extents.div_bound_scaled reads it at the index).
					facts = append(facts, extentFact{kind: factDivIndex, container: fact.container, other: pair.index, bound: fact.bound, via: pair.bound, viaBinding: fact.viaBinding, indexDirect: true})
				}
			}
		}
	}
	return facts
}

// boolBindingFacts returns the facts a Bool binding remembers, marked as
// recovered through the binding.
func (tc *TypeChecker) boolBindingFacts(name string) []extentFact {
	stored := tc.boolFacts[name]
	facts := make([]extentFact, 0, len(stored))
	for _, fact := range stored {
		if fact.dead {
			continue
		}
		fact.viaBinding = true
		facts = append(facts, fact)
	}
	return facts
}

// minLengthKnown reports whether len(container) >= k is established by the
// live fact stack or by facts already derived from earlier conjuncts.
func (tc *TypeChecker) minLengthKnown(container string, k int64, earlier []extentFact) bool {
	for _, facts := range [][]extentFact{tc.extentFacts, earlier} {
		for _, fact := range facts {
			if !fact.dead && fact.kind == factMinLen && fact.container == container && fact.bound >= k {
				return true
			}
		}
	}
	return false
}

func (tc *TypeChecker) factsFromConditionWith(cond ast.Expression, earlier []extentFact) ([]extentFact, []indexPair) {
	if ident, isIdent := cond.(*ast.Identifier); isIdent {
		// A Bool binding stands for the condition assigned to it.
		return tc.boolBindingFacts(ident.Value), nil
	}
	infix, ok := cond.(*ast.InfixExpression)
	if !ok {
		return nil, nil
	}
	if infix.Operator == "&&" {
		left, leftPairs := tc.factsFromConditionWith(infix.Left, earlier)
		right, rightPairs := tc.factsFromConditionWith(infix.Right, append(append([]extentFact{}, earlier...), left...))
		return append(left, right...), append(leftPairs, rightPairs...)
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
	// container admits a fact's container position: a local binding, or a
	// top-level owned array, whose static extent no statement can change
	// (the index positions stay local: a callee may write a global index).
	container := func(name string) bool {
		return tc.localBinding(name) || tc.globalStaticArray(name)
	}

	minusLen, minusK, rightIsLenMinus := lenMinus(infix.Right)

	// Literal bounds on a binding (docs/spec/50-borrowing.md, literal bound
	// and lower bound): `i < K`, `i <= K`, `K > i`, `K >= i` bound i above;
	// `i >= K`, `i > K`, `K <= i`, `K < i` below. Only plain bindings, never
	// an offset form, whose fixed-width sum may have wrapped.
	if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsConst && rightConst >= 0 && local(leftIndex) {
		switch infix.Operator {
		case "<":
			return []extentFact{{kind: factIndexLit, other: leftIndex, bound: rightConst}}, nil
		case "<=":
			return []extentFact{{kind: factIndexLit, other: leftIndex, bound: rightConst + 1}}, nil
		case ">=":
			return []extentFact{{kind: factLowerLit, other: leftIndex, bound: rightConst}}, nil
		case ">":
			return []extentFact{{kind: factLowerLit, other: leftIndex, bound: rightConst + 1}}, nil
		}
	}
	if rightIsIndex && !rightIsConst && rightOffset == 0 && leftIsConst && leftConst >= 0 && local(rightIndex) {
		switch infix.Operator {
		case ">":
			return []extentFact{{kind: factIndexLit, other: rightIndex, bound: leftConst}}, nil
		case ">=":
			return []extentFact{{kind: factIndexLit, other: rightIndex, bound: leftConst + 1}}, nil
		case "<=":
			return []extentFact{{kind: factLowerLit, other: rightIndex, bound: leftConst}}, nil
		case "<":
			return []extentFact{{kind: factLowerLit, other: rightIndex, bound: leftConst + 1}}, nil
		}
	}

	switch infix.Operator {
	case ">=":
		if leftIsLen && rightIsConst && rightConst >= 0 && container(leftLen) {
			return []extentFact{{kind: factMinLen, container: leftLen, bound: rightConst}}, nil
		}
		// len(v) >= n: n bounds indices into v (Oak.Extents.bound_through_upper).
		if leftIsLen && rightIsIndex && !rightIsConst && rightOffset == 0 && container(leftLen) && local(rightIndex) {
			return []extentFact{{kind: factUpperBound, container: leftLen, other: rightIndex}}, nil
		}
	case ">":
		if leftIsLen && rightIsConst && rightConst >= 0 && container(leftLen) {
			return []extentFact{{kind: factMinLen, container: leftLen, bound: rightConst + 1}}, nil
		}
		// n > i between two local bindings: i < n.
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsIndex && !rightIsConst && rightOffset == 0 &&
			!leftIsLen && local(leftIndex, rightIndex) {
			return []extentFact{{kind: factBelow, other: rightIndex, via: leftIndex, indexDirect: true}},
				[]indexPair{{index: rightIndex, bound: leftIndex}}
		}
		// len(v) > i: a plain index bound. An offset form (len(v) > i + K)
		// proves nothing, because fixed-width i + K may have wrapped.
		if leftIsLen && rightIsIndex && !rightIsConst && rightOffset == 0 && container(leftLen) && local(rightIndex) {
			// len(v) > n is both an index bound and an upper bound for n.
			return []extentFact{
				{kind: factIndexBound, container: leftLen, other: rightIndex},
				{kind: factUpperBound, container: leftLen, other: rightIndex},
			}, nil
		}
	case "<=":
		if leftIsConst && rightIsLen && leftConst >= 0 && container(rightLen) {
			return []extentFact{{kind: factMinLen, container: rightLen, bound: leftConst}}, nil
		}
		// n <= len(v): n bounds indices into v.
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsLen && local(leftIndex) && container(rightLen) {
			return []extentFact{{kind: factUpperBound, container: rightLen, other: leftIndex}}, nil
		}
		// i <= len(v) - K with len(v) >= K known: i + (K - 1) < len(v),
		// and the subtraction cannot wrap (Oak.Extents.guard_without_wrap).
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsLenMinus && minusK >= 1 &&
			local(leftIndex) && container(minusLen) && tc.minLengthKnown(minusLen, minusK, earlier) {
			return []extentFact{{kind: factIndexBound, container: minusLen, other: leftIndex, offset: minusK - 1}}, nil
		}
	case "<":
		if leftIsConst && rightIsLen && leftConst >= 0 && container(rightLen) {
			return []extentFact{{kind: factMinLen, container: rightLen, bound: leftConst + 1}}, nil
		}
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsLen && local(leftIndex) && container(rightLen) {
			// i < len(v) bounds i, and makes i an upper bound for indices into v.
			return []extentFact{
				{kind: factIndexBound, container: rightLen, other: leftIndex},
				{kind: factUpperBound, container: rightLen, other: leftIndex},
			}, nil
		}
		// i < n between two local bindings: resolved against upper bounds
		// once the whole condition is known.
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsIndex && !rightIsConst && rightOffset == 0 &&
			!rightIsLen && local(leftIndex, rightIndex) {
			// The relation itself is kept too: a midpoint declared under it
			// is below its upper end (Oak.Extents.midpoint_under_bound).
			return []extentFact{{kind: factBelow, other: leftIndex, via: rightIndex, indexDirect: true}},
				[]indexPair{{index: leftIndex, bound: rightIndex}}
		}
		// i < len(v) - K with len(v) >= K known: i + K < len(v)
		// (Oak.Extents.guard_without_wrap).
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsLenMinus &&
			local(leftIndex) && container(minusLen) && tc.minLengthKnown(minusLen, minusK, earlier) {
			return []extentFact{{kind: factIndexBound, container: minusLen, other: leftIndex, offset: minusK}}, nil
		}
	case "==":
		if leftIsLen && rightIsLen && container(leftLen) && container(rightLen) {
			return []extentFact{{kind: factSameLen, container: leftLen, other: rightLen}}, nil
		}
	}
	return nil, nil
}

// factNames lists every binding a fact set depends on.
func factNames(facts []extentFact) map[string]bool {
	names := map[string]bool{}
	for _, fact := range facts {
		names[fact.container] = true
		if fact.other != "" {
			names[fact.other] = true
		}
		if fact.via != "" {
			names[fact.via] = true
		}
	}
	return names
}

// dependsOn reports whether a fact mentions any of the names.
func (fact extentFact) dependsOn(names map[string]bool) bool {
	return (fact.container != "" && touchedBy(names, fact.container)) ||
		(fact.other != "" && touchedBy(names, fact.other)) ||
		(fact.via != "" && touchedBy(names, fact.via))
}

// rememberBoolFacts records the facts a Bool binding's new value carries
// (none clears any earlier association).
func (tc *TypeChecker) rememberBoolFacts(name *ast.Identifier, facts []extentFact) {
	if name == nil {
		return
	}
	if tc.boolFacts == nil {
		tc.boolFacts = make(map[string][]extentFact)
	}
	if len(facts) == 0 {
		delete(tc.boolFacts, name.Value)
		return
	}
	tc.boolFacts[name.Value] = facts
}

// loopConditionFacts derives the facts a while condition establishes for
// its body, with bindings as they are on entry. A fact composed through a
// binding the loop assigns, or recovered through a Bool binding when the
// loop assigns any of its participants, is dropped: the re-evaluated
// condition does not re-check it, while a direct comparison does.
func (tc *TypeChecker) loopConditionFacts(loop *ast.WhileStatement) []extentFact {
	assigned := map[string]bool{}
	assignedNames(loop, assigned)
	kept := make([]extentFact, 0)
	for _, fact := range tc.factsFromCondition(loop.Condition) {
		if fact.kind == factBelow {
			// The guard compares the two bindings itself on every
			// iteration; only a relation replayed from a Bool binding is
			// stale once either side is written.
			if fact.viaBinding && (touchedBy(assigned, fact.other) || touchedBy(assigned, fact.via)) {
				continue
			}
			kept = append(kept, fact)
			continue
		}
		if fact.via != "" && touchedBy(assigned, fact.via) {
			continue
		}
		if fact.viaBinding {
			// The container and the composed-through binding came from the
			// remembered condition; a directly compared index is re-checked.
			if touchedBy(assigned, fact.container) || (!fact.indexDirect && fact.other != "" && touchedBy(assigned, fact.other)) {
				continue
			}
		}
		kept = append(kept, fact)
	}
	return kept
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
				if field, isField := stmt.(*ast.IndexAssignmentStatement); isField && field.Target != nil && field.Target.Dot {
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
		return n.Name != nil && touchedBy(names, n.Name.Value)
	case *ast.VariableDeclaration:
		return n.Name != nil && touchedBy(names, n.Name.Value)
	case *ast.WhileStatement:
		return assignsAny(n.Condition, names, false) || assignsAny(n.Body, names, false)
	case *ast.ExpressionStatement:
		return assignsAny(n.Expression, names, false)
	case *ast.IndexAssignmentStatement:
		// A field assignment writes the path; an element write leaves the
		// container's length alone.
		if n.Target != nil && n.Target.Dot {
			if path, isPath := pathOf(n.Target); isPath && touchedBy(names, path) {
				return true
			}
		}
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

// enterFactScope pushes the facts a dominating condition establishes for
// the scope that follows; assignments inside the scope kill them from the
// assignment on (killFacts), so no whole-scope rejection is needed.
func (tc *TypeChecker) enterFactScope(cond ast.Expression) int {
	facts := tc.factsFromCondition(cond)
	if len(facts) == 0 {
		return len(tc.extentFacts)
	}
	return tc.pushExtentFacts(facts)
}

// assignedNames collects every binding the node (recursively) assigns or
// declares, in any branch or loop it contains.
func assignedNames(node ast.Node, into map[string]bool) {
	switch n := node.(type) {
	case nil:
	case *ast.BlockStatement:
		for _, stmt := range n.Statements {
			assignedNames(stmt, into)
		}
	case *ast.BlockExpression:
		assignedNames(n.Block, into)
	case *ast.UnsafeBlock:
		assignedNames(n.Body, into)
	case *ast.AssignmentStatement:
		if n.Name != nil {
			into[n.Name.Value] = true
		}
		assignedNames(n.Value, into)
	case *ast.VariableDeclaration:
		if n.Name != nil {
			into[n.Name.Value] = true
		}
		assignedNames(n.Value, into)
	case *ast.WhileStatement:
		assignedNames(n.Condition, into)
		assignedNames(n.Body, into)
	case *ast.IfStatement:
		assignedNames(n.Condition, into)
		assignedNames(n.Consequence, into)
		assignedNames(n.Alternative, into)
	case *ast.ExpressionStatement:
		assignedNames(n.Expression, into)
	case *ast.IndexAssignmentStatement:
		if n.Target != nil && n.Target.Dot {
			if path, isPath := pathOf(n.Target); isPath {
				into[path] = true
			}
		}
		assignedNames(n.Value, into)
	case *ast.MatchExpression:
		assignedNames(n.Scrutinee, into)
		for _, arm := range n.Arms {
			assignedNames(arm.Body, into)
		}
	case *ast.InvocationExpression:
		for _, arg := range n.Arguments {
			assignedNames(arg, into)
		}
	case *ast.InfixExpression:
		assignedNames(n.Left, into)
		assignedNames(n.Right, into)
	case *ast.PrefixExpression:
		assignedNames(n.Right, into)
	}
}

// killFacts marks every live fact that depends on one of the names dead,
// for the rest of every enclosing scope.
func (tc *TypeChecker) killFacts(names map[string]bool) {
	if len(names) == 0 {
		return
	}
	for i := range tc.extentFacts {
		fact := &tc.extentFacts[i]
		if fact.dependsOn(names) {
			fact.dead = true
		}
	}
	// Remembered Bool conditions die with their bindings or participants.
	for bound, facts := range tc.boolFacts {
		if names[bound] {
			delete(tc.boolFacts, bound)
			continue
		}
		kept := facts[:0]
		for _, fact := range facts {
			if !fact.dependsOn(names) {
				kept = append(kept, fact)
			}
		}
		tc.boolFacts[bound] = kept
	}
}

// killFactsAssignedBy kills the facts a statement or loop invalidates.
func (tc *TypeChecker) killFactsAssignedBy(node ast.Node) {
	names := map[string]bool{}
	assignedNames(node, names)
	tc.killFacts(names)
}

// deadSnapshot records which facts are dead, so alternatives (match arms,
// if branches) can each start from the same state and the union of their
// kills applies after the construct.
func (tc *TypeChecker) deadSnapshot() []bool {
	dead := make([]bool, len(tc.extentFacts))
	for i, fact := range tc.extentFacts {
		dead[i] = fact.dead
	}
	return dead
}

func (tc *TypeChecker) restoreDead(snapshot []bool) {
	for i := range snapshot {
		if i < len(tc.extentFacts) {
			tc.extentFacts[i].dead = snapshot[i]
		}
	}
}

func unionDead(a, b []bool) []bool {
	out := make([]bool, len(a))
	for i := range a {
		out[i] = a[i] || (i < len(b) && b[i])
	}
	return out
}

// recordIndexProof marks v[index] proven when a fact or a static extent
// bounds it; the backend then elides the check.
func (tc *TypeChecker) recordIndexProof(expr *ast.IndexExpression, arr *ArrayType) {
	name, isPath := pathOf(expr.Left)
	if !isPath || arr == nil {
		return
	}
	if !tc.indexUnder(expr.Index, name, arr) {
		return
	}
	if tc.provenIndices == nil {
		tc.provenIndices = make(map[string]bool)
	}
	tc.provenIndices[positionKey(expr.Token)] = true
}

// provenBelow reports whether the live facts prove `index < bound` for a
// literal bound: the index laws applied to a virtual container of static
// extent bound and no name (typechecker/refinements.go discharges a
// construction `Name(v)` with it when the predicate is `value < K`).
func (tc *TypeChecker) provenBelow(index ast.Expression, bound int64) bool {
	if bound <= 0 {
		return false
	}
	return tc.indexUnder(index, "", &ArrayType{Length: bound, ElementType: &UnitType{}})
}

// indexUnder decides whether the live facts prove index < the extent of
// the container name (typed arr), by the laws of Oak.Extents.
func (tc *TypeChecker) indexUnder(indexExpr ast.Expression, name string, arr *ArrayType) bool {
	proven := false
	// lengthAtLeast: the container is known to hold at least n elements —
	// its declared static extent, or a live min-length fact.
	lengthAtLeast := func(n int64) bool {
		if arr.Length >= 0 && !arr.IsSlice && !arr.IsSpan && arr.Length >= n {
			return true
		}
		for _, fact := range tc.extentFacts {
			if !fact.dead && fact.kind == factMinLen && fact.container == name && fact.bound >= n {
				return true
			}
		}
		return false
	}
	// literalUpper: the live literal bound on a binding, if any.
	literalUpper := func(binding string) (int64, bool) {
		bound, found := int64(0), false
		for _, fact := range tc.extentFacts {
			if !fact.dead && fact.kind == factIndexLit && fact.other == binding && (!found || fact.bound < bound) {
				bound, found = fact.bound, true
			}
		}
		return bound, found
	}
	literalLower := func(binding string) (int64, bool) {
		bound, found := int64(0), false
		for _, fact := range tc.extentFacts {
			if !fact.dead && fact.kind == factLowerLit && fact.other == binding && (!found || fact.bound > bound) {
				bound, found = fact.bound, true
			}
		}
		return bound, found
	}
	if _, bound, isRefined := tc.refinedBelow(indexExpr); isRefined {
		// Name(e) with `Name: type = T where value < K` is below K: the
		// construction's guard trapped otherwise (typechecker/refinements.go).
		proven = lengthAtLeast(bound)
	} else if mask, isMasked := maskedIndex(indexExpr); isMasked {
		// e & M < len whenever M < len (Oak.Extents.masked_under_length).
		proven = lengthAtLeast(mask + 1)
	} else if index, scale, offset, isScaled := scaledIndex(indexExpr); isScaled {
		// i * K + j under i < U needs (U - 1) * K + j < len
		// (Oak.Extents.scaled_under_bound).
		if upper, bounded := literalUpper(index); bounded && upper >= 1 {
			proven = lengthAtLeast((upper-1)*scale + offset + 1)
		}
		// i * K + j under i < len(c) / K with j < K (Oak.Extents.div_bound_scaled).
		for _, fact := range tc.extentFacts {
			if !fact.dead && fact.kind == factDivIndex && fact.other == index && fact.container == name && fact.bound == scale && offset < scale {
				proven = true
			}
		}
	} else if index, k, isMinus := minusIndex(indexExpr); isMinus {
		// i - K under K <= L <= i and i < U needs U - K <= len
		// (Oak.Extents.subtraction_under_bounds); under i < len(v) it is
		// immediate (subtraction_under_length).
		if lower, bounded := literalLower(index); bounded && lower >= k {
			if upper, hasUpper := literalUpper(index); hasUpper && upper >= k && lengthAtLeast(upper-k) {
				proven = true
			}
			for _, fact := range tc.extentFacts {
				if !fact.dead && fact.kind == factIndexBound && fact.other == index && fact.offset == 0 && fact.container == name {
					proven = true
				}
			}
		}
	} else if constant, isConst := constantIndex(indexExpr); isConst && constant >= 0 {
		if arr.Length >= 0 && !arr.IsSlice && !arr.IsSpan && constant < arr.Length {
			proven = true // static extent (Oak.Extents.static_extent)
		}
		for _, fact := range tc.extentFacts {
			if fact.dead {
				continue
			}
			if fact.kind == factMinLen && fact.container == name && constant < fact.bound {
				proven = true // Oak.Extents.constant_under_min_length
			}
		}
	} else if index, offset, isIndex := offsetIndex(indexExpr); isIndex {
		// i + j under i < K needs K + j <= len (Oak.Extents.literal_bound_under_length).
		if upper, bounded := literalUpper(index); bounded && lengthAtLeast(upper+offset) {
			proven = true
		}
		// i + j under i < len(c) / K with j < K (Oak.Extents.div_bound_under_length).
		for _, fact := range tc.extentFacts {
			if !fact.dead && fact.kind == factDivIndex && fact.other == index && fact.container == name && offset < fact.bound {
				proven = true
			}
		}
		for _, fact := range tc.extentFacts {
			// i + K < len(c) bounds v[i + j] for every j <= K
			// (Oak.Extents.offset_under_bound).
			if fact.dead || fact.kind != factIndexBound || fact.other != index || offset > fact.offset {
				continue
			}
			if fact.container == name {
				proven = true
				continue
			}
			for _, same := range tc.extentFacts {
				if !same.dead && same.kind == factSameLen && ((same.container == fact.container && same.other == name) || (same.other == fact.container && same.container == name)) {
					proven = true // Oak.Extents.bound_transfers
				}
			}
		}
	}
	return proven
}

// declarationFacts derives the fact a local view/span declaration
// establishes for the rest of its block: `s: []T = subslice(v, start, n)`
// with a literal n has exactly n elements, and `s: []T = v[lo:hi]` with
// literal bounds exactly hi - lo, once the (bounds-checked) construction
// succeeds (Oak.Extents.subslice_extent).
func (tc *TypeChecker) declarationFacts(decl *ast.VariableDeclaration) []extentFact {
	if decl == nil || decl.Name == nil || decl.Value == nil || !tc.localBinding(decl.Name.Value) {
		return nil
	}
	// A binding declared at a refinement type carries the refinement's
	// predicate (typechecker/refinements.go). The type is read by name
	// only: re-parsing an arbitrary annotation here would repeat the
	// checks its own site already made.
	if ident, isIdent := decl.Type.(*ast.Identifier); isIdent {
		if _, isRefinement := tc.refinements[ident.Value]; isRefinement {
			if facts := tc.refinementFacts(decl.Name.Value, tc.parseTypeExpression(decl.Type)); len(facts) != 0 {
				return facts
			}
		}
	}
	// A literal integer initializer bounds the binding both ways
	// (docs/spec/50-borrowing.md, lower bound; literal bound): `i: u32 =
	// 16` is `16 <= i` and `i < 17` until the binding is written.
	if k, isConst := constantIndex(decl.Value); isConst && k >= 0 {
		return []extentFact{
			{kind: factLowerLit, other: decl.Name.Value, bound: k},
			{kind: factIndexLit, other: decl.Name.Value, bound: k + 1},
		}
	}
	// The midpoint `m = a + (b - a) / K` (K a literal >= 2) under a live
	// `a < b` is below b (Oak.Extents.midpoint_under_bound: the
	// subtraction and the sum are the natural ones because a < b), so m
	// inherits b's upper bounds: `m < len(c)` for `b <= len(c)`, `m < B - 1`
	// for `b < B` — the binary-search probe.
	if low, high, isMidpoint := midpointOf(decl.Value); isMidpoint && tc.localBinding(low) && tc.localBinding(high) && tc.belowLive(low, high) {
		m := decl.Name.Value
		facts := []extentFact{{kind: factBelow, other: m, via: high, indexDirect: true}}
		for _, fact := range tc.extentFacts {
			if fact.dead || fact.other != high {
				continue
			}
			switch fact.kind {
			case factUpperBound:
				facts = append(facts, extentFact{kind: factIndexBound, container: fact.container, other: m, via: high, viaBinding: fact.viaBinding, indexDirect: true})
			case factIndexBound:
				// m < high < len(c) (an offset bound on high needs no
				// weakening: m + K < high + K).
				facts = append(facts, extentFact{kind: factIndexBound, container: fact.container, other: m, offset: fact.offset, via: high, viaBinding: fact.viaBinding, indexDirect: true})
			case factDivUpper, factDivIndex:
				// m < high <= len(c) / K, or m < high < len(c) / K.
				facts = append(facts, extentFact{kind: factDivIndex, container: fact.container, other: m, bound: fact.bound, via: high, viaBinding: fact.viaBinding, indexDirect: true})
			case factIndexLit:
				if fact.bound >= 2 {
					facts = append(facts, extentFact{kind: factIndexLit, other: m, bound: fact.bound - 1})
				}
			}
		}
		return facts
	}
	// `n: u32 = len(v)` binds an upper bound for indices into v: n = len(v)
	// gives n <= len(v), so a later `i < n` proves `i < len(v)`
	// (Oak.Extents.bound_through_upper). This is the canonical strict loop
	// shape (85-discipline.md section 3), where the bound must be a binding.
	if container, isLen := lenOf(decl.Value); isLen && tc.localBinding(container) {
		return []extentFact{{kind: factUpperBound, container: container, other: decl.Name.Value}}
	}
	// `pages: u32 = len(v) / K` with a literal K >= 1: pages <= len(v) / K,
	// so a later `i < pages` proves `v[i * K + j]` for every j < K
	// (Oak.Extents.div_bound_scaled) — the page count of a keyed view.
	if quotient, isDiv := decl.Value.(*ast.InfixExpression); isDiv && quotient.Operator == "/" {
		if container, isLen := lenOf(quotient.Left); isLen && tc.localBinding(container) {
			if k, isConst := constantIndex(quotient.Right); isConst && k >= 1 {
				return []extentFact{{kind: factDivUpper, container: container, other: decl.Name.Value, bound: k}}
			}
		}
	}
	// `hi: u32 = pages` copies a binding: the new binding inherits every
	// live bound of the old one (they are equal at this point; a later
	// write to either kills only its own facts).
	if source, isIdent := decl.Value.(*ast.Identifier); isIdent && tc.localBinding(source.Value) {
		var inherited []extentFact
		for _, fact := range tc.extentFacts {
			if fact.dead || fact.other != source.Value {
				continue
			}
			switch fact.kind {
			case factUpperBound, factIndexLit, factLowerLit, factDivUpper, factDivIndex, factIndexBound:
				copied := fact
				copied.other = decl.Name.Value
				inherited = append(inherited, copied)
			}
		}
		return inherited
	}
	var length int64
	switch value := decl.Value.(type) {
	case *ast.InvocationExpression:
		fn, isIdent := value.Function.(*ast.Identifier)
		if !isIdent || fn.Value != "subslice" || len(value.Arguments) != 3 {
			return nil
		}
		n, isConst := constantIndex(value.Arguments[2])
		if !isConst || n < 0 {
			return nil
		}
		length = n
	case *ast.SliceExpression:
		lo, loConst := constantIndex(value.Low)
		hi, hiConst := constantIndex(value.High)
		if !loConst || !hiConst || lo < 0 || hi < lo {
			return nil
		}
		length = hi - lo
	default:
		return nil
	}
	return []extentFact{{kind: factMinLen, container: decl.Name.Value, bound: length}}
}

// enterDeclarationFacts pushes a declaration's fact when the remaining
// statements of the block never reassign the binding — except that a
// literal lower bound survives a loop whose only write to the binding is
// its trailing increment under an upper bound (lowerBoundsSurviving), the
// increment only raising it.
func (tc *TypeChecker) enterDeclarationFacts(decl *ast.VariableDeclaration, rest []ast.Statement) {
	facts := tc.declarationFacts(decl)
	if len(facts) == 0 {
		return
	}
	flowSensitive := true
	for _, fact := range facts {
		if fact.kind == factMinLen {
			flowSensitive = false
		}
	}
	if flowSensitive {
		// A fact about a binding is killed flow-sensitively by any later
		// write to it — a direct assignment when it is checked, a loop on
		// its entry unless the loop preserves the bound
		// (lowerBoundsSurviving, upperBoundsSurviving) — so it is pushed
		// for the statements before that write.
		tc.pushExtentFacts(facts)
		return
	}
	names := factNames(facts)
	for _, stmt := range rest {
		if assignsAny(stmt, names, false) {
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
	return tc.enterFactScope(match.Scrutinee)
}

// lowerBoundsSurviving names the bindings whose literal lower bounds a
// loop keeps alive through its body: the loop's own condition bounds the
// binding above (so the increment cannot wrap), and the body's only write
// to it is the trailing `i = i + c` with c a literal, which only raises it
// (Oak.Extents.increment_keeps_lower_bound, increment_without_wrap). Any
// other write kills the bound on entry like every other fact.
func (tc *TypeChecker) lowerBoundsSurviving(loop *ast.WhileStatement, conditionFacts []extentFact) map[string]bool {
	keep := map[string]bool{}
	if loop == nil || loop.Body == nil || len(loop.Body.Statements) == 0 {
		return keep
	}
	var name string
	var value ast.Expression
	switch last := loop.Body.Statements[len(loop.Body.Statements)-1].(type) {
	case *ast.AssignmentStatement:
		if last.Name == nil {
			return keep
		}
		name, value = last.Name.Value, last.Value
	case *ast.IndexAssignmentStatement:
		if last.Target == nil || !last.Target.Dot {
			return keep
		}
		path, isPath := pathOf(last.Target)
		if !isPath {
			return keep
		}
		name, value = path, last.Value
	default:
		return keep
	}
	increment, isIncrement := value.(*ast.InfixExpression)
	if !isIncrement || increment.Operator != "+" {
		return keep
	}
	incrementOf := func(a, b ast.Expression) bool {
		path, isPath := pathOf(a)
		if !isPath || path != name {
			return false
		}
		c, isConst := constantIndex(b)
		return isConst && c >= 0
	}
	if !incrementOf(increment.Left, increment.Right) && !incrementOf(increment.Right, increment.Left) {
		return keep
	}
	bounded := false
	for _, fact := range conditionFacts {
		if (fact.kind == factIndexLit || fact.kind == factIndexBound) && fact.other == name && fact.offset == 0 {
			bounded = true
		}
	}
	if !bounded || assignsAny(loop.Body, map[string]bool{name: true}, true) || assignsAny(loop.Condition, map[string]bool{name: true}, false) {
		return keep
	}
	keep[name] = true
	return keep
}

// midpointOf reads `a + (b - a) / K` (either operand order of the sum)
// with K a literal of at least 2, and names a and b.
func midpointOf(expr ast.Expression) (low, high string, ok bool) {
	sum, isInfix := expr.(*ast.InfixExpression)
	if !isInfix || sum.Operator != "+" {
		return "", "", false
	}
	for _, order := range [][2]ast.Expression{{sum.Left, sum.Right}, {sum.Right, sum.Left}} {
		base, isPath := pathOf(order[0])
		div, isDiv := order[1].(*ast.InfixExpression)
		if !isPath || !isDiv || div.Operator != "/" {
			continue
		}
		k, isConst := constantIndex(div.Right)
		diff, isDiff := div.Left.(*ast.InfixExpression)
		if !isConst || k < 2 || !isDiff || diff.Operator != "-" {
			continue
		}
		upper, upperIsPath := pathOf(diff.Left)
		lower, lowerIsPath := pathOf(diff.Right)
		if upperIsPath && lowerIsPath && lower == base {
			return base, upper, true
		}
	}
	return "", "", false
}

// belowLive reports a live `low < high` relation between two bindings.
func (tc *TypeChecker) belowLive(low, high string) bool {
	for _, fact := range tc.extentFacts {
		if !fact.dead && fact.kind == factBelow && fact.other == low && fact.via == high {
			return true
		}
	}
	return false
}

// upperBoundsSurviving names the bindings whose upper bounds a loop keeps
// alive through its body: the body's first statement declares the
// midpoint `m = a + (x - a) / K` under the loop's own guard `a < x`, m is
// never written again, and every write to x in the body is `x = m` —
// which only lowers x (Oak.Extents.midpoint_under_bound,
// decreasing_keeps_upper_bound). This is the binary search: `hi = mid`
// keeps `hi <= len(keys)`, so `keys[mid]` is proven on every iteration.
func (tc *TypeChecker) upperBoundsSurviving(loop *ast.WhileStatement, conditionFacts []extentFact) map[string]bool {
	keep := map[string]bool{}
	if loop == nil || loop.Body == nil || len(loop.Body.Statements) == 0 {
		return keep
	}
	decl, isDecl := loop.Body.Statements[0].(*ast.VariableDeclaration)
	if !isDecl || decl.Name == nil || decl.Value == nil {
		return keep
	}
	low, high, isMidpoint := midpointOf(decl.Value)
	if !isMidpoint || strings.Contains(high, ".") || strings.Contains(low, ".") {
		return keep
	}
	below := false
	for _, fact := range conditionFacts {
		if fact.kind == factBelow && !fact.viaBinding && fact.other == low && fact.via == high {
			below = true
		}
	}
	if !below {
		return keep
	}
	m := decl.Name.Value
	rest := &ast.BlockStatement{Statements: loop.Body.Statements[1:]}
	if assignsAny(rest, map[string]bool{m: true}, false) || assignsAny(loop.Condition, map[string]bool{m: true, high: true}, false) {
		return keep
	}
	var writes []ast.Expression
	collectAssignments(rest, high, &writes)
	if len(writes) == 0 {
		return keep
	}
	for _, write := range writes {
		if ident, isIdent := write.(*ast.Identifier); !isIdent || ident.Value != m {
			return keep
		}
	}
	keep[high] = true
	return keep
}

// collectAssignments gathers the values written to a plain binding
// anywhere in the node, declarations included.
func collectAssignments(node ast.Node, name string, into *[]ast.Expression) {
	switch n := node.(type) {
	case nil:
	case *ast.BlockStatement:
		for _, stmt := range n.Statements {
			collectAssignments(stmt, name, into)
		}
	case *ast.BlockExpression:
		collectAssignments(n.Block, name, into)
	case *ast.UnsafeBlock:
		collectAssignments(n.Body, name, into)
	case *ast.AssignmentStatement:
		if n.Name != nil && n.Name.Value == name {
			*into = append(*into, n.Value)
		}
		collectAssignments(n.Value, name, into)
	case *ast.VariableDeclaration:
		if n.Name != nil && n.Name.Value == name {
			*into = append(*into, n.Value)
		}
		collectAssignments(n.Value, name, into)
	case *ast.WhileStatement:
		collectAssignments(n.Condition, name, into)
		collectAssignments(n.Body, name, into)
	case *ast.IfStatement:
		collectAssignments(n.Condition, name, into)
		collectAssignments(n.Consequence, name, into)
		collectAssignments(n.Alternative, name, into)
	case *ast.ExpressionStatement:
		collectAssignments(n.Expression, name, into)
	case *ast.IndexAssignmentStatement:
		collectAssignments(n.Value, name, into)
	case *ast.MatchExpression:
		collectAssignments(n.Scrutinee, name, into)
		for _, arm := range n.Arms {
			collectAssignments(arm.Body, name, into)
		}
	case *ast.InvocationExpression:
		for _, arg := range n.Arguments {
			collectAssignments(arg, name, into)
		}
	case *ast.InfixExpression:
		collectAssignments(n.Left, name, into)
		collectAssignments(n.Right, name, into)
	case *ast.PrefixExpression:
		collectAssignments(n.Right, name, into)
	}
}

// killFactsAssignedByExcept kills the facts a loop invalidates, keeping
// the literal lower bounds of the bindings lowerBoundsSurviving names and
// the upper bounds of the bindings upperBoundsSurviving names.
func (tc *TypeChecker) killFactsAssignedByExcept(node ast.Node, keepLower, keepUpper map[string]bool) {
	names := map[string]bool{}
	assignedNames(node, names)
	if len(names) == 0 {
		return
	}
	for i := range tc.extentFacts {
		fact := &tc.extentFacts[i]
		if fact.kind == factLowerLit && keepLower[fact.other] {
			continue
		}
		switch fact.kind {
		case factUpperBound, factIndexLit, factDivUpper, factDivIndex, factIndexBound:
			if keepUpper[fact.other] {
				continue
			}
		}
		if fact.dependsOn(names) {
			fact.dead = true
		}
	}
	for bound, facts := range tc.boolFacts {
		if names[bound] {
			delete(tc.boolFacts, bound)
			continue
		}
		kept := facts[:0]
		for _, fact := range facts {
			if !fact.dependsOn(names) {
				kept = append(kept, fact)
			}
		}
		tc.boolFacts[bound] = kept
	}
}

// loopExitFact is the lower bound a loop leaves behind: `while i < K` (a
// bare comparison with a literal, no break in the body) exits with K <= i
// (Oak.Extents.loop_exit_lower_bound); `i <= K` exits with K + 1 <= i.
func (tc *TypeChecker) loopExitFact(loop *ast.WhileStatement) []extentFact {
	infix, ok := loop.Condition.(*ast.InfixExpression)
	if !ok || containsBreak(loop.Body) {
		return nil
	}
	index, offset, isIndex := offsetIndex(infix.Left)
	if !isIndex || offset != 0 || !tc.localBinding(index) {
		return nil
	}
	if _, isConst := constantIndex(infix.Left); isConst {
		return nil
	}
	k, isConst := constantIndex(infix.Right)
	if !isConst || k < 0 {
		return nil
	}
	switch infix.Operator {
	case "<":
		return []extentFact{{kind: factLowerLit, other: index, bound: k}}
	case "<=":
		return []extentFact{{kind: factLowerLit, other: index, bound: k + 1}}
	}
	return nil
}

// containsBreak reports whether a loop body can leave the loop early: a
// break anywhere in it outside nested loops (whose breaks are their own).
func containsBreak(node ast.Node) bool {
	switch n := node.(type) {
	case nil:
		return false
	case *ast.BreakStatement:
		return true
	case *ast.BlockStatement:
		for _, stmt := range n.Statements {
			if containsBreak(stmt) {
				return true
			}
		}
	case *ast.BlockExpression:
		return containsBreak(n.Block)
	case *ast.UnsafeBlock:
		return containsBreak(n.Body)
	case *ast.ExpressionStatement:
		return containsBreak(n.Expression)
	case *ast.MatchExpression:
		for _, arm := range n.Arms {
			if containsBreak(arm.Body) {
				return true
			}
		}
	case *ast.IfStatement:
		return true // conservative: the branches are not walked here
	}
	return false
}

// recordVectorAccessProof marks `simd.load_E(v, index)` or
// `simd.store_E(s, index, x)` proven when the live facts cover every one
// of its L lanes, `index .. index + L - 1`: a constant index under a
// min-length fact of at least `index + L` (Oak.Extents.vector_under_min_length),
// `i + j` under an offset bound `i + K < len` with `j + L - 1 <= K`
// (vector_under_offset_bound), or `i + j` under a literal bound `i < U`
// with the length known to be at least `U - 1 + j + L`
// (vector_under_literal_bound). The backend then emits the access without
// its trap check. Anything else stays checked (docs/spec/93-simd.md
// section 1.2: a load past the end traps, never reads).
func (tc *TypeChecker) recordVectorAccessProof(call *ast.InvocationExpression, member string) {
	splitAt := strings.LastIndex(member, "_")
	if splitAt <= 0 || call == nil || len(call.Arguments) < 2 {
		return
	}
	op, suffix := member[:splitAt], member[splitAt+1:]
	if op != "load" && op != "store" {
		return
	}
	var lanes int64
	for _, shape := range SimdShapes {
		if shape.Suffix == suffix {
			lanes = int64(shape.Lanes)
		}
	}
	name, isPath := pathOf(call.Arguments[0])
	if lanes == 0 || !isPath || !tc.localBinding(name) {
		return
	}
	lengthAtLeast := func(n int64) bool {
		for _, fact := range tc.extentFacts {
			if !fact.dead && fact.kind == factMinLen && fact.container == name && fact.bound >= n {
				return true
			}
		}
		return false
	}
	proven := false
	if constant, isConst := constantIndex(call.Arguments[1]); isConst && constant >= 0 {
		proven = lengthAtLeast(constant + lanes)
	} else if index, offset, isIndex := offsetIndex(call.Arguments[1]); isIndex {
		for _, fact := range tc.extentFacts {
			if fact.dead || fact.other != index {
				continue
			}
			if fact.kind == factIndexBound && fact.container == name && offset+lanes-1 <= fact.offset {
				proven = true
			}
			if fact.kind == factIndexLit && fact.bound >= 1 && lengthAtLeast(fact.bound-1+offset+lanes) {
				proven = true
			}
		}
	}
	if !proven {
		return
	}
	if tc.provenIndices == nil {
		tc.provenIndices = make(map[string]bool)
	}
	tc.provenIndices[positionKey(call.Token)] = true
}
