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
)

type extentFactKind int

const (
	factMinLen     extentFactKind = iota // len(container) >= bound
	factIndexBound                       // index < len(container)
	factSameLen                          // len(container) == len(other)
	factUpperBound                       // other <= len(container), other a local binding
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
				if fact.dead || fact.kind != factUpperBound || fact.other != pair.bound {
					continue
				}
				facts = append(facts, extentFact{kind: factIndexBound, container: fact.container, other: pair.index, via: pair.bound, viaBinding: fact.viaBinding, indexDirect: true})
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

	minusLen, minusK, rightIsLenMinus := lenMinus(infix.Right)

	switch infix.Operator {
	case ">=":
		if leftIsLen && rightIsConst && rightConst >= 0 && local(leftLen) {
			return []extentFact{{kind: factMinLen, container: leftLen, bound: rightConst}}, nil
		}
		// len(v) >= n: n bounds indices into v (Oak.Extents.bound_through_upper).
		if leftIsLen && rightIsIndex && !rightIsConst && rightOffset == 0 && local(leftLen, rightIndex) {
			return []extentFact{{kind: factUpperBound, container: leftLen, other: rightIndex}}, nil
		}
	case ">":
		if leftIsLen && rightIsConst && rightConst >= 0 && local(leftLen) {
			return []extentFact{{kind: factMinLen, container: leftLen, bound: rightConst + 1}}, nil
		}
		// len(v) > i: a plain index bound. An offset form (len(v) > i + K)
		// proves nothing, because fixed-width i + K may have wrapped.
		if leftIsLen && rightIsIndex && !rightIsConst && rightOffset == 0 && local(leftLen, rightIndex) {
			// len(v) > n is both an index bound and an upper bound for n.
			return []extentFact{
				{kind: factIndexBound, container: leftLen, other: rightIndex},
				{kind: factUpperBound, container: leftLen, other: rightIndex},
			}, nil
		}
	case "<=":
		if leftIsConst && rightIsLen && leftConst >= 0 && local(rightLen) {
			return []extentFact{{kind: factMinLen, container: rightLen, bound: leftConst}}, nil
		}
		// n <= len(v): n bounds indices into v.
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsLen && local(leftIndex, rightLen) {
			return []extentFact{{kind: factUpperBound, container: rightLen, other: leftIndex}}, nil
		}
		// i <= len(v) - K with len(v) >= K known: i + (K - 1) < len(v),
		// and the subtraction cannot wrap (Oak.Extents.guard_without_wrap).
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsLenMinus && minusK >= 1 &&
			local(leftIndex, minusLen) && tc.minLengthKnown(minusLen, minusK, earlier) {
			return []extentFact{{kind: factIndexBound, container: minusLen, other: leftIndex, offset: minusK - 1}}, nil
		}
	case "<":
		if leftIsConst && rightIsLen && leftConst >= 0 && local(rightLen) {
			return []extentFact{{kind: factMinLen, container: rightLen, bound: leftConst + 1}}, nil
		}
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsLen && local(leftIndex, rightLen) {
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
			return nil, []indexPair{{index: leftIndex, bound: rightIndex}}
		}
		// i < len(v) - K with len(v) >= K known: i + K < len(v)
		// (Oak.Extents.guard_without_wrap).
		if leftIsIndex && !leftIsConst && leftOffset == 0 && rightIsLenMinus &&
			local(leftIndex, minusLen) && tc.minLengthKnown(minusLen, minusK, earlier) {
			return []extentFact{{kind: factIndexBound, container: minusLen, other: leftIndex, offset: minusK}}, nil
		}
	case "==":
		if leftIsLen && rightIsLen && local(leftLen, rightLen) {
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
	return names[fact.container] || (fact.other != "" && names[fact.other]) || (fact.via != "" && names[fact.via])
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
		if fact.via != "" && assigned[fact.via] {
			continue
		}
		if fact.viaBinding {
			// The container and the composed-through binding came from the
			// remembered condition; a directly compared index is re-checked.
			if assigned[fact.container] || (!fact.indexDirect && fact.other != "" && assigned[fact.other]) {
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
			if fact.dead {
				continue
			}
			if fact.kind == factMinLen && fact.container == name && constant < fact.bound {
				proven = true // Oak.Extents.constant_under_min_length
			}
		}
	} else if index, offset, isIndex := offsetIndex(expr.Index); isIndex {
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
	if !proven {
		return
	}
	if tc.provenIndices == nil {
		tc.provenIndices = make(map[string]bool)
	}
	tc.provenIndices[positionKey(expr.Token)] = true
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
	return tc.enterFactScope(match.Scrutinee)
}
