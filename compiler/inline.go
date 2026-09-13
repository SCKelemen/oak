package compiler

// Proof-preserving inlining (docs/spec/90-backend.md section 9, "Inlining
// as a source transformation"). A private leaf helper of at most twelve
// lines is the shape the C backend already emits as a forced-inline
// function; this pass performs the same inlining on the source tree
// before the type checker runs, so the merged body carries the caller's
// extent facts into the callee's element accesses (typechecker/extents.go):
// a guard around the call proves the index inside the helper, and neither
// backend emits a bounds check for it. The rule is mechanical and visible:
// the same helpers are inlined at every optimization level, and a helper
// that is not inlined is exactly one the rule below excludes.
//
// The transformation is statement-level: the callee's statements are
// spliced before the statement holding the call, its declared names are
// renamed to fresh ones (Oak forbids shadowing), its parameters are bound
// to the arguments (a plain identifier argument substitutes directly when
// the callee never assigns the parameter, so the caller's facts about it
// apply unchanged; anything else is copied into a typed temporary), and
// its tail expression takes the call's place. A call in operand position
// binds the tail to a typed result temporary first. Nothing moves across a
// short-circuit operator, a match arm, a loop condition, or a function
// literal, and a helper that writes through a span parameter is inlined
// only where nothing else in the statement is evaluated.

import (
	"fmt"
	"reflect"
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/discipline"
	"github.com/SCKelemen/oak/token"
)

// inlineHelperLines is the C backend's bound on a forced-inline helper's
// source span (codegen.computeInlineHelpers); the two rules are one rule.
const inlineHelperLines = 12

type inlineCandidate struct {
	fn *ast.FunctionStatement
	// body is the helper's body as a block (an expression body wrapped).
	body *ast.BlockExpression
	// declared names the body introduces: locals and pattern bindings.
	declared map[string]bool
	// free names the body references without declaring (globals, types,
	// builtins); a caller declaring one of them cannot host the body.
	free map[string]bool
	// assigned parameters, which get a private copy instead of substitution.
	assigned map[string]bool
	// writtenParams are the parameters written through by element or member
	// assignment; only a span or view parameter may be, since the write
	// then reaches the same memory whether or not the call is inlined.
	writtenParams map[string]bool
	// writesThroughParam: an element or field write on a parameter, visible
	// to the caller when the parameter is a span.
	writesThroughParam bool
}

type inliner struct {
	functions  map[string]*ast.FunctionStatement
	candidates map[string]*inlineCandidate
	counter    int
}

// inlineHelpers rewrites every call to an inlinable helper in program. The
// pass runs in rounds: a helper that called only helpers becomes a leaf
// once those are spliced into it, and the next round inlines it in turn,
// so an accessor chain (`tkind` over `tword` over `term_at` over `state`)
// flattens to the element read it denotes. Rounds stop when a pass inlines
// nothing new; the bound keeps a pathological program from cycling.
func inlineHelpers(program *ast.Program) {
	if program == nil {
		return
	}
	in := &inliner{functions: map[string]*ast.FunctionStatement{}, candidates: map[string]*inlineCandidate{}}
	duplicates := map[string]bool{}
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil && fn.Receiver == nil {
			if in.functions[fn.Name.Value] != nil {
				duplicates[fn.Name.Value] = true
			}
			in.functions[fn.Name.Value] = fn
		}
	}
	const maxRounds = 8
	for round := 0; round < maxRounds; round++ {
		in.candidates = map[string]*inlineCandidate{}
		for name, fn := range in.functions {
			if duplicates[name] {
				continue
			}
			if cand := in.candidate(fn); cand != nil {
				in.candidates[name] = cand
			}
		}
		if len(in.candidates) == 0 {
			return
		}
		before := in.counter
		for _, stmt := range program.Statements {
			fn, ok := stmt.(*ast.FunctionStatement)
			if !ok || fn.Body == nil || fn.ExternSymbol != "" || fn.Name == nil {
				continue
			}
			if _, isLeaf := in.candidates[fn.Name.Value]; isLeaf && fn.Receiver == nil {
				continue // a leaf calls nothing
			}
			if fn.Kernel {
				// A kernel is analyzed and compiled as written
				// (docs/spec/56-kernels.md): its independence rule judges the
				// helper call, not an expansion the Metal emitter never sees.
				continue
			}
			body, wrapped := functionBlock(fn)
			if body == nil || body.Block == nil {
				continue
			}
			scope := &callerScope{declared: map[string]bool{}}
			collectDeclaredNames(reflect.ValueOf(fn), scope.declared)
			in.inlineBlock(body.Block, scope)
			if wrapped && (len(body.Block.Statements) != 1 || body.Block.Statements[0].(*ast.ExpressionStatement).Expression != fn.Body) {
				// An expression body (`f: (...) = expr`) that received hoisted
				// statements becomes the block it now is; one untouched stays as
				// written.
				fn.Body = body
			}
		}
		if in.counter == before {
			return
		}
	}
}

// functionBlock is a function's body as a block: the block itself, or an
// expression body (`f: (...): T = expr`) wrapped as the one-statement block
// it denotes (wrapped reports the second case). The prover's accessor
// helpers are all of the second form, and they are exactly the calls whose
// prologue, record copy, and guard the native backend paid for at every
// element read.
func functionBlock(fn *ast.FunctionStatement) (*ast.BlockExpression, bool) {
	if fn.Body == nil {
		return nil, false
	}
	if block, isBlock := fn.Body.(*ast.BlockExpression); isBlock {
		return block, false
	}
	tok, _ := ast.ExpressionToken(fn.Body)
	return &ast.BlockExpression{Token: tok, Block: &ast.BlockStatement{Token: tok, Statements: []ast.Statement{&ast.ExpressionStatement{Token: tok, Expression: fn.Body}}}}, true
}

// candidate applies the forced-inline rule and the pass's own body
// restrictions; nil when fn is not inlined.
func (in *inliner) candidate(fn *ast.FunctionStatement) *inlineCandidate {
	if fn.Receiver != nil || fn.ExternSymbol != "" || fn.AsmBacked || fn.NativeBacked || fn.Body == nil ||
		fn.Exported || len(fn.TypeParams) > 0 || fn.Name.Value == "main" || len(fn.Dispatch) > 0 ||
		fn.Kernel || fn.Theorem {
		return nil
	}
	if fn.EndToken.Line <= 0 || fn.EndToken.Line-fn.Token.Line > inlineHelperLines {
		return nil
	}
	body, _ := functionBlock(fn)
	if body == nil || body.Block == nil || len(body.Block.Statements) == 0 || body.Block.DeferredFrom > 0 {
		return nil
	}
	if !discipline.InlineHelperShape(fn, in.functions) {
		return nil
	}
	for _, p := range fn.Parameters {
		if p == nil || p.Name == nil || p.Variadic || p.Type == nil {
			return nil
		}
	}
	if !inlinableBody(reflect.ValueOf(body)) {
		return nil
	}
	scalarLocals := true
	walkSyntax(reflect.ValueOf(body), func(node any) bool {
		switch n := node.(type) {
		case *ast.VariableDeclaration:
			if n.Type == nil || !scalarTypeSyntax(n.Type) {
				scalarLocals = false
			}
		case *ast.BindingPattern:
			scalarLocals = false
		}
		return scalarLocals
	})
	if !scalarLocals {
		return nil
	}
	cand := &inlineCandidate{fn: fn, body: body, declared: map[string]bool{}, free: map[string]bool{}, assigned: map[string]bool{}, writtenParams: map[string]bool{}}
	params := map[string]bool{}
	for _, p := range fn.Parameters {
		params[p.Name.Value] = true
	}
	collectDeclaredNames(reflect.ValueOf(body), cand.declared)
	for name := range cand.declared {
		if params[name] {
			return nil // a parameter redeclared: not a shape the checker accepts anyway
		}
	}
	collectReferencedNames(reflect.ValueOf(body), cand.free)
	for name := range cand.declared {
		delete(cand.free, name)
	}
	for name := range params {
		delete(cand.free, name)
	}
	collectWrites(reflect.ValueOf(body), params, cand)
	paramTypes := map[string]ast.Expression{}
	for _, p := range fn.Parameters {
		paramTypes[p.Name.Value] = p.Type
	}
	for name := range cand.writtenParams {
		if !spanOrViewSyntax(paramTypes[name]) {
			return nil // a write into a by-value array or record copy
		}
	}
	return cand
}

// scalarTypeSyntax reports whether a type expression names a builtin
// scalar. Only scalars are copied into temporaries: a span, view, array, or
// record temporary would be a new binding with borrow consequences of its
// own (a reborrow suspending its parent until the block ends, a copy of an
// aggregate), where the call it replaces held the value for the call alone.
func scalarTypeSyntax(expr ast.Expression) bool {
	ident, ok := expr.(*ast.Identifier)
	if !ok {
		return false
	}
	switch ident.Value {
	case "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "u128", "int", "uint", "usize", "isize",
		"f16", "bf16", "f32", "f64", "Bool", "byte", "char":
		return true
	}
	return false
}

// spanOrViewSyntax reports whether a type expression spells a span ([*]T)
// or a view ([]T): the two forms whose element writes reach the caller's
// memory (parser.parseArrayType).
func spanOrViewSyntax(expr ast.Expression) bool {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index.Dot {
		return false
	}
	marker, ok := index.Index.(*ast.Identifier)
	return ok && (marker.Value == "*" || marker.Value == "")
}

// inlinableBody rejects bodies whose statements cannot be spliced into a
// caller: deferred statements, breaks (no loop to leave), function
// literals (their captures would need renaming), nested deferred blocks.
func inlinableBody(v reflect.Value) bool {
	ok := true
	walkSyntax(v, func(node any) bool {
		switch n := node.(type) {
		case *ast.BreakStatement, *ast.DeferStatement, *ast.FunctionLiteral, *ast.TryExpression:
			ok = false
			return false
		case *ast.BlockStatement:
			if n.DeferredFrom > 0 {
				ok = false
				return false
			}
		}
		return ok
	})
	return ok
}

type callerScope struct {
	declared map[string]bool
}

// inlineBlock rewrites the statements of one block in place.
func (in *inliner) inlineBlock(block *ast.BlockStatement, scope *callerScope) {
	if block == nil || block.DeferredFrom > 0 {
		return
	}
	out := make([]ast.Statement, 0, len(block.Statements))
	for _, stmt := range block.Statements {
		out = append(out, in.inlineStatement(stmt, scope)...)
	}
	block.Statements = out
}

// inlineStatement returns the statements that replace stmt: the hoisted
// callee statements followed by the rewritten statement, or nothing when
// the statement was a unit call whose body has no tail expression.
func (in *inliner) inlineStatement(stmt ast.Statement, scope *callerScope) []ast.Statement {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		if s.Value == nil {
			return []ast.Statement{s}
		}
		hoisted, _ := in.rewriteSlot(&s.Value, scope, false)
		return append(hoisted, s)
	case *ast.AssignmentStatement:
		if s.Value == nil {
			return []ast.Statement{s}
		}
		hoisted, _ := in.rewriteSlot(&s.Value, scope, false)
		return append(hoisted, s)
	case *ast.IndexAssignmentStatement:
		if s.Value == nil {
			return []ast.Statement{s}
		}
		hoisted := in.hoistOperands(&s.Value, scope)
		return append(hoisted, s)
	case *ast.ExpressionStatement:
		if s.Expression == nil {
			return []ast.Statement{s}
		}
		hoisted, dropped := in.rewriteSlot(&s.Expression, scope, true)
		if dropped {
			return hoisted
		}
		return append(hoisted, s)
	case *ast.WhileStatement:
		in.inlineBlock(s.Body, scope)
	case *ast.UnsafeBlock:
		in.inlineBlock(s.Body, scope)
	case *ast.BlockStatement:
		in.inlineBlock(s, scope)
	case *ast.IfStatement:
		in.inlineBlock(s.Consequence, scope)
		if s.Alternative != nil {
			in.inlineStatement(s.Alternative, scope)
		}
	}
	return []ast.Statement{stmt}
}

// rewriteSlot rewrites the whole value of a statement slot. A candidate
// call filling the slot is expanded in place: its tail expression becomes
// the slot's value (dropped reports a tail-less body, which leaves the slot
// with nothing to hold). A match filling the slot has its arms rewritten as
// slots of their own — in statement position every arm, since the backends
// lower a statement-position match to branches of statements; in a value
// position only arms that are already statement-bearing blocks, so no arm
// acquires statements where the backends expect a bare expression.
// Anything else is walked for calls in operand position.
func (in *inliner) rewriteSlot(slot *ast.Expression, scope *callerScope, statement bool) (hoisted []ast.Statement, dropped bool) {
	switch e := (*slot).(type) {
	case *ast.InvocationExpression:
		if cand := in.candidateOf(e); cand != nil {
			for i := range e.Arguments {
				hoisted = append(hoisted, in.hoistOperands(&e.Arguments[i], scope)...)
			}
			stmts, tail, ok := in.expand(e, cand, scope, true)
			if !ok || (!statement && containsBlock(tail)) {
				return hoisted, false
			}
			hoisted = append(hoisted, stmts...)
			if tail == nil {
				return hoisted, true
			}
			*slot = tail
			return hoisted, false
		}
	case *ast.MatchExpression:
		hoisted = in.hoistOperands(&e.Scrutinee, scope)
		for _, arm := range e.Arms {
			if arm == nil || arm.Body == nil {
				continue
			}
			if block, isBlock := arm.Body.(*ast.BlockExpression); isBlock {
				if statement || (block.Block != nil && len(block.Block.Statements) > 1) {
					in.inlineBlock(block.Block, scope)
				}
				continue
			}
			if !statement {
				continue
			}
			armHoisted, armDropped := in.rewriteSlot(&arm.Body, scope, true)
			if len(armHoisted) == 0 {
				continue
			}
			stmts := armHoisted
			if !armDropped {
				tok, _ := ast.ExpressionToken(arm.Body)
				stmts = append(stmts, &ast.ExpressionStatement{Token: tok, Expression: arm.Body})
			}
			arm.Body = &ast.BlockExpression{Token: arm.Token, Block: &ast.BlockStatement{Token: arm.Token, Statements: stmts}}
		}
		return hoisted, false
	case *ast.BlockExpression:
		if statement || (e.Block != nil && len(e.Block.Statements) > 1) {
			in.inlineBlock(e.Block, scope)
		}
		return nil, false
	}
	return in.hoistOperands(slot, scope), false
}

// hoistOperands walks an expression in evaluation order and hoists every
// candidate call in operand position into a typed result temporary.
func (in *inliner) hoistOperands(slot *ast.Expression, scope *callerScope) []ast.Statement {
	h := &hoister{in: in, scope: scope}
	h.walk(slot)
	return h.hoisted
}

type hoister struct {
	in      *inliner
	scope   *callerScope
	hoisted []ast.Statement
	// blocked is set once a call this pass does not inline has been passed
	// in evaluation order: hoisting a later call above it would reorder
	// two user-level effects.
	blocked bool
}

func (h *hoister) walk(slot *ast.Expression) {
	if slot == nil || *slot == nil {
		return
	}
	switch e := (*slot).(type) {
	case *ast.InvocationExpression:
		for i := range e.Arguments {
			h.walk(&e.Arguments[i])
		}
		cand := h.in.candidateOf(e)
		if cand == nil {
			if !h.in.pureBuiltinCall(e) {
				h.blocked = true
			}
			return
		}
		if h.blocked || !scalarTypeSyntax(cand.fn.ReturnType) {
			h.blocked = true
			return
		}
		stmts, tail, ok := h.in.expand(e, cand, h.scope, false)
		if !ok || tail == nil || containsBlock(tail) {
			h.blocked = true
			return
		}
		name := h.in.resultName()
		result := &ast.VariableDeclaration{
			Token: e.Token,
			Name:  identifierAt(e.Token, name),
			Type:  cloneExpression(cand.fn.ReturnType),
			Value: tail,
		}
		h.hoisted = append(append(h.hoisted, stmts...), result)
		*slot = identifierAt(e.Token, name)
	case *ast.InfixExpression:
		h.walk(&e.Left)
		if e.Operator == "&&" || e.Operator == "||" {
			return
		}
		h.walk(&e.Right)
	case *ast.PrefixExpression:
		h.walk(&e.Right)
	case *ast.IndexExpression:
		h.walk(&e.Left)
		if !e.Dot {
			h.walk(&e.Index)
		}
	case *ast.MatchExpression:
		h.walk(&e.Scrutinee)
		// Arms evaluate conditionally: nothing crosses them.
	case *ast.FunctionLiteral, *ast.BlockExpression, *ast.Identifier, *ast.IntegerLiteral, *ast.FloatLiteral, *ast.StringLiteral, *ast.Boolean:
		return
	default:
		// Other composite expressions (literals of arrays and records, casts
		// spelled as calls are handled above) evaluate their exported
		// expression slots in field order.
		v := reflect.ValueOf(*slot)
		if v.Kind() != reflect.Pointer || v.IsNil() {
			return
		}
		h.walkFields(v.Elem())
	}
}

func (h *hoister) walkFields(v reflect.Value) {
	switch v.Kind() {
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			f := v.Field(i)
			if !v.Type().Field(i).IsExported() {
				continue
			}
			if f.Kind() == reflect.Interface && f.Type() == reflect.TypeOf((*ast.Expression)(nil)).Elem() {
				if f.CanAddr() {
					h.walk(f.Addr().Interface().(*ast.Expression))
				}
				continue
			}
			h.walkFields(f)
		}
	case reflect.Slice:
		for i := 0; i < v.Len(); i++ {
			h.walkFields(v.Index(i))
		}
	case reflect.Map:
		// Record literal fields carry their order in FieldOrder; the map
		// shares the same expression nodes, so the slice walk covers them.
	}
}

// pureBuiltinCall reports whether a call names no user function: a type
// conversion, len, or another builtin. Reordering a pure read across one
// changes nothing but which trap fires first.
func (in *inliner) pureBuiltinCall(call *ast.InvocationExpression) bool {
	ident, ok := call.Function.(*ast.Identifier)
	if !ok {
		return false
	}
	if in.functions[ident.Value] != nil {
		return false
	}
	switch ident.Value {
	case "assert", "panic", "unreachable", "print", "println", "eprint", "eprintln", "exit":
		return false
	}
	return true
}

func (in *inliner) candidateOf(call *ast.InvocationExpression) *inlineCandidate {
	ident, ok := call.Function.(*ast.Identifier)
	if !ok || call.ResolvedMethod != "" {
		return nil
	}
	cand := in.candidates[ident.Value]
	if cand == nil || len(call.Arguments) != len(cand.fn.Parameters) {
		return nil
	}
	return cand
}

func (in *inliner) resultName() string {
	in.counter++
	return "__inl" + strconv.Itoa(in.counter) + "_r"
}

// expand produces the statements standing in for call and the callee's
// tail expression (nil when the body ends in a statement). whole reports
// that the call is a statement's entire value, the only position where a
// helper writing through a parameter may be inlined.
func (in *inliner) expand(call *ast.InvocationExpression, cand *inlineCandidate, scope *callerScope, whole bool) ([]ast.Statement, ast.Expression, bool) {
	if cand.writesThroughParam && !whole {
		return nil, nil, false
	}
	for name := range cand.free {
		if scope.declared[name] {
			return nil, nil, false
		}
	}
	for i, p := range cand.fn.Parameters {
		if ident, isIdent := call.Arguments[i].(*ast.Identifier); isIdent && !cand.assigned[p.Name.Value] && !cand.declared[ident.Value] {
			continue
		}
		if !scalarTypeSyntax(p.Type) {
			return nil, nil, false
		}
	}
	in.counter++
	prefix := "__inl" + strconv.Itoa(in.counter) + "_"
	context := helperContext(cand.fn.Name.Token.SemanticContext, fmt.Sprintf("inline:%s:%d", cand.fn.Name.Value, in.counter))
	rename := map[string]string{}
	var stmts []ast.Statement
	for i, p := range cand.fn.Parameters {
		arg := call.Arguments[i]
		if ident, isIdent := arg.(*ast.Identifier); isIdent && !cand.assigned[p.Name.Value] && !cand.declared[ident.Value] {
			rename[p.Name.Value] = ident.Value
			continue
		}
		temp := prefix + "a" + strconv.Itoa(i)
		typ := cloneExpression(p.Type)
		stampSemanticContext(reflect.ValueOf(typ), context)
		stmts = append(stmts, &ast.VariableDeclaration{Token: call.Token, Name: identifierAt(call.Token, temp), Type: typ, Value: arg})
		rename[p.Name.Value] = temp
	}
	for name := range cand.declared {
		rename[name] = prefix + name
	}
	body := cloneExpression(cand.body).(*ast.BlockExpression)
	stampSemanticContext(reflect.ValueOf(body), context)
	renameBindings(reflect.ValueOf(body), rename)
	bodyStmts := body.Block.Statements
	var tail ast.Expression
	if last, ok := bodyStmts[len(bodyStmts)-1].(*ast.ExpressionStatement); ok && !last.Discard {
		tail = last.Expression
		bodyStmts = bodyStmts[:len(bodyStmts)-1]
	}
	stmts = append(stmts, bodyStmts...)
	for name := range cand.declared {
		scope.declared[prefix+name] = true
	}
	return stmts, tail, true
}

// containsBlock reports whether an expression holds a block anywhere — a
// match with block arms, typically. Such a value is only lowered in
// statement position (a statement-position match becomes branches of
// statements); in a declaration or operand it would have to be emitted as
// an expression, which the C backend cannot do for a block.
func containsBlock(expr ast.Expression) bool {
	if expr == nil {
		return false
	}
	found := false
	walkSyntax(reflect.ValueOf(expr), func(node any) bool {
		if _, isBlock := node.(*ast.BlockExpression); isBlock {
			found = true
		}
		return !found
	})
	return found
}

func identifierAt(tok token.Token, name string) *ast.Identifier {
	tok.Literal = name
	return &ast.Identifier{Token: tok, Value: name}
}

// walkSyntax visits every pointer node in a syntax tree, pre-order; visit
// returns false to stop descending.
func walkSyntax(v reflect.Value, visit func(node any) bool) {
	switch v.Kind() {
	case reflect.Interface, reflect.Pointer:
		if v.IsNil() {
			return
		}
		if v.Kind() == reflect.Pointer {
			if !visit(v.Interface()) {
				return
			}
		}
		walkSyntax(v.Elem(), visit)
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			if v.Type().Field(i).IsExported() {
				walkSyntax(v.Field(i), visit)
			}
		}
	case reflect.Slice:
		for i := 0; i < v.Len(); i++ {
			walkSyntax(v.Index(i), visit)
		}
	case reflect.Map:
		iter := v.MapRange()
		for iter.Next() {
			walkSyntax(iter.Value(), visit)
		}
	}
}

// collectDeclaredNames gathers every name a syntax tree binds: parameters,
// local declarations, pattern bindings, and function-literal arguments.
func collectDeclaredNames(v reflect.Value, into map[string]bool) {
	walkSyntax(v, func(node any) bool {
		switch n := node.(type) {
		case *ast.FunctionParameter:
			if n.Name != nil {
				into[n.Name.Value] = true
			}
		case *ast.VariableDeclaration:
			if n.Name != nil {
				into[n.Name.Value] = true
			}
		case *ast.BindingPattern:
			if n.Name != nil {
				into[n.Name.Value] = true
			}
		case *ast.FunctionLiteral:
			for _, arg := range n.Arguments {
				if arg != nil {
					into[arg.Value] = true
				}
			}
		}
		return true
	})
}

// collectReferencedNames gathers every identifier used as a name (not a
// member label or a variant name) in a syntax tree.
func collectReferencedNames(v reflect.Value, into map[string]bool) {
	walkSyntax(v, func(node any) bool {
		switch n := node.(type) {
		case *ast.Identifier:
			into[n.Value] = true
		case *ast.IndexExpression:
			if n.Dot {
				collectReferencedNames(reflect.ValueOf(n.Left), into)
				return false
			}
		case *ast.FieldAccessorExpression:
			return false
		case *ast.VariantPattern:
			if n.Payload != nil {
				collectReferencedNames(reflect.ValueOf(n.Payload), into)
			}
			return false
		}
		return true
	})
}

// collectWrites records which parameters the body assigns and whether it
// writes an element or member through one.
func collectWrites(v reflect.Value, params map[string]bool, cand *inlineCandidate) {
	walkSyntax(v, func(node any) bool {
		switch n := node.(type) {
		case *ast.AssignmentStatement:
			if n.Name != nil && params[n.Name.Value] {
				cand.assigned[n.Name.Value] = true
			}
		case *ast.IndexAssignmentStatement:
			if root := indexRoot(n.Target); root != nil && params[root.Value] {
				cand.writesThroughParam = true
				cand.writtenParams[root.Value] = true
			}
		}
		return true
	})
}

func indexRoot(e ast.Expression) *ast.Identifier {
	for e != nil {
		switch n := e.(type) {
		case *ast.Identifier:
			return n
		case *ast.IndexExpression:
			e = n.Left
		default:
			return nil
		}
	}
	return nil
}

// renameBindings applies rename to every identifier occurrence that names a
// binding: member labels, variant names, field accessors, and the type
// annotations of declarations are left alone.
func renameBindings(v reflect.Value, rename map[string]string) {
	walkSyntax(v, func(node any) bool {
		switch n := node.(type) {
		case *ast.Identifier:
			if to, ok := rename[n.Value]; ok {
				n.Value = to
				n.Token.Literal = to
			}
		case *ast.IndexExpression:
			if n.Dot {
				renameBindings(reflect.ValueOf(n.Left), rename)
				return false
			}
		case *ast.FieldAccessorExpression:
			return false
		case *ast.VariantPattern:
			if n.Payload != nil {
				renameBindings(reflect.ValueOf(n.Payload), rename)
			}
			return false
		case *ast.VariableDeclaration:
			if n.Name != nil {
				if to, ok := rename[n.Name.Value]; ok {
					n.Name.Value = to
					n.Name.Token.Literal = to
				}
			}
			renameBindings(reflect.ValueOf(n.Value), rename)
			return false
		case *ast.BindingPattern:
			if n.Name != nil {
				if to, ok := rename[n.Name.Value]; ok {
					n.Name.Value = to
					n.Name.Token.Literal = to
				}
			}
			return false
		}
		return true
	})
}
