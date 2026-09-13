package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// Left-to-right evaluation (docs/spec/10-syntax.md §3d, 90-backend.md
// "Evaluation order").
//
// Oak evaluates the operands of an operator, the arguments of a call, the
// elements of an array literal, the fields of a record literal, and the
// operands of an index or slice left to right; the interpreter does. C
// leaves every one of those orders unspecified, and gcc on x86-64 evaluates
// a call's arguments right to left — so `bump(..) + bump(..)`, lowered to
// `oak_add_u32( bump(..), bump(..) )`, ran backwards under gcc.
//
// This pass makes the emitted C realize the rule. At every statement
// position the backend sequences the statement's expression: each group of
// siblings C may reorder is examined, and when two or more of its members
// could observe the order — a member is *effectful* when it contains a call
// the C compiler is free to reorder (a program function, a method, an
// extern, an atomic builtin, a runtime builtin), and *sensitive* when it is
// effectful or reads a global or a variable an effectful sibling may write
// through a span or address argument — the sensitive members are evaluated
// into C temporaries in source order before the statement, and the
// statement reads the temporaries. Pure members (literals, arithmetic on
// locals, casts, conversions, `len`, borrow constructions, field reads no
// sibling can write) stay inline: C may evaluate them whenever it likes
// because nothing can tell.
//
// Conditional contexts are never hoisted out of. The arms of a match in
// expression position and the right operand of `&&`/`||` evaluate only when
// chosen, so when one of them needs sequencing the whole conditional is
// emitted in statement form (`T t; if ( c ) { ...; t = a; } else { t = b; }`)
// and the statement reads `t`. A while condition needing sequencing is
// emitted as `for (;;) { temporaries; if ( !( cond ) ) { break; } body }`,
// so the temporaries are re-evaluated on every iteration.
//
// The temporary's C type is the type the checker recorded for the member
// (tc.Env().CheckedExpressionType); when it has no C spelling the backend
// falls back to `__typeof__` (counted in seqTypeofFallbacks, which the
// golden corpus keeps at zero).

// effects summarizes what an expression does that C's unspecified order
// could reorder observably.
type effects struct {
	effectful bool            // contains a call the C compiler may order freely
	global    bool            // reads a name that is not a local of the function
	reads     map[string]bool // roots of the locals it reads
	writes    map[string]bool // roots an effectful call may write through
}

func (e *effects) merge(o effects) {
	e.effectful = e.effectful || o.effectful
	e.global = e.global || o.global
	for name := range o.reads {
		e.read(name)
	}
	for name := range o.writes {
		e.write(name)
	}
}

func (e *effects) read(name string) {
	if e.reads == nil {
		e.reads = map[string]bool{}
	}
	e.reads[name] = true
}

func (e *effects) write(name string) {
	if e.writes == nil {
		e.writes = map[string]bool{}
	}
	e.writes[name] = true
}

// pureCallNames are the compiler-known callees whose value depends only on
// their operands: no call the C compiler could move relative to another.
var pureCallNames = map[string]bool{
	"len": true, "core_len": true, "core_index": true, "core_slice": true,
	"view": true, "span": true, "view_as": true, "span_as": true, "subslice": true,
	"size_of": true, "align_of": true, "offset_of": true, "static_assert": true, "address_of": true,
	"str_bytes": true, "text_literal": true,
}

// pureCall reports whether a call is one the sequencing pass may leave
// inline: a cast, a conversion, checked arithmetic, a float intrinsic, a
// layout query, a borrow construction, a refinement's guard, a sealed
// coercion. Every program function, method, extern, atomic and runtime
// builtin — and every callee the backend does not recognize — is effectful.
func (cg *CodeGenerator) pureCall(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	if _, isAccessor := call.Function.(*ast.FieldAccessorExpression); isAccessor {
		return true
	}
	if name, isRefinement := tc.RefinedConstruction(call.Token); isRefinement && name != "" && len(call.Arguments) == 1 {
		return true
	}
	ident, ok := call.Function.(*ast.Identifier)
	if !ok {
		return false
	}
	name := ident.Value
	if cg.isLocalName(name) || cg.programFunctions[name] != nil {
		return false
	}
	if _, isAtomic := semir.LookupAtomicBuiltin(name); isAtomic {
		return false
	}
	if runtimeBuiltins[name] != "" {
		return false
	}
	if _, isCast := primitiveCasts[name]; isCast {
		return true
	}
	if _, _, _, isConversion := typechecker.ConversionParts(name); isConversion {
		return true
	}
	if isArithmeticHelperName(name) || typechecker.FloatIntrinsicName(name) || pureCallNames[name] {
		return true
	}
	if strings.HasPrefix(name, "__abstract_") || strings.HasPrefix(name, "__concrete_") {
		return true
	}
	return false
}

// isArithmeticHelperName recognizes {type}_{checked|saturating|trapping}_{op}
// (docs/spec/20-types.md §11.1a).
func isArithmeticHelperName(name string) bool {
	parts := strings.Split(name, "_")
	if len(parts) != 3 {
		return false
	}
	switch parts[1] {
	case "checked", "saturating", "trapping":
	default:
		return false
	}
	switch parts[2] {
	case "add", "sub", "mul", "div", "rem", "neg", "shl", "shr", "abs":
		return true
	}
	return false
}

// unhoistable marks the argument shapes the call site expands itself
// (boundary spans, C strings, argv, out parameters) and the expressions
// with no value to hold: they are never moved into a temporary.
func (cg *CodeGenerator) unhoistable(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.BlockExpression, *ast.FunctionLiteral, *ast.StringLiteral, *ast.IntegerLiteral, *ast.FloatLiteral, *ast.Boolean, *ast.Identifier, *ast.FieldAccessorExpression:
		return true
	case *ast.InvocationExpression:
		if _, ok := boundarySpanArgument(e); ok {
			return true
		}
		if _, ok := cStringArgument(e); ok {
			return true
		}
		if _, _, ok := argvArgument(e); ok {
			return true
		}
		if _, ok := outArgument(e); ok {
			return true
		}
		if _, _, ok := libraryCallTarget(e.Function); ok {
			return true
		}
		if cg.custodyTransitionOperand(e) != nil {
			return true
		}
	case *ast.MatchExpression:
		// An ADT match has no expression-position lowering to hoist into.
		if len(e.Arms) > 0 {
			if _, isVariant := e.Arms[0].Pattern.(*ast.VariantPattern); isVariant {
				return true
			}
		}
	}
	return false
}

// writeRoot names the variable an argument lets the callee write through:
// `span(&x)` and `&x` name x, and a local that is itself a span or a
// buffer names that local.
func (cg *CodeGenerator) writeRoot(arg ast.Expression) (string, bool) {
	switch a := arg.(type) {
	case *ast.PrefixExpression:
		if a.Operator == "&" {
			if root, ok := rootIdentifier(a.Right); ok {
				return root, true
			}
		}
	case *ast.InvocationExpression:
		if ident, ok := a.Function.(*ast.Identifier); ok && (ident.Value == "span" || ident.Value == "span_as" || ident.Value == "subslice") && len(a.Arguments) >= 1 {
			return cg.writeRoot(a.Arguments[0])
		}
	case *ast.Identifier:
		switch cg.localTypes[a.Value].kind {
		case containerSpan, containerBuffer:
			return a.Value, true
		}
	case *ast.IndexExpression:
		if a.Dot {
			return cg.writeRoot(a.Left)
		}
	}
	return "", false
}

// rootIdentifier finds the variable at the base of an access path.
func rootIdentifier(expr ast.Expression) (string, bool) {
	for {
		switch e := expr.(type) {
		case *ast.Identifier:
			return e.Value, true
		case *ast.IndexExpression:
			expr = e.Left
		case *ast.SliceExpression:
			expr = e.Seq
		default:
			return "", false
		}
	}
}

// summarize computes the effects of an expression, conditional parts
// included (they may or may not run, so they count).
func (cg *CodeGenerator) summarize(expr ast.Expression, tc *typechecker.TypeChecker) effects {
	var e effects
	switch x := expr.(type) {
	case nil:
	case *ast.Identifier:
		if cg.isLocalName(x.Value) {
			e.read(x.Value)
		} else if cg.programFunctions[x.Value] == nil {
			e.global = true
		}
	case *ast.InvocationExpression:
		if _, isIdent := x.Function.(*ast.Identifier); !isIdent {
			e.merge(cg.summarize(x.Function, tc))
		}
		for _, arg := range x.Arguments {
			e.merge(cg.summarize(arg, tc))
		}
		if !cg.pureCall(x, tc) {
			e.effectful = true
			for _, arg := range x.Arguments {
				if root, ok := cg.writeRoot(arg); ok {
					e.write(root)
				}
			}
			if access, isDot := x.Function.(*ast.IndexExpression); isDot && access.Dot {
				// A method may write its receiver's state.
				if root, ok := rootIdentifier(access.Left); ok {
					e.write(root)
				}
			}
		}
	case *ast.IndexExpression:
		e.merge(cg.summarize(x.Left, tc))
		if !x.Dot {
			e.merge(cg.summarize(x.Index, tc))
		}
	default:
		for _, child := range expressionChildren(expr) {
			e.merge(cg.summarize(child, tc))
		}
		if _, isBlock := expr.(*ast.BlockExpression); isBlock {
			e.effectful = true
		}
	}
	return e
}

// expressionChildren lists every subexpression of a node, conditional
// parts included.
func expressionChildren(expr ast.Expression) []ast.Expression {
	switch x := expr.(type) {
	case *ast.InfixExpression:
		return []ast.Expression{x.Left, x.Right}
	case *ast.PrefixExpression:
		return []ast.Expression{x.Right}
	case *ast.IndexExpression:
		if x.Dot {
			return []ast.Expression{x.Left}
		}
		return []ast.Expression{x.Left, x.Index}
	case *ast.SliceExpression:
		return []ast.Expression{x.Seq, x.Low, x.High}
	case *ast.InvocationExpression:
		children := []ast.Expression{x.Function}
		return append(children, x.Arguments...)
	case *ast.ArrayLiteral:
		return x.Elements
	case *ast.RecordLiteral:
		children := make([]ast.Expression, 0, len(x.FieldOrder))
		for _, field := range x.FieldOrder {
			children = append(children, field.Value)
		}
		return children
	case *ast.VariantExpression:
		return []ast.Expression{x.Payload}
	case *ast.MatchExpression:
		children := []ast.Expression{x.Scrutinee}
		for _, arm := range x.Arms {
			children = append(children, arm.Body)
		}
		return children
	case *ast.BlockExpression:
		if x.Block == nil {
			return nil
		}
		var children []ast.Expression
		for _, stmt := range x.Block.Statements {
			switch s := stmt.(type) {
			case *ast.ExpressionStatement:
				children = append(children, s.Expression)
			case *ast.VariableDeclaration:
				children = append(children, s.Value)
			case *ast.AssignmentStatement:
				children = append(children, s.Value)
			}
		}
		return children
	}
	return nil
}

// sensitiveMembers marks the members of one unsequenced group whose
// evaluation order is observable, and returns each member's summary.
func (cg *CodeGenerator) sensitiveMembers(members []ast.Expression, tc *typechecker.TypeChecker) ([]bool, []effects) {
	summaries := make([]effects, len(members))
	for i, m := range members {
		if m != nil {
			summaries[i] = cg.summarize(m, tc)
		}
	}
	sensitive := make([]bool, len(members))
	for i, m := range members {
		if m == nil {
			continue
		}
		sensitive[i] = summaries[i].effectful || cg.conflicts(summaries[i], i, summaries)
	}
	return sensitive, summaries
}

// conflicts reports whether a member's reads could observe an effectful
// sibling: it reads a global, or a variable the sibling may write.
func (cg *CodeGenerator) conflicts(member effects, index int, summaries []effects) bool {
	for j, sibling := range summaries {
		if j == index || !sibling.effectful {
			continue
		}
		if member.global {
			return true
		}
		for name := range member.reads {
			if sibling.writes[name] {
				return true
			}
		}
	}
	return false
}

// groupNeedsSequencing reports whether a group has two or more sensitive
// members the pass can hoist.
func (cg *CodeGenerator) groupNeedsSequencing(members []ast.Expression, tc *typechecker.TypeChecker) bool {
	count := 0
	sensitive, _ := cg.sensitiveMembers(members, tc)
	for i, s := range sensitive {
		if s && !cg.unhoistable(members[i]) {
			count++
		}
	}
	return count >= 2
}

// needsSequencing reports whether sequencing expr at a statement position
// would emit anything — the dry run the while and conditional lowerings
// decide their shape by.
func (cg *CodeGenerator) needsSequencing(expr ast.Expression, tc *typechecker.TypeChecker) bool {
	if cg.noSequence {
		return false
	}
	switch e := expr.(type) {
	case nil:
		return false
	case *ast.InfixExpression:
		if e.Operator == "&&" || e.Operator == "||" {
			return cg.needsSequencing(e.Left, tc) || cg.needsSequencing(e.Right, tc)
		}
	case *ast.MatchExpression:
		if cg.needsSequencing(e.Scrutinee, tc) {
			return true
		}
		if cg.unhoistable(e) {
			return false
		}
		for _, arm := range e.Arms {
			if cg.needsSequencing(arm.Body, tc) {
				return true
			}
		}
		return false
	case *ast.BlockExpression:
		return false
	}
	members := cg.groupOf(expr)
	if len(members) > 1 && cg.groupNeedsSequencing(members, tc) {
		return true
	}
	for _, m := range members {
		if cg.needsSequencing(m, tc) {
			return true
		}
	}
	return false
}

// groupOf lists the siblings of a node that C may evaluate in any order:
// the unsequenced group. Conditional constructs return nothing here; they
// are handled by their own cases.
func (cg *CodeGenerator) groupOf(expr ast.Expression) []ast.Expression {
	switch x := expr.(type) {
	case *ast.InfixExpression:
		if x.Operator == "&&" || x.Operator == "||" {
			return nil
		}
		return []ast.Expression{x.Left, x.Right}
	case *ast.PrefixExpression:
		return []ast.Expression{x.Right}
	case *ast.IndexExpression:
		if x.Dot {
			return []ast.Expression{x.Left}
		}
		return []ast.Expression{x.Left, x.Index}
	case *ast.SliceExpression:
		return []ast.Expression{x.Seq, x.Low, x.High}
	case *ast.InvocationExpression:
		members := make([]ast.Expression, 0, len(x.Arguments)+1)
		members = append(members, cg.calleeOperand(x))
		return append(members, x.Arguments...)
	case *ast.ArrayLiteral:
		return x.Elements
	case *ast.RecordLiteral:
		members := make([]ast.Expression, 0, len(x.FieldOrder))
		for _, field := range x.FieldOrder {
			members = append(members, field.Value)
		}
		return members
	case *ast.VariantExpression:
		return []ast.Expression{x.Payload}
	}
	return nil
}

// calleeOperand is the part of a callee that is evaluated: the receiver of
// a method call, or a callee expression that is not a plain name. A named
// function is not an operand.
func (cg *CodeGenerator) calleeOperand(call *ast.InvocationExpression) ast.Expression {
	switch fn := call.Function.(type) {
	case *ast.Identifier, *ast.FieldAccessorExpression:
		return nil
	case *ast.IndexExpression:
		if fn.Dot {
			if _, _, isLibrary := libraryCallTarget(call.Function); isLibrary {
				return nil
			}
			return fn.Left
		}
	}
	return call.Function
}

// sequence rewrites expr so that C evaluates its sensitive members left to
// right, writing the temporaries it needs at the current statement
// position. Nodes nothing was hoisted from are returned as they are.
func (cg *CodeGenerator) sequence(expr ast.Expression, tc *typechecker.TypeChecker) ast.Expression {
	if cg.noSequence || expr == nil {
		return expr
	}
	switch e := expr.(type) {
	case *ast.InfixExpression:
		if e.Operator == "&&" || e.Operator == "||" {
			left := cg.sequence(e.Left, tc)
			if cg.needsSequencing(e.Right, tc) {
				rebuilt := *e
				rebuilt.Left = left
				return cg.hoistStatementForm(&rebuilt, e, tc)
			}
			if left == e.Left {
				return e
			}
			rebuilt := *e
			rebuilt.Left = left
			return &rebuilt
		}
		members := cg.sequenceGroup([]ast.Expression{e.Left, e.Right}, tc)
		if members[0] == e.Left && members[1] == e.Right {
			return e
		}
		rebuilt := *e
		rebuilt.Left, rebuilt.Right = members[0], members[1]
		return &rebuilt
	case *ast.PrefixExpression:
		right := cg.sequence(e.Right, tc)
		if right == e.Right {
			return e
		}
		rebuilt := *e
		rebuilt.Right = right
		return &rebuilt
	case *ast.IndexExpression:
		if e.Dot {
			left := cg.sequence(e.Left, tc)
			if left == e.Left {
				return e
			}
			rebuilt := *e
			rebuilt.Left = left
			return &rebuilt
		}
		members := cg.sequenceGroup([]ast.Expression{e.Left, e.Index}, tc)
		if members[0] == e.Left && members[1] == e.Index {
			return e
		}
		rebuilt := *e
		rebuilt.Left, rebuilt.Index = members[0], members[1]
		return &rebuilt
	case *ast.SliceExpression:
		members := cg.sequenceGroup([]ast.Expression{e.Seq, e.Low, e.High}, tc)
		if members[0] == e.Seq && members[1] == e.Low && members[2] == e.High {
			return e
		}
		rebuilt := *e
		rebuilt.Seq, rebuilt.Low, rebuilt.High = members[0], members[1], members[2]
		return &rebuilt
	case *ast.InvocationExpression:
		operand := cg.calleeOperand(e)
		members := make([]ast.Expression, 0, len(e.Arguments)+1)
		members = append(members, operand)
		members = append(members, e.Arguments...)
		sequenced := cg.sequenceGroup(members, tc)
		changed := sequenced[0] != operand
		for i, arg := range e.Arguments {
			changed = changed || sequenced[i+1] != arg
		}
		if !changed {
			return e
		}
		rebuilt := *e
		rebuilt.Arguments = sequenced[1:]
		if sequenced[0] != operand {
			if access, isDot := e.Function.(*ast.IndexExpression); isDot && access.Dot {
				receiver := *access
				receiver.Left = sequenced[0]
				rebuilt.Function = &receiver
			} else {
				rebuilt.Function = sequenced[0]
			}
		}
		return &rebuilt
	case *ast.ArrayLiteral:
		sequenced := cg.sequenceGroup(e.Elements, tc)
		changed := false
		for i, elem := range e.Elements {
			changed = changed || sequenced[i] != elem
		}
		if !changed {
			return e
		}
		rebuilt := *e
		rebuilt.Elements = sequenced
		return &rebuilt
	case *ast.RecordLiteral:
		members := make([]ast.Expression, 0, len(e.FieldOrder))
		for _, field := range e.FieldOrder {
			members = append(members, field.Value)
		}
		sequenced := cg.sequenceGroup(members, tc)
		changed := false
		for i := range members {
			changed = changed || sequenced[i] != members[i]
		}
		if !changed {
			return e
		}
		rebuilt := *e
		rebuilt.FieldOrder = make([]ast.RecordField, len(e.FieldOrder))
		rebuilt.Fields = make(map[string]ast.Expression, len(e.Fields))
		for name, value := range e.Fields {
			rebuilt.Fields[name] = value
		}
		for i, field := range e.FieldOrder {
			field.Value = sequenced[i]
			rebuilt.FieldOrder[i] = field
			rebuilt.Fields[field.Name] = sequenced[i]
		}
		return &rebuilt
	case *ast.VariantExpression:
		if e.Payload == nil {
			return e
		}
		payload := cg.sequence(e.Payload, tc)
		if payload == e.Payload {
			return e
		}
		rebuilt := *e
		rebuilt.Payload = payload
		return &rebuilt
	case *ast.MatchExpression:
		scrutinee := cg.sequence(e.Scrutinee, tc)
		rebuilt := *e
		rebuilt.Scrutinee = scrutinee
		if !cg.unhoistable(e) {
			for _, arm := range e.Arms {
				if cg.needsSequencing(arm.Body, tc) {
					return cg.hoistStatementForm(&rebuilt, e, tc)
				}
			}
		}
		if scrutinee == e.Scrutinee {
			return e
		}
		return &rebuilt
	}
	return expr
}

// sequenceGroup sequences the members of one unsequenced group: when two
// or more are sensitive, each sensitive member is hoisted in order (its own
// inner groups first, so nested temporaries precede it); otherwise the
// members are sequenced individually and stay in place.
func (cg *CodeGenerator) sequenceGroup(members []ast.Expression, tc *typechecker.TypeChecker) []ast.Expression {
	out := make([]ast.Expression, len(members))
	if !cg.groupNeedsSequencing(members, tc) {
		for i, m := range members {
			out[i] = cg.sequence(m, tc)
		}
		return out
	}
	sensitive, summaries := cg.sensitiveMembers(members, tc)
	for i, m := range members {
		inner := cg.sequence(m, tc)
		if !sensitive[i] || cg.unhoistable(m) {
			out[i] = inner
			continue
		}
		if _, alreadyHoisted := inner.(*ast.Identifier); alreadyHoisted && inner != m {
			// A conditional hoisted in statement form is already a
			// temporary; hoisting it again would only copy it.
			out[i] = inner
			continue
		}
		// What inner sequencing left behind may be pure (its calls are
		// temporaries now): then it stays inline, and only a residual that
		// still has an effect, or still reads what a sibling writes, moves.
		if residual := cg.summarize(inner, tc); !residual.effectful && !cg.conflicts(residual, i, summaries) {
			out[i] = inner
			continue
		}
		out[i] = cg.hoist(inner, m, tc)
	}
	return out
}

// hoist evaluates a member into a fresh temporary at the current statement
// position and returns the temporary's name as the expression to read.
func (cg *CodeGenerator) hoist(value, original ast.Expression, tc *typechecker.TypeChecker) ast.Expression {
	name, cType := cg.sequenceTemporary(value, original, tc)
	cg.write(fmt.Sprintf("  %s %s = ", cType, name))
	cg.emitExpressionFragment(value, tc)
	cg.output.WriteString(";\n")
	return &ast.Identifier{Token: tokenOf(original), Value: name}
}

// hoistStatementForm evaluates a conditional construct whose chosen part
// needs sequencing: the temporary is declared, then assigned inside the
// branch structure, so hoisted operands run only when their arm does.
func (cg *CodeGenerator) hoistStatementForm(value, original ast.Expression, tc *typechecker.TypeChecker) ast.Expression {
	name, cType := cg.sequenceTemporary(value, original, tc)
	cg.write(fmt.Sprintf("  %s %s;\n", cType, name))
	cg.assignTo(name, value, tc)
	return &ast.Identifier{Token: tokenOf(original), Value: name}
}

// assignTo emits `name = expr` as statements, descending into conditional
// constructs so that each arm sequences its own operands.
func (cg *CodeGenerator) assignTo(name string, expr ast.Expression, tc *typechecker.TypeChecker) {
	switch e := expr.(type) {
	case *ast.MatchExpression:
		if trueBody, falseBody, isBool := boolMatchBranches(e); isBool {
			condition := cg.sequence(e.Scrutinee, tc)
			cg.write("  if ( ")
			cg.emitCondition(condition, tc)
			cg.output.WriteString(" ) {\n")
			cg.indentLevel++
			cg.assignTo(name, trueBody, tc)
			cg.indentLevel--
			cg.write("  } else {\n")
			cg.indentLevel++
			cg.assignTo(name, falseBody, tc)
			cg.indentLevel--
			cg.write("  }\n")
			return
		}
		if cg.scalarMatch(e) {
			scrutinee := cg.sequence(e.Scrutinee, tc)
			if _, isIdent := scrutinee.(*ast.Identifier); !isIdent {
				// Evaluated once, whatever the arms compare it with.
				scrutinee = cg.hoist(scrutinee, e.Scrutinee, tc)
			}
			for i, arm := range e.Arms {
				last := i == len(e.Arms)-1
				literal, isLiteral := arm.Pattern.(*ast.LiteralPattern)
				if last || !isLiteral {
					if i > 0 {
						cg.write("  else {\n")
					} else {
						cg.write("  {\n")
					}
				} else {
					if i > 0 {
						cg.write("  else if ( ")
					} else {
						cg.write("  if ( ")
					}
					cg.emitExpressionFragment(scrutinee, tc)
					cg.output.WriteString(" == ")
					cg.emitExpressionFragment(literal.Value, tc)
					cg.output.WriteString(" ) {\n")
				}
				cg.indentLevel++
				cg.assignTo(name, arm.Body, tc)
				cg.indentLevel--
				cg.write("  }\n")
				if last || !isLiteral {
					break
				}
			}
			return
		}
	case *ast.InfixExpression:
		if e.Operator == "&&" || e.Operator == "||" {
			left := cg.sequence(e.Left, tc)
			cg.write(fmt.Sprintf("  %s = ", name))
			cg.emitExpressionFragment(left, tc)
			cg.output.WriteString(";\n")
			if e.Operator == "&&" {
				cg.write(fmt.Sprintf("  if ( %s ) {\n", name))
			} else {
				cg.write(fmt.Sprintf("  if ( !%s ) {\n", name))
			}
			cg.indentLevel++
			cg.assignTo(name, e.Right, tc)
			cg.indentLevel--
			cg.write("  }\n")
			return
		}
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			outer := cg.localTypes
			cg.localTypes = make(map[string]localContainer, len(outer))
			for n, info := range outer {
				cg.localTypes[n] = info
			}
			defer func() { cg.localTypes = outer }()
			statements := e.Block.Statements
			for _, stmt := range statements[:len(statements)-1] {
				cg.emitStatement(stmt, tc, false)
			}
			if last, isExpr := statements[len(statements)-1].(*ast.ExpressionStatement); isExpr && !last.Discard {
				cg.assignTo(name, last.Expression, tc)
				return
			}
			cg.emitStatement(statements[len(statements)-1], tc, false)
			return
		}
	}
	value := cg.sequence(expr, tc)
	cg.write(fmt.Sprintf("  %s = ", name))
	cg.emitExpressionFragment(value, tc)
	cg.output.WriteString(";\n")
}

// scalarMatch reports a match whose arms are literal or wildcard patterns —
// the shape the inline ternary chain lowers.
func (cg *CodeGenerator) scalarMatch(match *ast.MatchExpression) bool {
	for _, arm := range match.Arms {
		switch arm.Pattern.(type) {
		case *ast.LiteralPattern, *ast.WildcardPattern:
		default:
			return false
		}
	}
	return len(match.Arms) > 0
}

// sequenceTemporary names a fresh temporary for a member and spells its C
// type from the checker's recorded type, falling back to __typeof__ of the
// member when the type has no C spelling.
func (cg *CodeGenerator) sequenceTemporary(value, original ast.Expression, tc *typechecker.TypeChecker) (name, cType string) {
	name = fmt.Sprintf("oak__seq_%d", cg.seqCounter)
	cg.seqCounter++
	if cg.localTypes == nil {
		cg.localTypes = map[string]localContainer{}
	}
	var checked typechecker.Type
	if tc != nil {
		if tok, positioned := ast.ExpressionToken(original); positioned {
			checked, _ = tc.ExpressionTypeAt(tok)
		}
		if checked == nil && tc.Env() != nil {
			checked = tc.Env().CheckedExpressionType(original)
		}
	}
	if typeExpr, ok := checkedTypeExpression(checked); ok {
		cg.localTypes[name] = cg.classifyContainer(typeExpr)
		return name, cg.parseTypeExpression(typeExpr)
	}
	cg.seqTypeofFallbacks++
	cg.localTypes[name] = localContainer{kind: containerUnknown}
	return name, fmt.Sprintf("__typeof__( %s )", cg.fragmentText(value, tc))
}

// checkedTypeExpression spells a checked type as the type AST the C type
// mapping reads: names for scalars, strings, records and sum types; the
// parser's index forms for arrays, views and spans.
func checkedTypeExpression(typ typechecker.Type) (ast.Expression, bool) {
	switch t := typ.(type) {
	case *typechecker.PrimitiveType:
		return &ast.Identifier{Value: t.Name}, true
	case *typechecker.BoolType:
		return &ast.Identifier{Value: "Bool"}, true
	case *typechecker.StringType:
		return &ast.Identifier{Value: "string"}, true
	case *typechecker.ADTType:
		if t.Name != "" && !strings.ContainsAny(t.Name, "[] ,") {
			return &ast.Identifier{Value: t.Name}, true
		}
	case *typechecker.RecordType:
		if t.Name != "" && !strings.ContainsAny(t.Name, "[] ,") {
			return &ast.Identifier{Value: t.Name}, true
		}
	case *typechecker.ArrayType:
		element, ok := checkedTypeExpression(t.ElementType)
		if !ok {
			return nil, false
		}
		switch {
		case t.IsSpan:
			return &ast.IndexExpression{Left: element, Index: &ast.Identifier{Value: "*"}}, true
		case t.IsSlice:
			return &ast.IndexExpression{Left: element, Index: &ast.Identifier{Value: ""}}, true
		case t.Length >= 0:
			return &ast.IndexExpression{Left: element, Index: &ast.IntegerLiteral{Value: t.Length}}, true
		}
	}
	return nil, false
}

// fragmentText renders an expression fragment to a string without
// disturbing the output.
func (cg *CodeGenerator) fragmentText(expr ast.Expression, tc *typechecker.TypeChecker) string {
	start := cg.output.Len()
	cg.emitExpressionFragment(expr, tc)
	whole := cg.output.String()
	cg.output.Reset()
	cg.output.WriteString(whole[:start])
	return whole[start:]
}

// tokenOf is the position a rewritten node keeps, so position-keyed
// recordings still resolve.
func tokenOf(expr ast.Expression) token.Token {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e.Token
	case *ast.InvocationExpression:
		return e.Token
	case *ast.InfixExpression:
		return e.Token
	case *ast.PrefixExpression:
		return e.Token
	case *ast.IndexExpression:
		return e.Token
	case *ast.SliceExpression:
		return e.Token
	case *ast.MatchExpression:
		return e.Token
	case *ast.RecordLiteral:
		return e.Token
	case *ast.ArrayLiteral:
		return e.Token
	case *ast.VariantExpression:
		return e.Token
	case *ast.BlockExpression:
		return e.Token
	}
	return token.Token{}
}
