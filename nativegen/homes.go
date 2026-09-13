package nativegen

// Liveness for the caller-saved homes (docs/spec/94-assembler.md §9,
// twenty-third increment; the last-use release in liveness.go is its complement within a statement list). A pre-pass over the function body numbers its
// statements and calls in source order — the order the lowering emits — and
// records, per variable name, the position of its declaration and the
// position of the end of the last statement that reads it; per while loop,
// the positions its body spans. From those two facts the call sequence
// decides whether a home must be saved around a call, and a declaration
// whether its variable crosses a call at all.
//
// A read counts at its own position — a call's argument is copied into a
// scratch register before the call — except an operand the lowering reads
// in place: a variable named directly under a binary operation, a
// comparison, or an element index is read by the instruction that runs
// after the whole operation's other operands, calls included, so it counts
// at that expression's end. A call counts after its arguments. A variable
// declared outside a loop and read anywhere inside it is live across every
// call in the loop, since the next iteration reads it after this one's
// calls. Names declared more than once (sibling scopes) merge
// conservatively: the earliest declaration, the latest read.

import "github.com/SCKelemen/oak/ast"

type callLiveness struct {
	decl    map[string]int
	lastUse map[string]int
	calls   map[*ast.InvocationExpression]int
	loops   [][2]int
	pos     int
}

// analyzeLiveness numbers fn's body. Parameters are declared at position 0.
func analyzeLiveness(fn *ast.FunctionStatement) *callLiveness {
	lv := &callLiveness{decl: map[string]int{}, lastUse: map[string]int{}, calls: map[*ast.InvocationExpression]int{}}
	for _, p := range fn.Parameters {
		if p != nil && p.Name != nil {
			lv.decl[p.Name.Value] = 0
		}
	}
	lv.pos = 1
	if fn.Body != nil {
		lv.statement(fn.Body)
	}
	return lv
}

func (lv *callLiveness) next() int {
	lv.pos++
	return lv.pos
}

// declare records a declaration at the current position (the earliest wins).
func (lv *callLiveness) declare(name string) {
	if at, seen := lv.decl[name]; !seen || lv.pos < at {
		lv.decl[name] = lv.pos
	}
}

// use records a read of name at a fresh position: a read after a call in
// the same expression must number past it.
func (lv *callLiveness) use(name string) { lv.noteUse(name, lv.next()) }

func (lv *callLiveness) noteUse(name string, at int) {
	if lv.lastUse[name] < at {
		lv.lastUse[name] = at
	}
}

// statement visits one statement (or the body expression standing as one).
func (lv *callLiveness) statement(node ast.Node) {
	lv.next()
	lv.inner(node)
	lv.next()
}

// operand visits an operand read in place: an identifier's read is
// deferred to the enclosing operation's end (returned to the caller to
// note), anything else is visited now.
func (lv *callLiveness) operand(expr ast.Expression, deferred *[]string) {
	if ident, isIdent := expr.(*ast.Identifier); isIdent {
		*deferred = append(*deferred, ident.Value)
		return
	}
	lv.inner(expr)
}

// inner visits a node's children: nested statements get frames of their
// own, expressions record their identifiers and calls.
func (lv *callLiveness) inner(node ast.Node) {
	switch e := node.(type) {
	case nil:
		return
	case *ast.BlockStatement:
		for _, s := range e.Statements {
			lv.statement(s)
		}
	case *ast.BlockExpression:
		if e.Block != nil {
			lv.inner(e.Block)
		}
	case *ast.ExpressionStatement:
		lv.inner(e.Expression)
	case *ast.VariableDeclaration:
		if e.Value != nil {
			lv.inner(e.Value)
		}
		if e.Name != nil {
			lv.declare(e.Name.Value)
		}
	case *ast.AssignmentStatement:
		lv.inner(e.Value)
		if e.Name != nil {
			lv.use(e.Name.Value) // conservatively a read: the home must hold
		}
	case *ast.IndexAssignmentStatement:
		// The lowering evaluates the value first, then the target's index
		// (elementStore); the numbering follows the lowering.
		lv.inner(e.Value)
		lv.inner(e.Target)
	case *ast.WhileStatement:
		start := lv.pos
		lv.inner(e.Condition)
		if e.Body != nil {
			lv.inner(e.Body)
		}
		lv.loops = append(lv.loops, [2]int{start, lv.next()})
	case *ast.IfStatement:
		lv.inner(e.Condition)
		if e.Consequence != nil {
			lv.inner(e.Consequence)
		}
		if e.Alternative != nil {
			lv.inner(e.Alternative)
		}
	case *ast.BreakStatement:
	case *ast.Identifier:
		lv.use(e.Value)
	case *ast.InfixExpression:
		var deferred []string
		lv.operand(e.Left, &deferred)
		lv.operand(e.Right, &deferred)
		end := lv.next()
		for _, name := range deferred {
			lv.noteUse(name, end)
		}
	case *ast.PrefixExpression:
		lv.inner(e.Right)
	case *ast.IndexExpression:
		lv.inner(e.Left)
		if !e.Dot {
			var deferred []string
			lv.operand(e.Index, &deferred)
			end := lv.next()
			for _, name := range deferred {
				lv.noteUse(name, end)
			}
		}
	case *ast.InvocationExpression:
		for _, a := range e.Arguments {
			lv.inner(a)
		}
		lv.calls[e] = lv.next() // the call runs after its arguments
	case *ast.ArrayLiteral:
		for _, a := range e.Elements {
			lv.inner(a)
		}
	case *ast.RecordLiteral:
		for _, field := range e.FieldOrder {
			if value, given := e.Fields[field.Name]; given {
				lv.inner(value)
			}
		}
	case *ast.VariantExpression:
		if e.Payload != nil {
			lv.inner(e.Payload)
		}
	case *ast.MatchExpression:
		lv.inner(e.Scrutinee)
		for _, arm := range e.Arms {
			if arm == nil {
				continue
			}
			if block, isBlock := arm.Body.(*ast.BlockExpression); isBlock {
				lv.inner(block)
			} else {
				lv.inner(arm.Body)
			}
		}
	default:
		// A node the lowering does not reach: its identifiers still count
		// as reads of this statement, its calls as calls here.
		walk(node, func(n ast.Node) {
			switch x := n.(type) {
			case *ast.Identifier:
				lv.use(x.Value)
			case *ast.InvocationExpression:
				if _, seen := lv.calls[x]; !seen {
					lv.calls[x] = lv.pos
				}
			case *ast.VariableDeclaration:
				if x.Name != nil {
					lv.declare(x.Name.Value)
				}
			}
		})
	}
}

// liveAfter reports whether name may be read after the call at position at:
// a later statement reads it, or a loop containing the call and entered
// after the declaration reads it anywhere.
func (lv *callLiveness) liveAfter(name string, at int) bool {
	last, read := lv.lastUse[name]
	if !read {
		return false
	}
	if last > at {
		return true
	}
	decl := lv.decl[name]
	for _, loop := range lv.loops {
		if loop[0] <= at && at <= loop[1] && decl < loop[0] && last >= loop[0] {
			return true
		}
	}
	return false
}

// crossing reports whether name is live across some call after its
// declaration: such a variable is best kept in a callee-saved register.
func (lv *callLiveness) crossing(name string) bool {
	decl := lv.decl[name]
	for _, at := range lv.calls {
		if at > decl && lv.liveAfter(name, at) {
			return true
		}
	}
	return false
}
