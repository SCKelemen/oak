package nativegen

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Constant-trip unrolling (docs/spec/94-assembler.md §9 "Constant-trip
// loops"; spec/lean/Oak/ConstantUnroll.lean loop_eq_unrolled). A loop
// whose trip count is a literal,
//
//	round: u32 = 0
//	while round < u32(7) { …; round = round + u32(1) }
//
// is rewritten, before lowering, into its trips: seven copies of the body,
// flat in the enclosing scope, the kth with `round` replaced by `u32(k)`
// and its locals renamed for the trip (`g0` to `g0_t3`), and `round =
// u32(7)` after them for whatever reads the index later.
// The loop disappears and with it every data-dependent index it carried:
// an array the body indexes by the loop's variable is indexed by
// constants afterward, so the lowering keeps its elements as scalars and
// the frame-slot promotion (machine/slots.go) can move what is left into
// registers — the state words of a hash compression, which its final
// `while i < 8 { v[i] = v[i] ^ v[i + 8] … }` otherwise pins to the frame.
// A conditional on the index (`round < u32(6) ? { … }`) becomes a
// conditional on a literal, which the lowering folds.
//
// Recognized: the declaration `i: u32 = 0` immediately before the loop,
// the condition `i < N` with N a literal (or `u32(N)`) from 1 to 16 — the
// bound on the code the rewrite may spell — the body's last statement
// `i = i + u32(1)`, and no other write of the index, no declaration
// shadowing it, and no `break` in the body. The body runs the trips in
// order from any state, so nothing is assumed of it (loop_eq_unrolled).

// maxConstantTrips bounds the copies one loop may become.
const maxConstantTrips = 16

// constantLoop is one recognized loop: its index variable, trip count,
// and the locals its body declares, which each trip's copy renames.
type constantLoop struct {
	loop     *ast.WhileStatement
	idx      string
	trips    int64
	declared []string
}

// tripName is a body local's name in one trip's copy.
func tripName(name string, k int64) string { return name + "_t" + itoa(int(k)) }

// unrollConstantLoops returns the body with its constant-trip loops
// unrolled, and whether any was.
func unrollConstantLoops(fn *ast.FunctionStatement, body ast.Expression) (ast.Expression, bool) {
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil {
		return body, false
	}
	changed := false
	expansions := 0
	generated := map[string]bool{}
	var rewrite func(stmts []ast.Statement) []ast.Statement
	rewrite = func(stmts []ast.Statement) []ast.Statement {
		var out []ast.Statement
		var prev ast.Statement
		for _, stmt := range stmts {
			switch s := stmt.(type) {
			case *ast.WhileStatement:
				if c, ok := recognizeConstantLoop(s, prev, body); ok {
					// Inner expansion creates locals absent from c.declared.
					// Keep the outer loop in that case rather than copying
					// generated names the outer match cannot freshen.
					beforeInner := expansions
					s.Body.Statements = rewrite(s.Body.Statements)
					// Original-body freshness alone cannot see names made
					// by an earlier, separately scoped loop in this rewrite.
					fresh := true
					names := map[string]bool{}
					for _, name := range c.declared {
						for k := int64(0); k < c.trips; k++ {
							trip := tripName(name, k)
							if generated[trip] || names[trip] {
								fresh = false
							}
							names[trip] = true
						}
					}
					if fresh && expansions == beforeInner {
						expansions++
						for name := range names {
							generated[name] = true
						}
						out = append(out, unrolledConstantLoop(c)...)
						changed = true
					} else {
						out = append(out, stmt)
					}
					prev = stmt
					continue
				}
				if s.Body != nil {
					s.Body.Statements = rewrite(s.Body.Statements)
				}
			case *ast.ExpressionStatement:
				if inner, isBlock := s.Expression.(*ast.BlockExpression); isBlock && inner.Block != nil {
					inner.Block.Statements = rewrite(inner.Block.Statements)
				}
				if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
					for _, arm := range match.Arms {
						if armBlock, isBlock := arm.Body.(*ast.BlockExpression); isBlock && armBlock.Block != nil {
							armBlock.Block.Statements = rewrite(armBlock.Block.Statements)
						}
					}
				}
			case *ast.BlockStatement:
				s.Statements = rewrite(s.Statements)
			}
			out = append(out, stmt)
			prev = stmt
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

// recognizeConstantLoop reads a while statement, with the statement before
// it, as a constant-trip loop; body is the function body, for the
// freshness of the names the copies take.
func recognizeConstantLoop(loop *ast.WhileStatement, prev ast.Statement, body ast.Expression) (constantLoop, bool) {
	cond, isInfix := loop.Condition.(*ast.InfixExpression)
	if !isInfix || cond.Operator != "<" || loop.Body == nil || len(loop.Body.Statements) == 0 {
		return constantLoop{}, false
	}
	idx, isIdent := cond.Left.(*ast.Identifier)
	if !isIdent {
		return constantLoop{}, false
	}
	trips, isConst := constantValue(cond.Right)
	if !isConst || trips < 1 || trips > maxConstantTrips {
		return constantLoop{}, false
	}
	// `i: u32 = 0` right before the loop.
	decl, isDecl := prev.(*ast.VariableDeclaration)
	if !isDecl || decl.Name == nil || decl.Name.Value != idx.Value || decl.Type == nil || decl.Type.String() != "u32" {
		return constantLoop{}, false
	}
	if zero, isConst := constantValue(decl.Value); !isConst || zero != 0 {
		return constantLoop{}, false
	}
	// The last statement `i = i + 1`, and no other write of the index.
	last := loop.Body.Statements[len(loop.Body.Statements)-1]
	step, isStep := last.(*ast.AssignmentStatement)
	if !isStep || step.Name == nil || step.Name.Value != idx.Value {
		return constantLoop{}, false
	}
	inc, isInc := step.Value.(*ast.InfixExpression)
	if !isInc || inc.Operator != "+" || !isName(inc.Left, idx.Value) {
		return constantLoop{}, false
	}
	if one, isConst := constantValue(inc.Right); !isConst || one != 1 {
		return constantLoop{}, false
	}
	clean := true
	var declared []string
	for _, stmt := range loop.Body.Statements[:len(loop.Body.Statements)-1] {
		walk(stmt, func(n ast.Node) {
			switch x := n.(type) {
			case *ast.AssignmentStatement:
				if x.Name != nil && x.Name.Value == idx.Value {
					clean = false
				}
			case *ast.VariableDeclaration:
				if x.Name != nil {
					if x.Name.Value == idx.Value {
						clean = false
					}
					declared = append(declared, x.Name.Value)
				}
			case *ast.BreakStatement:
				clean = false
			}
		})
	}
	if !clean {
		return constantLoop{}, false
	}
	// The copies' locals take fresh names: the body declares them once
	// each, in one scope, as the verifier reads a body.
	for _, name := range declared {
		for k := int64(0); k < trips; k++ {
			if mentionsName(body, tripName(name, k)) {
				return constantLoop{}, false
			}
		}
	}
	return constantLoop{loop: loop, idx: idx.Value, trips: trips, declared: declared}, true
}

// unrolledConstantLoop spells the trips: each body copy flat in the
// enclosing scope with the index a literal and its locals renamed for
// the trip, then the index at its final value.
func unrolledConstantLoop(c constantLoop) []ast.Statement {
	tok := c.loop.Token
	ident := func(name string) *ast.Identifier { return &ast.Identifier{Token: tok, Value: name} }
	u32 := func(v int64) ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("u32"), Arguments: []ast.Expression{&ast.IntegerLiteral{Token: token.Token{Line: tok.Line, Literal: itoa(int(v))}, Value: v}}}
	}
	body := c.loop.Body.Statements[:len(c.loop.Body.Statements)-1]
	var out []ast.Statement
	for k := int64(0); k < c.trips; k++ {
		copied := cloneNode(&ast.BlockStatement{Token: tok, Statements: body}).(*ast.BlockStatement)
		substituteBound(copied, map[string]ast.Expression{c.idx: u32(k)})
		if len(c.declared) > 0 {
			rename := map[string]string{}
			for _, name := range c.declared {
				rename[name] = tripName(name, k)
			}
			renameBound(copied, rename)
		}
		foldConstantTests(copied)
		out = append(out, copied.Statements...)
	}
	out = append(out, &ast.AssignmentStatement{Token: tok, Name: ident(c.idx), Value: u32(c.trips)})
	return out
}

// foldConstantTests replaces a conditional's test that compares two
// constants — `u32(3) < u32(6)` once the index is a literal — with the
// Boolean it evaluates to, so the lowering takes the arm it names
// (constantArm) instead of testing at run time.
func foldConstantTests(node ast.Node) {
	walk(node, func(n ast.Node) {
		match, isMatch := n.(*ast.MatchExpression)
		if !isMatch {
			return
		}
		cond, isInfix := match.Scrutinee.(*ast.InfixExpression)
		if !isInfix {
			return
		}
		left, okL := constantValue(cond.Left)
		right, okR := constantValue(cond.Right)
		if !okL || !okR {
			return
		}
		var value bool
		switch cond.Operator {
		case "<":
			value = left < right
		case "<=":
			value = left <= right
		case ">":
			value = left > right
		case ">=":
			value = left >= right
		case "==":
			value = left == right
		case "!=":
			value = left != right
		default:
			return
		}
		match.Scrutinee = &ast.Boolean{Token: token.Token{Line: cond.Token.Line, Literal: map[bool]string{true: "true", false: "false"}[value]}, Value: value}
	})
}
