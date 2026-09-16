package metal

import "github.com/SCKelemen/oak/ast"

// A lane-independent span store is emitted for lane 0. That is sound only
// when every lane reaches it with the same value, or the source already
// restricts it to lane 0. This analysis proves that narrower fact; it does
// not grant permission to write a lane-dependent index. Independence and
// the existing lane-index rule still judge those stores.
type groupUniformity struct {
	em      *emitter
	varying map[string]bool
	locals  map[string]bool
}

type laneControl struct {
	varying bool
	zero    bool // the enclosing conditions imply lane(G) == 0
}

func (em *emitter) groupStoreRestrictions(fn *ast.FunctionStatement) map[*ast.IndexAssignmentStatement]string {
	u := &groupUniformity{em: em, varying: map[string]bool{}, locals: map[string]bool{}}
	walk(fn.Body, func(n ast.Node) {
		if d, ok := n.(*ast.VariableDeclaration); ok && d.Name != nil {
			u.locals[d.Name.Value] = true
		}
	})
	// Monotone, function-wide dependencies include back edges: a condition
	// used before an assignment in a loop can vary on the next iteration.
	for changed := true; changed; {
		changed = false
		u.walk(fn.Body, laneControl{}, func(n ast.Node, control laneControl) {
			var name string
			var value ast.Expression
			switch s := n.(type) {
			case *ast.VariableDeclaration:
				if s.Name == nil {
					return // the subset emitter diagnoses the declaration
				}
				name, value = s.Name.Value, s.Value
			case *ast.AssignmentStatement:
				name, value = s.Name.Value, s.Value
			case *ast.IndexAssignmentStatement:
				// Local aggregates can carry lane-dependent state into a
				// later guard. Parameter spans are handled at their reads.
				base := s.Target.Left
				for {
					field, ok := base.(*ast.IndexExpression)
					if !ok {
						break
					}
					base = field.Left
				}
				if id, ok := base.(*ast.Identifier); ok && u.locals[id.Value] {
					name, value = id.Value, s.Value
					control.varying = control.varying || u.expr(s.Target.Index)
				}
			}
			if name != "" && !u.varying[name] && (control.varying || u.expr(value)) {
				u.varying[name] = true
				changed = true
			}
		})
	}
	bad := map[*ast.IndexAssignmentStatement]string{}
	u.walk(fn.Body, laneControl{}, func(n ast.Node, control laneControl) {
		store, ok := n.(*ast.IndexAssignmentStatement)
		if !ok || control.zero {
			return
		}
		if control.varying {
			bad[store] = "has lane-dependent control flow"
		} else if u.expr(store.Value) {
			bad[store] = "has a value that is not proven uniform across lanes"
		}
	})
	return bad
}

// expr reports possible variation, not a proof that values differ. Helpers
// in the subset are pure and have no lane intrinsic, so uniform arguments
// give a uniform result. Reads of mutable storage are not such arguments:
// lanes can see different states even when they use the same address.
func (u *groupUniformity) expr(e ast.Expression) bool {
	switch v := e.(type) {
	case nil, *ast.IntegerLiteral, *ast.FloatLiteral, *ast.Boolean:
		return false
	case *ast.Identifier:
		return u.varying[v.Value]
	case *ast.PrefixExpression:
		return u.expr(v.Right)
	case *ast.InfixExpression:
		return u.expr(v.Left) || u.expr(v.Right)
	case *ast.IndexExpression:
		if v.Dot {
			return u.expr(v.Left)
		}
		// Only a read-only view can establish uniformity of an element
		// read. A local array may be private or shared threadgroup memory.
		t, known := u.em.checkedTypeOf(v.Left)
		if !known {
			_, t, known = u.em.bufferRef(v.Left)
		}
		return !known || t.kind != "view" || u.expr(v.Left) || u.expr(v.Index)
	case *ast.InvocationExpression:
		id, named := v.Function.(*ast.Identifier)
		if !named || id.Value == "lane" {
			return true
		}
		if id.Value == "len" && len(v.Arguments) == 1 {
			// Array lengths do not depend on their mutable contents.
			if t, ok := u.em.checkedTypeOf(v.Arguments[0]); ok && t.kind == "array" {
				return false
			}
		}
		for _, a := range v.Arguments {
			if u.expr(a) {
				return true
			}
		}
		return false
	case *ast.MatchExpression:
		if u.expr(v.Scrutinee) {
			return true
		}
		for _, arm := range v.Arms {
			if u.expr(arm.Body) {
				return true
			}
		}
		return false
	case *ast.RecordLiteral:
		for _, f := range v.FieldOrder {
			if u.expr(f.Value) {
				return true
			}
		}
		return false
	case *ast.BlockExpression:
		if v.Block != nil && len(v.Block.Statements) == 1 {
			if result, ok := v.Block.Statements[0].(*ast.ExpressionStatement); ok {
				return u.expr(result.Expression)
			}
		}
	}
	return true // no uniformity rule for an unrecognized expression
}

// walk carries control dependencies to every assignment, including the
// implicit loop guard created by a lane-dependent break. It is separate
// from emission so facts cannot depend on which arm is emitted first.
func (u *groupUniformity) walk(n ast.Node, control laneControl, visit func(ast.Node, laneControl)) {
	if n == nil {
		return
	}
	visit(n, control)
	switch v := n.(type) {
	case *ast.BlockStatement:
		for _, s := range v.Statements {
			u.walk(s, control, visit)
		}
	case *ast.BlockExpression:
		if v.Block != nil {
			u.walk(v.Block, control, visit)
		}
	case *ast.ExpressionStatement:
		u.walk(v.Expression, control, visit)
	case *ast.VariableDeclaration:
		u.walk(v.Value, control, visit)
	case *ast.AssignmentStatement:
		u.walk(v.Value, control, visit)
	case *ast.IndexAssignmentStatement:
		u.walk(v.Value, control, visit)
	case *ast.WhileStatement:
		control.varying = control.varying || u.expr(v.Condition) || u.divergentBreak(v.Body)
		control.zero = control.zero || selectsLaneZero(v.Condition, true)
		if v.Body != nil {
			u.walk(v.Body, control, visit)
		}
	case *ast.MatchExpression:
		control.varying = control.varying || u.expr(v.Scrutinee)
		trueBody, falseBody, ok := boolArms(v)
		if !ok {
			// The emitter rejects non-Bool matches in this subset.
			control.varying = true
			for _, arm := range v.Arms {
				u.walk(arm.Body, control, visit)
			}
			return
		}
		for _, arm := range []struct {
			body  ast.Expression
			truth bool
		}{{trueBody, true}, {falseBody, false}} {
			inner := control
			inner.zero = inner.zero || selectsLaneZero(v.Scrutinee, arm.truth)
			u.walk(arm.body, inner, visit)
		}
	}
}

func (u *groupUniformity) divergentBreak(body *ast.BlockStatement) bool {
	if body == nil {
		return false
	}
	var scan func(ast.Node, bool) bool
	scan = func(n ast.Node, varying bool) bool {
		switch v := n.(type) {
		case *ast.BreakStatement:
			return varying
		case *ast.BlockStatement:
			for _, s := range v.Statements {
				if scan(s, varying) {
					return true
				}
			}
		case *ast.BlockExpression:
			if v.Block != nil {
				return scan(v.Block, varying)
			}
		case *ast.ExpressionStatement:
			return scan(v.Expression, varying)
		case *ast.MatchExpression:
			varying = varying || u.expr(v.Scrutinee)
			for _, arm := range v.Arms {
				if scan(arm.Body, varying) {
					return true
				}
			}
			// A nested loop's breaks leave that loop, not this one.
		}
		return false
	}
	return scan(body, false)
}

// selectsLaneZero proves only explicit tests of lane(G), their negations,
// and Boolean combinations. In particular, the false arm of lane == 0 is
// not a lane-0 selection, nor is a disjunction with an unrelated condition.
func selectsLaneZero(e ast.Expression, truth bool) bool {
	if p, ok := e.(*ast.PrefixExpression); ok && p.Operator == "!" {
		return selectsLaneZero(p.Right, !truth)
	}
	v, ok := e.(*ast.InfixExpression)
	if !ok {
		return false
	}
	switch v.Operator {
	case "&&", "||":
		left, right := selectsLaneZero(v.Left, truth), selectsLaneZero(v.Right, truth)
		if (v.Operator == "&&") == truth {
			return left || right
		}
		return left && right
	case "==", "!=":
		if (v.Operator == "==") != truth {
			return false
		}
		for _, pair := range [][2]ast.Expression{{v.Left, v.Right}, {v.Right, v.Left}} {
			call, ok := pair[0].(*ast.InvocationExpression)
			zero, literal := pair[1].(*ast.IntegerLiteral)
			if !ok || !literal || zero.Value != 0 {
				continue
			}
			if id, ok := call.Function.(*ast.Identifier); ok && id.Value == "lane" && len(call.Arguments) == 1 {
				return true
			}
		}
	}
	return false
}
