package nativegen

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// If-conversion (docs/spec/94-assembler.md §9 "If-conversion"): a
// conditional chain whose every condition compares the same two operands
// and whose every arm only assigns register-homed integer locals from
// expressions that are safe to evaluate on either path lowers as one
// compare and a conditional select per assigned variable — no branch, no
// label, so the body of a loop stays one block for the verifier's loop
// shape and the branch predictor has nothing to learn:
//
//	k == target ? { found = true } | k < target ? { lo = mid + u32(1) } | { hi = mid }
//
//	add w9, w25, #1 ; movz w10, #1
//	cmp x26, x6
//	csel w24, w10, w24, eq      ; found
//	csel w7, w9, w7, lo         ; lo — k < target and not k == target
//	csel w23, w25, w23, hi      ; hi — neither
//
// Each arm's condition is the set of comparison outcomes (below, equal,
// above) its operator accepts, less the outcomes of the arms before it;
// the exclusive sets are disjoint, so the selects commute and the chain
// equals the first matching arm (Oak.Assembler.selectChain_firstArm). The
// arms' right-hand sides are evaluated before the compare — every arm
// speculatively, as the branch-free form must — so they may not read
// memory through a guard, call, or divide: identifiers, literals,
// conversions, and the wrap-free operators only (speculable). Within an
// arm a right-hand side may not read a variable the same arm assigned
// earlier (the temporaries hold the values before the chain).

// Comparison outcomes as a bit set: below, equal, above.
const (
	outcomeBelow uint8 = 1 << iota
	outcomeEqual
	outcomeAbove
	outcomeAll = outcomeBelow | outcomeEqual | outcomeAbove
)

// outcomeMasks maps a comparison operator to the outcomes it accepts.
var outcomeMasks = map[string]uint8{
	"==": outcomeEqual, "!=": outcomeBelow | outcomeAbove,
	"<": outcomeBelow, "<=": outcomeBelow | outcomeEqual,
	">": outcomeAbove, ">=": outcomeEqual | outcomeAbove,
}

// outcomeCodes spells an outcome set as a condition code, unsigned then
// signed; the empty set and the full set have no code (never, always).
var outcomeCodes = map[uint8][2]string{
	outcomeBelow: {"lo", "lt"}, outcomeEqual: {"eq", "eq"}, outcomeAbove: {"hi", "gt"},
	outcomeBelow | outcomeEqual: {"ls", "le"}, outcomeEqual | outcomeAbove: {"hs", "ge"}, outcomeBelow | outcomeAbove: {"ne", "ne"},
}

// selectAssign is one assignment inside an arm.
type selectAssign struct {
	name string
	typ  scalar
	rhs  ast.Expression
}

// selectArm is one arm of the chain: its condition's outcomes and its
// assignments (none for an empty arm).
type selectArm struct {
	mask    uint8
	assigns []selectAssign
}

// selectGroup is a run of consecutive arms whose conditions compare the
// same two operands: one compare serves them, their masks made exclusive
// within the group. The first group's operands may be computed (a guarded
// load in the condition — evaluated on every path, as the source does);
// every later group's condition is evaluated speculatively, so its
// operands are registers and immediates.
type selectGroup struct {
	left, right asm.Operand
	leftExpr    ast.Expression // set when the operand is computed
	rightExpr   ast.Expression
	typ         scalar
	signed      bool
	arms        []selectArm
}

// selectChain is a recognized chain: its compare groups in order, the else
// arm the last arm of the last group with that group's remaining mask.
type selectChain struct {
	groups  []selectGroup
	assigns int
}

// maxSelectArms and maxSelectAssigns bound the chain: every arm's
// right-hand side is live at once in the scratch registers.
const (
	maxSelectArms    = 4
	maxSelectAssigns = 4
)

// chainArm is a conditional's syntax before recognition.
type chainArm struct {
	cond *ast.InfixExpression
	body []ast.Statement
}

// conditionalArms flattens `c1 ? {…} | c2 ? {…} | {…}` in statement
// position into its arms and the else body (nil when there is none).
func conditionalArms(match *ast.MatchExpression) ([]chainArm, []ast.Statement, bool) {
	whenTrue, whenFalse, ok := statementConditional(match)
	if !ok {
		return nil, nil, false
	}
	cond, isInfix := match.Scrutinee.(*ast.InfixExpression)
	if !isInfix {
		return nil, nil, false
	}
	body, isBlock := blockStatements(whenTrue)
	if !isBlock {
		return nil, nil, false
	}
	arms := []chainArm{{cond: cond, body: body}}
	switch alt := whenFalse.(type) {
	case nil:
		return arms, nil, true
	case *ast.MatchExpression:
		rest, final, ok := conditionalArms(alt)
		if !ok {
			return nil, nil, false
		}
		return append(arms, rest...), final, true
	default:
		final, isBlock := blockStatements(whenFalse)
		if !isBlock {
			return nil, nil, false
		}
		return arms, final, true
	}
}

// ifArms flattens `if c1 {…} else if c2 {…} else {…}`.
func ifArms(s *ast.IfStatement) ([]chainArm, []ast.Statement, bool) {
	cond, isInfix := s.Condition.(*ast.InfixExpression)
	if !isInfix || s.Consequence == nil {
		return nil, nil, false
	}
	arms := []chainArm{{cond: cond, body: s.Consequence.Statements}}
	switch alt := s.Alternative.(type) {
	case nil:
		return arms, nil, true
	case *ast.IfStatement:
		rest, final, ok := ifArms(alt)
		if !ok {
			return nil, nil, false
		}
		return append(arms, rest...), final, true
	case *ast.BlockStatement:
		return arms, alt.Statements, true
	}
	return nil, nil, false
}

// blockStatements is the statement list of an arm written as a block.
func blockStatements(arm ast.Expression) ([]ast.Statement, bool) {
	block, isBlock := arm.(*ast.BlockExpression)
	if !isBlock {
		return nil, false
	}
	if block.Block == nil {
		return nil, true
	}
	return block.Block.Statements, true
}

// recognizeSelectChain decides whether the arms lower as selects: every
// condition an integer comparison — its operands registers and immediates
// the compare takes directly, or, for the first arm alone, any integer
// expressions — and every arm a list of speculable assignments to
// register-homed integer locals. Consecutive arms over one comparison
// spelling share a compare.
func (g *generator) recognizeSelectChain(arms []chainArm, final []ast.Statement) (*selectChain, bool) {
	if g.rvLane || len(arms) == 0 || len(arms) > maxSelectArms {
		return nil, false
	}
	chain := &selectChain{}
	spelling := ""
	seen := uint8(0)
	for i, arm := range arms {
		if _, isComparison := conditionCodes[arm.cond.Operator]; !isComparison {
			return nil, false
		}
		operand, err := g.operandType(arm.cond)
		if err != nil || operand.isFloat || operand.isVec {
			return nil, false
		}
		left, leftOK := g.simpleOperand(arm.cond.Left, operand, false)
		right, rightOK := g.simpleOperand(arm.cond.Right, operand, true)
		if leftOK && !rightOK {
			if c, isConst := g.constantOperand(arm.cond.Right, operand); isConst && c < 4096 {
				right, rightOK = imm(int64(c)), true
			}
		}
		spelled := ""
		var leftExpr, rightExpr ast.Expression
		switch {
		case leftOK && rightOK:
			spelled = fmt.Sprintf("%v %v", left, right)
		case i == 0:
			// The first condition is evaluated on every path: computed
			// operands are allowed (a guarded element read, `v[i] <= t`).
			if !leftOK {
				leftExpr = arm.cond.Left
			}
			if !rightOK {
				rightExpr = arm.cond.Right
			}
		default:
			return nil, false
		}
		body, ok := g.selectAssigns(arm.body)
		if !ok {
			return nil, false
		}
		chain.assigns += len(body)
		mask := outcomeMasks[arm.cond.Operator]
		if i > 0 && spelled != "" && spelled == spelling && operand.signed == chain.groups[len(chain.groups)-1].signed {
			group := &chain.groups[len(chain.groups)-1]
			group.arms = append(group.arms, selectArm{mask: mask &^ seen, assigns: body})
			seen |= mask
			continue
		}
		chain.groups = append(chain.groups, selectGroup{left: left, right: right, leftExpr: leftExpr, rightExpr: rightExpr, typ: operand, signed: operand.signed, arms: []selectArm{{mask: mask, assigns: body}}})
		spelling, seen = spelled, mask
	}
	if final != nil {
		body, ok := g.selectAssigns(final)
		if !ok {
			return nil, false
		}
		chain.assigns += len(body)
		group := &chain.groups[len(chain.groups)-1]
		group.arms = append(group.arms, selectArm{mask: outcomeAll &^ seen, assigns: body})
	}
	if chain.assigns == 0 || chain.assigns > maxSelectAssigns {
		return nil, false
	}
	return chain, true
}

// selectAssigns reads an arm's body as assignments to register-homed
// integer locals from speculable right-hand sides, none reading a
// variable the arm assigned before it.
func (g *generator) selectAssigns(body []ast.Statement) ([]selectAssign, bool) {
	var out []selectAssign
	for _, stmt := range body {
		assign, isAssign := stmt.(*ast.AssignmentStatement)
		if !isAssign {
			return nil, false
		}
		name := assign.Name.Value
		typ, isScalar := g.types[name]
		if !isScalar || typ.isFloat || typ.isVec {
			return nil, false
		}
		if _, isRecord := g.records[name]; isRecord {
			return nil, false
		}
		if v, inReg := g.regs[name]; !inReg || v < 0 || v >= vecBase {
			return nil, false
		}
		if !g.speculable(assign.Value) {
			return nil, false
		}
		for _, earlier := range out {
			if earlier.name == name || mentionsName(assign.Value, earlier.name) {
				return nil, false
			}
		}
		out = append(out, selectAssign{name: name, typ: typ, rhs: assign.Value})
	}
	return out, true
}

// speculable reports whether an expression may be evaluated on a path
// that does not take its arm: no memory through a guard, no call, no
// division — locals and parameters, literals, conversions, and the
// wrap-free arithmetic, logic, and shifts over those.
func (g *generator) speculable(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.Identifier:
		if _, isRecord := g.records[e.Value]; isRecord {
			return false
		}
		t, isScalar := g.types[e.Value]
		return isScalar && !t.isFloat && !t.isVec
	case *ast.IntegerLiteral, *ast.Boolean:
		return true
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent || len(e.Arguments) != 1 {
			return false
		}
		if _, isConversion := scalars[ident.Value]; !isConversion {
			return false
		}
		return g.speculable(e.Arguments[0])
	case *ast.InfixExpression:
		switch e.Operator {
		case "+", "-", "*", "&", "|", "^", "<<", ">>":
			return g.speculable(e.Left) && g.speculable(e.Right)
		}
	case *ast.PrefixExpression:
		return (e.Operator == "-" || e.Operator == "!") && g.speculable(e.Right)
	}
	return false
}

// mentionsName reports whether the expression names the identifier.
func mentionsName(expr ast.Expression, name string) bool {
	found := false
	mentionIdents(expr, func(ident string) {
		if ident == name {
			found = true
		}
	})
	return found
}

// lowerSelectChain emits the chain: the first group's computed operands,
// every arm's right-hand sides, then the groups from the last to the
// first — each its compare (or the flags a chain's guard left live, for a
// lone group) and, per variable it assigns, the selects from the group's
// last arm to its first over the value the later groups left; the
// variable's home is the value no arm supplies. The first group outermost
// is the chain's first-match order.
func (g *generator) lowerSelectChain(chain *selectChain) error {
	type temp struct {
		reg   int
		owned bool
	}
	temps := map[*selectAssign]temp{}
	var owned []int
	release := func(r int) {
		g.release(r)
	}
	first := &chain.groups[0]
	if first.leftExpr != nil {
		r, err := g.expr(first.leftExpr, &first.typ)
		if err != nil {
			return err
		}
		first.left = reg(r, first.typ)
		owned = append(owned, r)
	}
	if first.rightExpr != nil {
		r, err := g.expr(first.rightExpr, &first.typ)
		if err != nil {
			return err
		}
		first.right = reg(r, first.typ)
		owned = append(owned, r)
	}
	live, mark := g.liveFlags, len(g.items)
	for gi := range chain.groups {
		for a := range chain.groups[gi].arms {
			arm := &chain.groups[gi].arms[a]
			if arm.mask == 0 {
				continue // never taken: `x != y ? {…} | x < y ? {…}`
			}
			for k := range arm.assigns {
				assign := &arm.assigns[k]
				r, inPlace, err := g.operand(assign.rhs, assign.typ)
				if err != nil {
					return err
				}
				temps[assign] = temp{reg: r, owned: !inPlace}
				if !inPlace {
					owned = append(owned, r)
				}
			}
		}
	}
	// The flags of a chain's guard survive when no evaluation wrote them
	// and the chain's one compare is the guard's.
	if live != "" && g.reuseFlags && len(chain.groups) == 1 {
		clean := true
		for _, item := range g.items[mark:] {
			if ins, isIns := item.(asm.Instruction); isIns && asm.SetsFlags(ins.Mnemonic) {
				clean = false
			}
		}
		if clean {
			g.liveFlags = live
		}
	}
	// The variables, in order of first assignment, each with its current
	// value register: the home until a group's selects replace it.
	type current struct {
		reg   int
		owned bool
	}
	var order []string
	values := map[string]*current{}
	for _, group := range chain.groups {
		for _, arm := range group.arms {
			for _, assign := range arm.assigns {
				if _, known := values[assign.name]; !known {
					order = append(order, assign.name)
					values[assign.name] = &current{reg: g.regs[assign.name]}
				}
			}
		}
	}
	for gi := len(chain.groups) - 1; gi >= 0; gi-- {
		group := &chain.groups[gi]
		compare := fmt.Sprintf("%v %v", group.left, group.right)
		if g.reuseFlags && g.liveFlags != "" && g.liveFlags == compare {
			g.reused++
		} else {
			g.emit("cmp", group.left, group.right)
		}
		for _, name := range order {
			typ := g.types[name]
			cur := values[name]
			for a := len(group.arms) - 1; a >= 0; a-- {
				arm := &group.arms[a]
				if arm.mask == 0 {
					continue
				}
				for k := range arm.assigns {
					assign := &arm.assigns[k]
					if assign.name != name {
						continue
					}
					value := temps[assign]
					if arm.mask == outcomeAll {
						// Taken whenever this group is reached: the value itself.
						if cur.owned {
							release(cur.reg)
						}
						cur.reg, cur.owned = value.reg, false
						continue
					}
					code := outcomeCodes[arm.mask][0]
					if group.signed {
						code = outcomeCodes[arm.mask][1]
					}
					t, err := g.alloc(typ)
					if err != nil {
						return err
					}
					g.emit("csel", reg(t, typ), reg(value.reg, typ), reg(cur.reg, typ), asm.Condition{Code: code})
					if cur.owned {
						release(cur.reg)
					}
					cur.reg, cur.owned = t, true
				}
			}
		}
	}
	for _, name := range order {
		typ := g.types[name]
		cur := values[name]
		home := g.regs[name]
		if cur.reg == home {
			continue
		}
		if cur.owned && g.retargetSelect(cur.reg, home, typ, mark) {
			// The select that produced the value writes the home directly.
			g.release(cur.reg)
			g.killLoopFacts(name)
			continue
		}
		if !cur.owned {
			// A borrowed register (another local's home, a temporary an
			// arm still needs): copy before the assignment releases it.
			t, err := g.alloc(typ)
			if err != nil {
				return err
			}
			g.emit("mov", reg(t, typ), reg(cur.reg, typ))
			cur.reg = t
		}
		g.assignVar(name, cur.reg)
		g.killLoopFacts(name)
	}
	for _, r := range owned {
		release(r)
	}
	g.selected++
	return nil
}

// retargetSelect renames the destination of the select that wrote scratch
// r, emitted since item index from, to the variable's home v — when no
// instruction after it reads r (the value is consumed only by the
// assignment) and none reads or writes the home (another arm's in-place
// operand, another variable's select). The renaming is assignVar's
// retargetLast for a value that is not the last instruction's.
func (g *generator) retargetSelect(r, v int, typ scalar, from int) bool {
	at := -1
	for i := len(g.items) - 1; i >= from; i-- {
		ins, isIns := g.items[i].(asm.Instruction)
		if !isIns || ins.Mnemonic != "csel" || len(ins.Operands) != 4 {
			continue
		}
		if dst, isReg := ins.Operands[0].(asm.Register); isReg && dst.Num == r && dst.Class != asm.ClassV {
			at = i
			break
		}
	}
	if at < 0 {
		return false
	}
	for i := at + 1; i < len(g.items); i++ {
		ins, isIns := g.items[i].(asm.Instruction)
		if !isIns {
			return false
		}
		for _, operand := range ins.Operands {
			if o, isReg := operand.(asm.Register); isReg && o.Class != asm.ClassV && (o.Num == r || o.Num == v) {
				return false
			}
		}
	}
	ins := g.items[at].(asm.Instruction)
	operands := append([]asm.Operand(nil), ins.Operands...)
	operands[0] = reg(v, typ)
	ins.Operands = operands
	g.items[at] = ins
	return true
}
