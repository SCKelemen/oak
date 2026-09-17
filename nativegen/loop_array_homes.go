package nativegen

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// Loop-local homes leave an owned array in memory outside one loop. Inside,
// selected literal-index elements live in scalar homes, preloaded before the
// header and flushed after its exit. This is an untrusted machine candidate:
// it does not change the Oak reference the verifier compares against.
type loopArrayHome struct {
	hidden  string
	written bool
}

type loopArrayHomeSet struct {
	array *arrayLocal
	homes map[int64]loopArrayHome
}

var loopArrayHomesOf = map[*asm.Function]int{}
var loopResultHomesOf = map[*asm.Function]int{}

// LoopArrayHomes counts the element homes introduced by the candidate.
func LoopArrayHomes(fn *asm.Function) int { return loopArrayHomesOf[fn] }

// LoopResultHomes counts homes for exact named-local indirect result arrays.
// This is independent of the private-frame candidate and is verifier gated.
func LoopResultHomes(fn *asm.Function) int { return loopResultHomesOf[fn] }

// homeNodes is deliberately closed over ordinary expressions and structured
// control. Unsupported syntax cannot hide an alias or an exit past the flush.
// Declaration names and types are not expression reads; mentionIdents below
// independently counts every identifier, including in unsupported fields.
func homeNodes(n ast.Node, visit func(ast.Node)) bool {
	if n == nil {
		return true
	}
	visit(n)
	walk := func(n ast.Node) bool { return homeNodes(n, visit) }
	switch e := n.(type) {
	case *ast.Identifier, *ast.IntegerLiteral, *ast.FloatLiteral, *ast.Boolean, *ast.StringLiteral:
		return true
	case *ast.BlockStatement:
		if e == nil || e.Order != "" {
			return false
		}
		for _, s := range e.Statements {
			if !walk(s) {
				return false
			}
		}
		return true
	case *ast.BlockExpression:
		return e.Block != nil && walk(e.Block)
	case *ast.ExpressionStatement:
		return walk(e.Expression)
	case *ast.VariableDeclaration:
		return walk(e.Value)
	case *ast.AssignmentStatement:
		return walk(e.Value)
	case *ast.IndexAssignmentStatement:
		return walk(e.Target) && walk(e.Value)
	case *ast.IndexExpression:
		return walk(e.Left) && walk(e.Index)
	case *ast.InfixExpression:
		return walk(e.Left) && walk(e.Right)
	case *ast.PrefixExpression:
		return e.Operator != "&" && walk(e.Right)
	case *ast.InvocationExpression:
		if _, direct := e.Function.(*ast.Identifier); !direct {
			return false
		}
		for _, a := range e.Arguments {
			if !walk(a) {
				return false
			}
		}
		return true
	case *ast.ArrayLiteral:
		for _, a := range e.Elements {
			if !walk(a) {
				return false
			}
		}
		return true
	case *ast.MatchExpression:
		if !walk(e.Scrutinee) {
			return false
		}
		for _, arm := range e.Arms {
			if arm == nil {
				return false
			}
			switch p := arm.Pattern.(type) {
			case *ast.WildcardPattern:
			case *ast.LiteralPattern:
				if _, boolean := p.Value.(*ast.Boolean); !boolean {
					return false
				}
			default:
				return false
			}
			if !walk(arm.Body) {
				return false
			}
		}
		return true
	case *ast.WhileStatement:
		return e.Body != nil && walk(e.Condition) && walk(e.Body)
	case *ast.IfStatement:
		return walk(e.Condition) && e.Consequence != nil && walk(e.Consequence) && (e.Alternative == nil || walk(e.Alternative))
	default:
		return false // breaks, defer, closures, ordered/unknown control
	}
}

func homeMentions(n ast.Node, name string) int {
	count := 0
	mentionIdents(n, func(s string) {
		if s == name {
			count++
		}
	})
	return count
}

// loopHomeUses excludes aliases in the containing function, not just inside
// the loop: a previously formed view could otherwise observe stale memory.
// Computed indices AFTER the loop are allowed, because its exit flushes first.
func loopHomeUses(fn *ast.FunctionStatement, loop *ast.WhileStatement, name string, length int64) (map[int64]int, map[int64]bool) {
	if fn == nil || loop == nil || loop.Body == nil || length <= 0 || length > 64 || homeMentions(loop.Condition, name) != 0 {
		return nil, nil
	}
	block, ok := fn.Body.(*ast.BlockExpression)
	if !ok || block.Block == nil {
		return nil, nil
	}
	allowed, declarations := 0, 0
	valid := true
	if len(block.Block.Statements) > 0 {
		if tail, ok := block.Block.Statements[len(block.Block.Statements)-1].(*ast.ExpressionStatement); ok && !tail.Discard {
			if id, ok := tail.Expression.(*ast.Identifier); ok && id.Value == name {
				allowed++ // the exact function result, after the loop's flush
			}
		}
	}
	lenUse := func(e *ast.InvocationExpression) bool {
		f, ok := e.Function.(*ast.Identifier)
		if !ok || f.Value != "len" || len(e.Arguments) != 1 {
			return false
		}
		arg, ok := e.Arguments[0].(*ast.Identifier)
		return ok && arg.Value == name
	}
	if !homeNodes(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.VariableDeclaration:
			if e.Name != nil && e.Name.Value == name {
				declarations++
				allowed++
			}
		case *ast.AssignmentStatement:
			if e.Name != nil && e.Name.Value == name {
				valid = false
			}
		case *ast.IndexExpression:
			if id, ok := e.Left.(*ast.Identifier); ok && id.Value == name && !e.Dot {
				allowed++
			}
		case *ast.InvocationExpression:
			if lenUse(e) {
				allowed++
			}
		}
	}) || !valid || declarations != 1 || homeMentions(fn.Body, name) != allowed {
		return nil, nil
	}
	counts, writes := map[int64]int{}, map[int64]bool{}
	allowed = 0
	if !homeNodes(loop.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.WhileStatement:
			valid = false
		case *ast.IndexExpression:
			if id, ok := e.Left.(*ast.Identifier); ok && id.Value == name {
				k, constant := constantValue(e.Index)
				if e.Dot || !constant || k < 0 || k >= length {
					valid = false
				} else {
					counts[k]++
					allowed++
				}
			}
		case *ast.IndexAssignmentStatement:
			if e.Target != nil {
				if id, ok := e.Target.Left.(*ast.Identifier); ok && id.Value == name {
					if k, constant := constantValue(e.Target.Index); constant {
						writes[k] = true
					}
				}
			}
		case *ast.InvocationExpression:
			if lenUse(e) {
				allowed++
			}
		}
	}) || !valid || homeMentions(loop.Body, name) != allowed {
		return nil, nil
	}
	return counts, writes
}

// loopHomeStorageEligible distinguishes private frame arrays from exact
// result storage. A matching register number alone is not provenance: array
// fields, globals, parameter references, and views must never acquire homes.
// The result case additionally excludes other observers in the body. It still
// relies on the ordinary result-RAM/input separation contract at the caller;
// neither a tag nor the ABI's register spelling proves general non-aliasing.
func (g *generator) loopHomeStorageEligible(name string, arr *arrayLocal) bool {
	if arr == nil || arr.paramRef || arr.readOnly || arr.elemLayout != nil ||
		(arr.elem != scalars["u32"] && arr.elem != scalars["u64"]) || arr.length <= 0 || arr.length > 64 {
		return false
	}
	if !arr.inReg {
		return g.loopArrayHomesEnabled && !arr.resultStorage
	}
	return g.loopResultHomesEnabled && arr.resultStorage && g.resultIndirect &&
		name != "" && name == g.returnSlot && arr.reg == g.resultAreaReg && arr.offset == 0 &&
		len(arr.temps) == 0 && g.resultRecord != nil &&
		g.resultRecord.size > 16 && g.resultRecord.size%8 == 0 &&
		g.resultRecord == g.arrayLayout(arr.elem, arr.length) && g.resultHomeBodyIsolated()
}

// resultHomeBodyIsolated is deliberately narrower than private-frame homes.
// Mutable globals or a scalar callee could observe a caller-provided result
// pointer without the local's address ever being taken. Do not speculate about
// those aliases: allow only owned/scalar inputs and a call-free body whose
// nonlocal memory is immutable constant data. Full source-body checking also
// covers observations before/after the candidate loop.
func (g *generator) resultHomeBodyIsolated() bool {
	if g.fn == nil || g.fn.Body == nil || g.hasCalls {
		return false
	}
	for _, p := range g.fn.Parameters {
		if p == nil {
			return false
		}
		if _, scalar := scalarOf(p.Type); scalar {
			continue
		}
		elem, record, length, err := g.arrayTypeOf(p.Type)
		if err != nil || record != nil || length <= 0 || length > 64 ||
			(elem != scalars["u32"] && elem != scalars["u64"]) {
			return false
		}
	}
	isolate := true
	mentionIdents(g.fn.Body, func(name string) {
		if _, mutable := g.globals[name]; mutable {
			isolate = false
		}
		if _, aggregate := g.aggregates[name]; aggregate {
			if _, immutable := g.tables[name]; !immutable {
				isolate = false
			}
		}
	})
	if !isolate {
		return false
	}
	if !homeNodes(g.fn.Body, func(n ast.Node) {
		if call, ok := n.(*ast.InvocationExpression); ok {
			f, direct := call.Function.(*ast.Identifier)
			if !direct || (!isConversion(f.Value) && f.Value != "len") {
				isolate = false
			}
		}
	}) {
		return false
	}
	return isolate
}

// No language trap may bypass a result flush. The verifier's guard-holding
// result equivalence alone does not establish that property. Check only the
// active interval: computed accesses after the flush remain ordinary memory
// accesses. This intentionally refuses even some independently provable guards.
func (g *generator) resultHomeLoopTrapFree(loop *ast.WhileStatement) bool {
	if loop == nil || loop.Body == nil {
		return false
	}
	safe := true
	// Helper expansion may declare fixed arrays inside the loop (BLAKE's
	// quarter-round results). They are not bound in g.arrays at loop entry.
	// Record only explicit extents, refusing duplicate/shadowed identities.
	localLengths, declared := map[string]int64{}, map[string]bool{}
	if !homeNodes(loop.Body, func(n ast.Node) {
		if d, ok := n.(*ast.VariableDeclaration); ok {
			if d.Name == nil {
				safe = false
				return
			}
			name := d.Name.Value
			if declared[name] || g.arrays[name] != nil {
				safe = false
			}
			declared[name] = true
			if _, record, length, err := g.arrayTypeOf(d.Type); err == nil && record == nil && length > 0 {
				localLengths[name] = length
			}
		}
	}) {
		return false
	}
	visit := func(n ast.Node) {
		switch e := n.(type) {
		case *ast.InfixExpression:
			switch e.Operator {
			case "/", "%":
				safe = false
			case "<<", ">>":
				// Invalid literal counts refuse in the typed lowering; only
				// nonliteral shifts can emit a runtime bounds trap.
				if k, constant := constantValue(e.Right); !constant || k < 0 {
					safe = false
				}
			}
		case *ast.IndexExpression:
			id, direct := e.Left.(*ast.Identifier)
			_, _, length, known := g.staticArrayOf(e.Left)
			if direct && declared[id.Value] {
				length, known = localLengths[id.Value]
			}
			k, constant := constantValue(e.Index)
			if e.Dot || !direct || !known || !constant || k < 0 || k >= length {
				safe = false
			}
		case *ast.InvocationExpression:
			if f, direct := e.Function.(*ast.Identifier); direct {
				_, op, source, conversion := typechecker.ConversionParts(f.Value)
				if conversion && op == "trunc" && scalars[source].isFloat {
					safe = false
				}
			}
		}
	}
	return homeNodes(loop.Condition, visit) && homeNodes(loop.Body, visit) && safe
}

func (g *generator) beginLoopArrayHomes(loop *ast.WhileStatement) func() {
	if (!g.loopArrayHomesEnabled && !g.loopResultHomesEnabled) || g.rvLane || len(g.loops) != 0 || g.activeArrayHomes != nil {
		return nil
	}
	type choice struct {
		name    string
		arr     *arrayLocal
		index   int64
		count   int
		written bool
	}
	var choices []choice
	resultTrapFree := g.loopResultHomesEnabled && g.resultHomeLoopTrapFree(loop)
	for name, arr := range g.arrays {
		if !g.loopHomeStorageEligible(name, arr) || (arr.resultStorage && !resultTrapFree) {
			continue
		}
		counts, writes := loopHomeUses(g.fn, loop, name, arr.length)
		for k, count := range counts {
			if count >= 2 {
				choices = append(choices, choice{name, arr, k, count, writes[k]})
			}
		}
	}
	sort.Slice(choices, func(i, j int) bool {
		a, b := choices[i], choices[j]
		if a.count != b.count {
			return a.count > b.count
		}
		if a.name != b.name {
			return a.name < b.name
		}
		return a.index < b.index
	})
	if len(choices) == 0 {
		return nil
	}
	g.pushScope()
	g.activeArrayHomes = map[string]*loopArrayHomeSet{}
	var selected []choice
	for _, c := range choices {
		if len(selected) == 8 {
			break
		}
		hidden := fmt.Sprintf("%s#loop-home-%d", c.name, c.index)
		if homeMentions(g.fn.Body, hidden) != 0 {
			continue
		}
		r, free := g.takeCalleeRegister()
		if !free {
			break
		}
		g.declareAt(hidden, c.arr.elem, r)
		g.emit(loadOf(c.arr.elem), reg(r, c.arr.elem), g.memOf(c.arr.loc().plus(c.index*c.arr.elemSize())))
		set := g.activeArrayHomes[c.name]
		if set == nil {
			set = &loopArrayHomeSet{array: c.arr, homes: map[int64]loopArrayHome{}}
			g.activeArrayHomes[c.name] = set
		}
		set.homes[c.index] = loopArrayHome{hidden: hidden, written: c.written}
		selected = append(selected, c)
		if c.arr.resultStorage {
			g.resultHomesCount++
		} else {
			g.arrayHomesCount++
		}
	}
	return func() {
		for _, c := range selected {
			home := g.activeArrayHomes[c.name].homes[c.index]
			if home.written {
				g.emit(storeOf(c.arr.elem), reg(g.regs[home.hidden], c.arr.elem), g.memOf(c.arr.loc().plus(c.index*c.arr.elemSize())))
			}
		}
		g.activeArrayHomes = nil
		g.popScope()
	}
}

func (g *generator) loopArrayElement(e *ast.IndexExpression) (string, scalar, bool) {
	if e == nil || e.Dot {
		return "", scalar{}, false
	}
	id, ok := e.Left.(*ast.Identifier)
	if !ok {
		return "", scalar{}, false
	}
	set := g.activeArrayHomes[id.Value]
	if set == nil || g.arrays[id.Value] != set.array {
		return "", scalar{}, false
	}
	k, constant := constantValue(e.Index)
	if !constant {
		return "", scalar{}, false
	}
	home, found := set.homes[k]
	return home.hidden, set.array.elem, found
}
