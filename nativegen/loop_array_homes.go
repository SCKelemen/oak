package nativegen

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
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

// LoopArrayHomes counts the element homes introduced by the candidate.
func LoopArrayHomes(fn *asm.Function) int { return loopArrayHomesOf[fn] }

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

func (g *generator) beginLoopArrayHomes(loop *ast.WhileStatement) func() {
	if !g.loopArrayHomesEnabled || g.rvLane || len(g.loops) != 0 || g.activeArrayHomes != nil {
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
	for name, arr := range g.arrays {
		if arr == nil || arr.inReg || arr.paramRef || arr.readOnly || arr.elemLayout != nil || (arr.elem != scalars["u32"] && arr.elem != scalars["u64"]) {
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
		g.emit(loadOf(c.arr.elem), reg(r, c.arr.elem), g.slotMem(c.arr.offset+c.index*int64(c.arr.elem.bits/8)))
		set := g.activeArrayHomes[c.name]
		if set == nil {
			set = &loopArrayHomeSet{array: c.arr, homes: map[int64]loopArrayHome{}}
			g.activeArrayHomes[c.name] = set
		}
		set.homes[c.index] = loopArrayHome{hidden: hidden, written: c.written}
		selected = append(selected, c)
		g.arrayHomesCount++
	}
	return func() {
		for _, c := range selected {
			home := g.activeArrayHomes[c.name].homes[c.index]
			if home.written {
				g.emit(storeOf(c.arr.elem), reg(g.regs[home.hidden], c.arr.elem), g.slotMem(c.arr.offset+c.index*int64(c.arr.elem.bits/8)))
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
