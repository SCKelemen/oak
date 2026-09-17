package nativegen

import (
	"reflect"
	"sort"

	"github.com/SCKelemen/oak/ast"
)

// Last-use release: a variable declared in a statement list is dead after
// the statement of that list that mentions it last (a mention inside a
// nested loop or arm belongs to the enclosing statement, so a variable
// used in a loop lives until the loop ends), and its register or slot goes
// back to the pools for the declarations that follow. Textual order is
// execution order within one list, and the lowering assigns registers
// once, so the release is exact for straight-line code and safe around
// loops. This is what lets an inlined vector kernel keep its temporaries
// in registers: most vector locals are used once, right after they are
// declared.

// lastUses maps each name declared in the list to the index of the last
// statement mentioning it (nil when the list declares nothing); a name the
// trailing node mentions gets an index past the list.
func lastUses(stmts []ast.Statement, trailing ast.Node) map[string]int {
	declared := map[string]bool{}
	for _, stmt := range stmts {
		if d, ok := stmt.(*ast.VariableDeclaration); ok && d.Name != nil {
			declared[d.Name.Value] = true
		}
	}
	if len(declared) == 0 {
		return nil
	}
	last := map[string]int{}
	for i, stmt := range stmts {
		mentionIdents(stmt, func(name string) {
			if declared[name] {
				last[name] = i
			}
		})
	}
	if trailing != nil {
		// Mentioned past the list: never released within it.
		mentionIdents(trailing, func(name string) {
			if declared[name] {
				last[name] = len(stmts)
			}
		})
	}
	return last
}

// mentionIdents visits every identifier under a node — an over-approximation
// of the names used, which is the safe direction for liveness.
func mentionIdents(node ast.Node, visit func(string)) {
	var walkValue func(v reflect.Value)
	walkValue = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			if id, ok := v.Interface().(*ast.Identifier); ok {
				visit(id.Value)
				return
			}
			walkValue(v.Elem())
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walkValue(v.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				walkValue(v.Index(i))
			}
		case reflect.Map:
			iter := v.MapRange()
			for iter.Next() {
				walkValue(iter.Value())
			}
		}
	}
	walkValue(reflect.ValueOf(node))
}

// lastUseOrder groups the names of a last-use map by the statement of
// their last mention, each group in name order — the pools' order, and so
// the registers later declarations take, the same in every build of one
// source. The names are sorted once for the statement list: sorted at
// every statement they were a twenty-fifth of a native build.
func lastUseOrder(last map[string]int, statements int) [][]string {
	names := make([]string, 0, len(last))
	for name := range last {
		names = append(names, name)
	}
	sort.Strings(names)
	order := make([][]string, statements)
	for _, name := range names {
		if i := last[name]; i >= 0 && i < statements {
			order[i] = append(order[i], name)
		}
	}
	return order
}

// releaseDead returns the registers and slots of the variables whose last
// mention was statement i to the pools.
func (g *generator) releaseDead(last map[string]int, i int) {
	if len(last) == 0 {
		return
	}
	var names []string
	for name, at := range last {
		if at == i {
			names = append(names, name)
		}
	}
	sort.Strings(names)
	g.releaseNames(names)
}

// releaseNames returns the named variables' registers and slots to the
// pools, in the order given.
func (g *generator) releaseNames(names []string) {
	if len(names) == 0 {
		return
	}
	top := g.scopes[len(g.scopes)-1]
	for _, name := range names {
		b, ok := top[name]
		if !ok || b.freed {
			continue
		}
		if b.sa != nil {
			// Only the hidden elements own storage. Their names do not
			// occur in the source last-use map, so release their homes at
			// the parent's last mention, in element order. Nested loop or
			// arm uses belong to their enclosing statement, as for scalars.
			// Never recycle the synthetic parent's offset or register.
			for _, hidden := range b.sa.names {
				g.releaseDeadScalar(top, hidden)
			}
			b.freed = true
			top[name] = b
			continue
		}
		g.releaseDeadScalar(top, name)
	}
}

// releaseDeadScalar releases only an actual scalar home in this scope.
// Marking it freed keeps a repeated release or popScope from returning the
// same home twice; an outer binding is never reached through a name here.
func (g *generator) releaseDeadScalar(top map[string]slotBinding, name string) {
	b, ok := top[name]
	if !ok || b.arr != nil || b.rec != nil || b.sp != nil || b.sa != nil || b.freed {
		return
	}
	switch {
	case b.reg >= vecBase:
		g.releaseVectorHome(b.reg)
	case b.reg >= 0:
		g.freeCallee = append(g.freeCallee, b.reg)
	case b.offset >= 0 && b.typ.isVec:
		g.freeSlots16 = append(g.freeSlots16, b.offset)
	case b.offset >= 0:
		g.freeSlots8 = append(g.freeSlots8, b.offset)
		traceSlot("release-dead", name, b.offset, b.reg, g.nslots, len(g.freeSlots8))
	}
	b.freed = true
	top[name] = b
}
