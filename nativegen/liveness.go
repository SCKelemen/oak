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

// releaseDead returns the registers and slots of the variables whose last
// mention was statement i to the pools.
func (g *generator) releaseDead(last map[string]int, i int) {
	if len(last) == 0 {
		return
	}
	top := g.scopes[len(g.scopes)-1]
	// In name order, so the pools' order — and the registers later
	// declarations take — is the same in every build of one source.
	names := make([]string, 0, len(last))
	for name := range last {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		if last[name] != i {
			continue
		}
		b, ok := top[name]
		if !ok || b.arr != nil || b.rec != nil || b.sp != nil || b.freed {
			continue
		}
		switch {
		case b.reg >= vecBase:
			g.freeCalleeV = append(g.freeCalleeV, b.reg)
		case b.reg >= 0:
			g.freeCallee = append(g.freeCallee, b.reg)
		case b.offset >= 0 && b.typ.isVec:
			g.freeSlots16 = append(g.freeSlots16, b.offset)
		case b.offset >= 0:
			g.freeSlots8 = append(g.freeSlots8, b.offset)
		}
		b.freed = true
		top[name] = b
	}
}
