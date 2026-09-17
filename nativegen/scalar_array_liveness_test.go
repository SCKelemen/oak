package nativegen

import (
	"fmt"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func TestScalarArrayLastUseReleasesElementHomesOnce(t *testing.T) {
	top := map[string]slotBinding{
		// Deliberately leave the synthetic offset/register at zero.
		"a":   {sa: &scalarArray{names: []string{"a#0", "a#1"}}},
		"a#0": {reg: 19, offset: -1, typ: scalars["u32"]},
		"a#1": {reg: -1, offset: 24, typ: scalars["u32"]},
	}
	g := &generator{scopes: []map[string]slotBinding{top}}
	last := map[string]int{"a": 3}
	g.releaseDead(last, 2)
	if len(g.freeCallee) != 0 || len(g.freeSlots8) != 0 {
		t.Fatal("element homes released before the array's last use")
	}
	g.releaseDead(last, 3)
	for _, name := range []string{"a", "a#0", "a#1"} {
		if !top[name].freed {
			t.Errorf("%s was not marked freed", name)
		}
	}
	check := func() {
		t.Helper()
		if !reflect.DeepEqual(g.freeCallee, []int{19}) || !reflect.DeepEqual(g.freeSlots8, []int64{24}) {
			t.Fatalf("released homes = registers %v, slots %v; want [19], [24]", g.freeCallee, g.freeSlots8)
		}
	}
	check()
	g.releaseDead(last, 3)
	check()
	g.popScope()
	check()
}

func TestScalarArrayLastUseBoundsSpilledGroupStorage(t *testing.T) {
	top := map[string]slotBinding{}
	g := &generator{
		scopes:     []map[string]slotBinding{top},
		slots:      map[string]int64{},
		types:      map[string]scalar{},
		regs:       map[string]int{},
		usedCallee: calleeHigh - calleeLow + 1,
		// Two live aggregate slots may not be reused by any group.
		nslots: 2,
	}
	for group := 0; group < 8; group++ {
		name := fmt.Sprintf("g%d", group)
		sa := &scalarArray{elem: scalars["u32"], length: 4}
		for element := int64(0); element < sa.length; element++ {
			hidden := elementName(name, element)
			sa.names = append(sa.names, hidden)
			if offset := g.declare(hidden, sa.elem); offset < 16 {
				t.Fatalf("%s reused live aggregate slot %d", hidden, offset)
			}
		}
		top[name] = slotBinding{sa: sa}
		g.releaseDead(map[string]int{name: group}, group)
		if g.nslots != 6 || len(g.freeSlots8) != 4 {
			t.Fatalf("group %d: %d frame slots, %d free; want 6, 4", group, g.nslots, len(g.freeSlots8))
		}
	}
	g.popScope()
	if len(g.freeSlots8) != 4 {
		t.Fatalf("scope exit duplicated reused group homes: %v", g.freeSlots8)
	}
}

func TestScalarArrayLastUseStaysInDeclaringScope(t *testing.T) {
	outer := map[string]slotBinding{
		"a":   {sa: &scalarArray{names: []string{"a#0"}}},
		"a#0": {reg: 19, offset: -1, typ: scalars["u32"]},
	}
	inner := map[string]slotBinding{
		"a":   {sa: &scalarArray{names: []string{"a#0", "missing"}}},
		"a#0": {reg: 20, offset: -1, typ: scalars["u32"]},
	}
	g := &generator{scopes: []map[string]slotBinding{outer, inner}}
	g.releaseDead(map[string]int{"a": 0}, 0)
	if outer["a"].freed || outer["a#0"].freed || !reflect.DeepEqual(g.freeCallee, []int{20}) {
		t.Fatalf("inner release reached the outer array: %v", g.freeCallee)
	}
	// An inner statement list mentioning only the outer array does not
	// acquire ownership of that array's element homes.
	g.scopes[1] = map[string]slotBinding{}
	g.releaseDead(map[string]int{"a": 0}, 0)
	if outer["a#0"].freed || !reflect.DeepEqual(g.freeCallee, []int{20}) {
		t.Fatal("release searched an outer scope")
	}
}

func TestScalarArrayLastUseRetainsNestedAndTrailingMentions(t *testing.T) {
	ident := func() *ast.Identifier { return &ast.Identifier{Value: "a"} }
	read := func() ast.Statement { return &ast.ExpressionStatement{Expression: ident()} }
	decl := &ast.VariableDeclaration{Name: ident()}
	loop := &ast.WhileStatement{Condition: ident(), Body: &ast.BlockStatement{Statements: []ast.Statement{read()}}}
	branch := &ast.IfStatement{
		Consequence: &ast.BlockStatement{Statements: []ast.Statement{read()}},
		Alternative: &ast.BlockStatement{Statements: []ast.Statement{read()}},
	}
	for _, nested := range []ast.Statement{loop, branch} {
		stmts := []ast.Statement{decl, nested}
		if got := lastUses(stmts, nil)["a"]; got != 1 {
			t.Fatalf("nested mention last use = %d, want enclosing statement 1", got)
		}
		if got := lastUses(stmts, read())["a"]; got != 2 {
			t.Fatalf("trailing mention last use = %d, want past-list 2", got)
		}
	}
	if uses := lastUses(loop.Body.Statements, nil); len(uses) != 0 {
		t.Fatalf("loop body acquired an outer declaration: %v", uses)
	}
}
