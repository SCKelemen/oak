package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

const loopHomesSource = `f: (seed: u32, n: u32): [16]u32 {
  v: [16]u32
  i: u32 = 0
  while i < n {
    v[0] = v[0] + v[1]
    v[1] = v[1] ^ seed
    i = i + u32(1)
  }
  j: u32 = 0
  while j < u32(16) {
    v[j] = v[j] ^ seed
    j = j + u32(1)
  }
  v
}`

func parseLoopHomes(t *testing.T, source string) (*ast.FunctionStatement, *ast.WhileStatement) {
	t.Helper()
	p := parser.New(layout.New(scanner.New(source)))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := program.Statements[0].(*ast.FunctionStatement)
	for _, stmt := range fn.Body.(*ast.BlockExpression).Block.Statements {
		if loop, ok := stmt.(*ast.WhileStatement); ok {
			return fn, loop
		}
	}
	t.Fatal("missing loop")
	return nil, nil
}

func TestLoopArrayHomeUses(t *testing.T) {
	fn, loop := parseLoopHomes(t, loopHomesSource)
	counts, written := loopHomeUses(fn, loop, "v", 16)
	if counts[0] != 2 || counts[1] != 3 || !written[0] || !written[1] || len(counts) != 2 {
		t.Fatalf("literal uses, writes, and computed post-loop uses: %v %v", counts, written)
	}
	// Another array's whole-value assignment must not disqualify v. It is
	// exactly the message permutation alongside BLAKE3's cached state.
	other := strings.Replace(loopHomesSource, "i: u32 = 0", "m: [2]u32\n  i: u32 = 0", 1)
	other = strings.Replace(other, "i = i + u32(1)", "m = [2]u32{m[1], m[0]}\n    i = i + u32(1)", 1)
	fn, loop = parseLoopHomes(t, other)
	if got, _ := loopHomeUses(fn, loop, "v", 16); len(got) != 2 {
		t.Fatalf("another array's permutation disqualified v: %v", got)
	}
	// Scalar-valued calls cannot receive an address to this private array;
	// homes survive their ABI clobbers in callee-saved registers.
	fn, loop = parseLoopHomes(t, strings.Replace(loopHomesSource, "v[0] + v[1]", "mix(v[0], v[1])", 1))
	if got, _ := loopHomeUses(fn, loop, "v", 16); len(got) != 2 {
		t.Fatalf("scalar arguments disqualified v: %v", got)
	}
}

func TestLoopArrayHomeUsesRefuseUnsafeShapes(t *testing.T) {
	for _, tc := range []struct{ name, old, replacement string }{
		{"computed in loop", "v[0] = v[0]", "v[i] = v[0]"},
		{"past extent", "v[0] = v[0]", "v[16] = v[0]"},
		{"condition read", "while i < n", "while v[0] < n"},
		{"whole argument", "v[0] + v[1]", "consume(v)"},
		{"borrow before loop", "i: u32 = 0", "alias: []u32 = view(&v)\n  i: u32 = 0"},
		{"element address", "i: u32 = 0", "alias = &v[0]\n  i: u32 = 0"},
		{"whole copy before loop", "i: u32 = 0", "alias: [16]u32 = v\n  i: u32 = 0"},
		{"whole assignment", "i = i + u32(1)", "v = [16]u32{}\n    i = i + u32(1)"},
		{"shadow in body", "v[0] = v[0]", "v: [16]u32\n    v[0] = v[0]"},
		{"nested loop", "v[0] = v[0]", "while seed == u32(0) { seed = u32(1) }\n    v[0] = v[0]"},
		{"break", "i = i + u32(1)", "break"},
		{"function-valued unknown control", "v[0] + v[1]", "try v[0]"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			fn, loop := parseLoopHomes(t, strings.Replace(loopHomesSource, tc.old, tc.replacement, 1))
			if got, _ := loopHomeUses(fn, loop, "v", 16); got != nil {
				t.Fatalf("unsafe shape was admitted: %v", got)
			}
		})
	}
	fn, loop := parseLoopHomes(t, loopHomesSource)
	for _, length := range []int64{0, 65} {
		if got, _ := loopHomeUses(fn, loop, "v", length); got != nil {
			t.Fatalf("unsupported length %d admitted", length)
		}
	}
	loop.Body.Order = "ordered"
	if got, _ := loopHomeUses(fn, loop, "v", 16); got != nil {
		t.Fatal("ordered body admitted")
	}
}

func TestLoopArrayHomeLookupPreservesIdentity(t *testing.T) {
	arr := &arrayLocal{elem: scalars["u32"], length: 16}
	g := &generator{
		arrays:           map[string]*arrayLocal{"v": arr},
		activeArrayHomes: map[string]*loopArrayHomeSet{"v": {array: arr, homes: map[int64]loopArrayHome{0: {hidden: "home"}}}},
	}
	index := &ast.IndexExpression{Left: &ast.Identifier{Value: "v"}, Index: &ast.IntegerLiteral{Value: 0}}
	if name, elem, ok := g.loopArrayElement(index); !ok || name != "home" || elem != scalars["u32"] {
		t.Fatal("exact selected element was not found")
	}
	index.Index = &ast.IntegerLiteral{Value: 1}
	if _, _, ok := g.loopArrayElement(index); ok {
		t.Fatal("unselected element found")
	}
	index.Index = &ast.Identifier{Value: "i"}
	if _, _, ok := g.loopArrayElement(index); ok {
		t.Fatal("computed index found")
	}
	index.Index = &ast.IntegerLiteral{Value: 0}
	g.arrays["v"] = &arrayLocal{elem: scalars["u32"], length: 16}
	if _, _, ok := g.loopArrayElement(index); ok {
		t.Fatal("different array with same name found")
	}
	g.activeArrayHomes = nil
	if _, _, ok := g.loopArrayElement(index); ok {
		t.Fatal("home survived its region")
	}
}

func TestLoopArrayHomesPreloadFlushAndScope(t *testing.T) {
	for _, width := range []string{"u32", "u64"} {
		t.Run(width, func(t *testing.T) {
			source := `f: (n: u32): [16]u32 {
  v: [16]u32
  i: u32 = 0
  while i < n {
    v[0] = v[0] + v[1] + v[1]
    v[2] = v[2] + u32(1)
    i = i + u32(1)
  }
  v
}`
			fn, loop := parseLoopHomes(t, strings.ReplaceAll(source, "u32", width))
			elem := scalars[width]
			arr := &arrayLocal{elem: elem, length: 16, offset: 16}
			g := &generator{
				fn: fn, loopArrayHomesEnabled: true,
				arrays: map[string]*arrayLocal{"v": arr},
				scopes: []map[string]slotBinding{{}},
				regs:   map[string]int{}, slots: map[string]int64{}, types: map[string]scalar{},
				homesUsed: map[int]bool{}, flagsTo: map[string]string{}, defined: map[int]bool{},
				// Exactly two true callee homes; x16 must not be consumed.
				freeCallee: []int{19, 20, 16}, usedCallee: calleeHigh - calleeLow + 1,
				saveArea: 80,
			}
			finish := g.beginLoopArrayHomes(loop)
			if finish == nil || g.arrayHomesCount != 2 || len(g.items) != 2 {
				t.Fatalf("preload count=%d, items=%v", g.arrayHomesCount, g.items)
			}
			set := g.activeArrayHomes["v"]
			if len(set.homes) != 2 || !set.homes[0].written || set.homes[1].written {
				t.Fatalf("expected a written and a read-only home: %v", set.homes)
			}
			if _, selected := set.homes[2]; selected {
				t.Fatal("unselected written cell used a caller-saved home")
			}
			for i, item := range g.items {
				ins := item.(asm.Instruction)
				r := ins.Operands[0].(asm.Register)
				wantMem := g.slotMem(arr.offset + int64(i*elem.bits/8))
				if ins.Mnemonic != "ldr" || r != reg(g.regs[set.homes[int64(i)].hidden], elem) || ins.Operands[1] != wantMem {
					t.Fatalf("preload %d = %v", i, ins)
				}
				if r.Num < calleeLow || r.Num > calleeHigh {
					t.Fatalf("non-callee home: %v", r)
				}
			}
			g.label("loop_test")
			g.emit("bl", asm.Symbol{Name: "salt"}) // a call invalidates forwarding
			g.label("done_test")
			before := len(g.items)
			finish()
			if len(g.items) != before+1 {
				t.Fatalf("expected only the selected written cell to flush: %v", g.items[before:])
			}
			flush := g.items[before].(asm.Instruction)
			if flush.Mnemonic != "str" || flush.Operands[0] != reg(20, elem) || flush.Operands[1] != g.slotMem(arr.offset) {
				t.Fatalf("wrong post-exit flush: %v", flush)
			}
			if g.activeArrayHomes != nil || len(g.scopes) != 1 || len(g.regs) != 0 || g.arrays["v"] != arr {
				t.Fatal("private home scope outlived the loop or disturbed the backing array")
			}
		})
	}
}
