package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

func resultHomeGenerator(t *testing.T, width string) (*generator, *arrayLocal, *ast.WhileStatement) {
	t.Helper()
	fn, loop := parseLoopHomes(t, strings.ReplaceAll(loopHomesSource, "u32", width))
	g := &generator{
		fn: fn, loopResultHomesEnabled: true,
		resultIndirect: true, resultAreaReg: 8, returnSlot: "v",
		layouts: map[string]*recordLayout{}, arrays: map[string]*arrayLocal{},
		scopes: []map[string]slotBinding{{}},
		regs:   map[string]int{}, slots: map[string]int64{}, types: map[string]scalar{},
		homesUsed: map[int]bool{}, flagsTo: map[string]string{}, defined: map[int]bool{},
		freeCallee: []int{19, 20, 16}, usedCallee: calleeHigh - calleeLow + 1, saveArea: 80,
	}
	g.resultRecord = g.arrayLayout(scalars[width], 16)
	arr := g.arrayDeclarationStorage("v", scalars[width], 16)
	g.arrays["v"] = arr
	if !arr.resultStorage || !arr.inReg {
		t.Fatal("fixture did not obtain named-local result storage")
	}
	return g, arr, loop
}

func TestLoopResultHomeStorageEligibility(t *testing.T) {
	for _, tc := range []struct {
		name   string
		change func(*generator, *arrayLocal)
	}{
		{"disabled", func(g *generator, a *arrayLocal) { g.loopResultHomesEnabled = false; g.loopArrayHomesEnabled = true }},
		{"untagged same register", func(g *generator, a *arrayLocal) { a.resultStorage = false }},
		{"parameter", func(g *generator, a *arrayLocal) { a.paramRef = true }},
		{"read-only", func(g *generator, a *arrayLocal) { a.readOnly = true }},
		{"record elements", func(g *generator, a *arrayLocal) { a.elemLayout = g.resultRecord }},
		{"wrong base", func(g *generator, a *arrayLocal) { a.reg = 9 }},
		{"interior address", func(g *generator, a *arrayLocal) { a.offset = 8 }},
		{"temporary address", func(g *generator, a *arrayLocal) { a.temps = []int{8} }},
		{"frame impostor", func(g *generator, a *arrayLocal) { a.inReg = false; g.loopArrayHomesEnabled = true }},
		{"wrong local", func(g *generator, a *arrayLocal) { g.returnSlot = "other" }},
		{"direct result", func(g *generator, a *arrayLocal) { g.resultIndirect = false }},
		{"missing layout", func(g *generator, a *arrayLocal) { g.resultRecord = nil }},
		{"different layout", func(g *generator, a *arrayLocal) { g.resultRecord = g.arrayLayout(scalars["u64"], 8) }},
		{"different extent", func(g *generator, a *arrayLocal) { a.length = 15 }},
		{"oversized", func(g *generator, a *arrayLocal) { a.length = 65 }},
		{"zero extent", func(g *generator, a *arrayLocal) { a.length = 0 }},
		{"narrow", func(g *generator, a *arrayLocal) { a.elem = scalars["u16"] }},
	} {
		t.Run(tc.name, func(t *testing.T) {
			g, arr, loop := resultHomeGenerator(t, "u32")
			if !g.loopHomeStorageEligible("v", arr) {
				t.Fatal("valid result provenance refused")
			}
			tc.change(g, arr)
			if g.loopHomeStorageEligible("v", arr) || g.beginLoopArrayHomes(loop) != nil {
				t.Fatal("invalid result provenance acquired homes")
			}
		})
	}
}

func TestLoopResultHomesAddressAndLifetime(t *testing.T) {
	for _, width := range []string{"u32", "u64"} {
		for _, base := range []int{8, 24} {
			t.Run(width+"/"+xr(base).Text, func(t *testing.T) {
				g, arr, loop := resultHomeGenerator(t, width)
				g.resultAreaReg, arr.reg = base, base
				finish := g.beginLoopArrayHomes(loop)
				if finish == nil || g.resultHomesCount != 2 || g.arrayHomesCount != 0 || len(g.items) != 2 {
					t.Fatalf("result homes=%d frame homes=%d, items=%v", g.resultHomesCount, g.arrayHomesCount, g.items)
				}
				// v[1] has more uses than v[0], so it receives the first home.
				for i, index := range []int64{1, 0} {
					ins := g.items[i].(asm.Instruction)
					want := asm.Memory{Base: xr(base), Offset: index * arr.elemSize()}
					if ins.Mnemonic != "ldr" || ins.Operands[1] != want {
						t.Fatalf("result preload used wrong address: %v", ins)
					}
				}
				g.label("result_loop")
				g.label("result_done")
				before := len(g.items)
				finish()
				for i, index := range []int64{1, 0} {
					ins := g.items[before+i].(asm.Instruction)
					want := asm.Memory{Base: xr(base), Offset: index * arr.elemSize()}
					if ins.Mnemonic != "str" || ins.Operands[1] != want {
						t.Fatalf("result flush used wrong address: %v", ins)
					}
				}
				if g.activeArrayHomes != nil || len(g.scopes) != 1 || len(g.regs) != 0 || g.arrays["v"] != arr {
					t.Fatal("result homes escaped their loop scope")
				}
			})
		}
	}
}

func TestLoopResultHomesBodyIsolation(t *testing.T) {
	for _, tc := range []struct {
		name, old, replacement string
	}{
		{"scalar call", "v[0] + v[1]", "mix(v[0], v[1])"},
		{"call before loop", "i: u32 = 0", "i: u32 = observe(seed)"},
		{"call after loop", "v[j] ^ seed", "observe(v[j])"},
		{"assertion", "i: u32 = 0", "assert(seed == u32(0))\n  i: u32 = 0"},
		{"span input", "seed: u32", "seed: []u32"},
		{"record input", "seed: u32", "seed: Record"},
		{"oversized input", "seed: u32", "seed: [65]u32"},
		{"narrow input", "seed: u32", "seed: [16]u16"},
		{"view", "i: u32 = 0", "alias = view(&v)\n  i: u32 = 0"},
		{"address", "i: u32 = 0", "alias = &v[0]\n  i: u32 = 0"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			g, arr, _ := resultHomeGenerator(t, "u32")
			g.fn, _ = parseLoopHomes(t, strings.Replace(loopHomesSource, tc.old, tc.replacement, 1))
			// Deliberately leave hasCalls false: the closed syntax check must
			// independently exclude observers, not trust a stale summary.
			if g.resultHomeBodyIsolated() || g.loopHomeStorageEligible("v", arr) {
				t.Fatal("observable or unsupported body admitted")
			}
		})
	}
	for _, tc := range []struct {
		name   string
		change func(*generator)
	}{
		{"call summary", func(g *generator) { g.hasCalls = true }},
		{"scalar global", func(g *generator) { g.globals = map[string]asm.Global{"seed": {}} }},
		{"aggregate global", func(g *generator) { g.aggregates = map[string]*ast.VariableDeclaration{"seed": {}} }},
		{"ordered", func(g *generator) { g.fn.Body.(*ast.BlockExpression).Block.Order = "ordered" }},
		{"missing function", func(g *generator) { g.fn = nil }},
		{"missing body", func(g *generator) { g.fn.Body = nil }},
		{"missing parameter", func(g *generator) { g.fn.Parameters[0] = nil }},
	} {
		t.Run(tc.name, func(t *testing.T) {
			g, arr, _ := resultHomeGenerator(t, "u32")
			tc.change(g)
			if g.loopHomeStorageEligible("v", arr) {
				t.Fatal("non-isolated body admitted")
			}
		})
	}
	// Owned value inputs rely on the existing result/input snapshot contract;
	// constant tables are read-only, not observable mutable result aliases.
	g, arr, _ := resultHomeGenerator(t, "u32")
	source := strings.Replace(loopHomesSource, "seed: u32", "input: [16]u32", 1)
	source = strings.ReplaceAll(source, "seed", "input[0] ^ IV[0]")
	g.fn, _ = parseLoopHomes(t, source)
	g.aggregates = map[string]*ast.VariableDeclaration{"IV": {}}
	g.tables = map[string]GlobalArray{"IV": {}}
	if !g.loopHomeStorageEligible("v", arr) {
		t.Fatal("owned input and immutable table refused")
	}
}

func TestLoopResultHomesRefuseTrapsBeforeFlush(t *testing.T) {
	for _, tc := range []struct{ name, expr string }{
		{"shift", "seed << n"},
		{"division", "seed / n"},
		{"remainder", "seed % n"},
		{"constant division", "seed / u32(2)"},
		{"dynamic index", "other[n]"},
		{"past extent", "other[16]"},
		{"float truncation", "u32_trunc_f64(1.5)"},
	} {
		for _, condition := range []bool{false, true} {
			t.Run(tc.name+map[bool]string{false: "/body", true: "/condition"}[condition], func(t *testing.T) {
				g, _, _ := resultHomeGenerator(t, "u32")
				source := loopHomesSource
				if condition {
					source = strings.Replace(source, "while i < n", "while i < ("+tc.expr+")", 1)
				} else {
					source = strings.Replace(source, "v[0] + v[1]", "v[0] + v[1] + ("+tc.expr+")", 1)
				}
				var loop *ast.WhileStatement
				g.fn, loop = parseLoopHomes(t, source)
				g.arrays["other"] = &arrayLocal{elem: scalars["u32"], length: 16}
				if g.resultHomeLoopTrapFree(loop) || g.beginLoopArrayHomes(loop) != nil {
					t.Fatal("potential trap can bypass result flush")
				}
			})
		}
	}
	g, _, loop := resultHomeGenerator(t, "u32")
	// The fixture has a computed index in the next loop, after this flush.
	if !g.resultHomeLoopTrapFree(loop) || g.beginLoopArrayHomes(loop) == nil {
		t.Fatal("post-flush computed access disqualified a trap-free interval")
	}
}

func TestLoopResultHomesLocalArrayExtents(t *testing.T) {
	for _, tc := range []struct {
		name, declaration, index string
		want                     bool
	}{
		{"explicit", "local: [4]u32 = [4]u32{1, 2, 3, 4}", "3", true},
		{"past local extent", "local: [4]u32 = [4]u32{1, 2, 3, 4}", "4", false},
		{"computed", "local: [4]u32 = [4]u32{1, 2, 3, 4}", "n", false},
		{"unknown extent", "local = [4]u32{1, 2, 3, 4}", "3", false},
		{"shadow array", "v: [4]u32\n local: [4]u32", "3", false},
		{"duplicate", "local: [4]u32\n local: [8]u32", "3", false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			g, _, _ := resultHomeGenerator(t, "u32")
			source := strings.Replace(loopHomesSource, "v[0] = v[0] + v[1]", tc.declaration+"\n v[0] = v[0] + v[1] + local["+tc.index+"]", 1)
			var loop *ast.WhileStatement
			g.fn, loop = parseLoopHomes(t, source)
			if got := g.resultHomeLoopTrapFree(loop); got != tc.want {
				t.Fatalf("trap-free=%v, want %v", got, tc.want)
			}
		})
	}
}
