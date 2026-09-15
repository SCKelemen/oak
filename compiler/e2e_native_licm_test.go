package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Loop-invariant code motion (docs/spec/94-assembler.md §9 "Loop
// invariants"; nativegen/licm.go): the os pilot's page-zeroing loop. The
// element address of `tables[dom]`, its stride constant, the global's
// address, and the guard `dom < len(tables)` leave the body — the guard
// peeled behind the loop's exit test, so a loop that never runs with an
// out-of-range `dom` does not trap — and the zero is stored from `xzr`.
// Both backends agree on the values.
const nativeLicmProgram = `
Page: type = struct { words: [64]u64, count: u32, tag: u32 }

fill: u64 = u64(7)

zero_page: (tables: [*]Page, dom: u32, n: u32): () {
  j: u32 = 0
  while j < n {
    tables[dom].words[j] = fill
    j = j + u32(1)
  }
}

main: (): i32 {
  pages: [2]Page = [2]Page{ Page { words: [64]u64{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }, count: u32(0), tag: u32(1) }, Page { words: [64]u64{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }, count: u32(0), tag: u32(2) } }
  zero_page(span(&pages), u32(1), u32(64))
  // A loop that never runs must not trap on its invariant guard.
  zero_page(span(&pages), u32(9), u32(0))
  // 7 + 7 + 0 + 1 + 2 = 17.
  i32_bits_u32(u32_trunc_u64(pages[1].words[0] + pages[1].words[63] + pages[0].words[5]) + pages[0].tag + pages[1].tag)
}
`

func TestE2ENativeLoopInvariants(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("licm.oak", nativeLicmProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	var fn *asm.Function
	for _, f := range model.AsmFunctions {
		if f.Name == "zero_page" {
			fn = f
		}
	}
	if fn == nil {
		t.Fatalf("zero_page was not lowered natively:\n%s", joined)
	}
	if strings.Contains(joined, "the checker refuses the lowering of zero_page") {
		t.Errorf("the hoisted form must be admitted:\n%s", joined)
	}
	counts := map[string]int{}
	traps := 0
	for _, ins := range loopBody(fn) {
		counts[ins.Mnemonic]++
		if ins.Mnemonic == "b." {
			if target, isSym := ins.Operands[0].(asm.Symbol); isSym && strings.HasPrefix(target.Name, "trap") {
				traps++
			}
		}
	}
	if counts["movz"]+counts["movk"] != 0 || counts["umaddl"] != 0 || counts["adrp"] != 0 {
		t.Errorf("the stride, the element address, and the global's address must leave the loop; body mnemonics: %v", counts)
	}
	if traps > 1 {
		t.Errorf("the invariant guard must be peeled, leaving the element guard alone; body mnemonics: %v", counts)
	}
	_, code, abnormal := buildAndRunFrom(t, "native_licm", comp)
	if abnormal || code != 17 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 17\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_licm_c", New().WithSource("licm.oak", nativeLicmProgram)); abnormal || code != 17 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 17", code, abnormal)
	}
}
