package compiler

// Two late peepholes on the OS page walkers' shapes (docs/spec/94-assembler.md
// §9): a Bool materialized only to be branched on becomes the branch on the
// flags (`cset wN, cond; cbz wN, L` is `b.!cond L`), and a record-span
// element base with a stride below 2^16 (`movz wT, #2096; umaddl xD, wI,
// wT, xB`, no movk) is shared like the wide form, and a span-of-records
// element indexes by the variable's own register, so a second element
// through the same index spells the same base and needs no second guard.
// All stay verifier-gated.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

const nativeWalkerCleanupProgram = `Regime: type = struct {
  pages: [256]u64
  root: u16
  pool_base: u64
}

status: (va: u64, bound: u64): u8 {
  r: u8 = u8(1)
  oor: Bool = va >= bound
  r = oor ? u8(0) | r
  go: Bool = r == u8(1)
  go ? { r = u8(2) }
  r
}

root_pa: (s: [*]Regime, dom: u32): u64 {
  base: u64 = s[dom].pool_base
  root: u16 = s[dom].root
  base + u64(root) * u64(16384)
}

main: (): i32 {
  regimes: [2]Regime
  s: [*]Regime = span(&regimes)
  s[1].root = u16(3)
  s[1].pool_base = u64(65536)
  a: u8 = status(u64(5), u64(10))
  b: u8 = status(u64(10), u64(10))
  (a == u8(2) && b == u8(0) && root_pa(s, u32(1)) == u64(65536 + 3 * 16384)) ? 42 | 1
}
`

func TestE2ENativeWalkerCleanups(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("walker_cleanup.oak", nativeWalkerCleanupProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	joined := strings.Join(infos, "\n")
	count := func(fn *asm.Function, mnemonic string) int {
		n := 0
		for _, item := range fn.Items {
			if ins, ok := item.(asm.Instruction); ok && ins.Mnemonic == mnemonic {
				n++
			}
		}
		return n
	}
	for _, name := range []string{"status", "root_pa"} {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must stay proven:\n%s", name, joined)
		}
	}
	// The range test branches on its flags; the status test that feeds a
	// select keeps its Bool (a different shape).
	if n := count(units["status"], "cbz") + count(units["status"], "cbnz"); n != 0 || count(units["status"], "b.") == 0 {
		t.Fatalf("status: a Bool tested at once is a branch on the flags, got %d cbz/cbnz:\n%s\n%s", n, nativegen.Describe(units["status"]), joined)
	}
	// Both element bases index by dom's own register (no copy), so one
	// guard serves both reads.
	if n := count(units["root_pa"], "cmp"); n != 1 {
		t.Fatalf("root_pa: one guard for two reads through the same index, got %d cmp:\n%s", n, nativegen.Describe(units["root_pa"]))
	}
	for _, item := range units["root_pa"].Items {
		if ins, ok := item.(asm.Instruction); ok && ins.Mnemonic == "umaddl" {
			if idx, isReg := ins.Operands[1].(asm.Register); !isReg || idx.Num != 2 {
				t.Fatalf("root_pa: the element base indexes by the parameter's register: %v\n%s", ins, nativegen.Describe(units["root_pa"]))
			}
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "walker_cleanup", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
}
