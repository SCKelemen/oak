package compiler

// A read of a record span's array leaf at a computed index —
// `s[dom].pages[cell(t, i)]`, the OS pilot's get_page_entry — is proven
// in the linear normal form: the read is one atom named by its index's
// own form, which sees through the machine's argument-register masks
// (docs/spec/94-assembler.md §9, "the linear normal form sees through a
// covering mask"). It was evidence before, the bit-level decision over a
// 49152-element memory exceeding its budget.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeSelectIndexProgram = `Regime: type = struct {
  pages: [4096]u64
  root: u16
  pool_base: u64
}
entries: u32 = u32(64)
cell: (table: u16, idx: u32): u32 { u32(table) * entries + idx }
get_page_entry: (s: [*]Regime, dom: u32, t: u16, i: u32): u64 { s[dom].pages[cell(t, i)] }

main: (): i32 {
  regimes: [2]Regime
  s: [*]Regime = span(&regimes)
  s[1].pages[cell(u16(3), u32(5))] = u64(42)
  i32_bits_u32(u32_trunc_u64(get_page_entry(s, u32(1), u16(3), u32(5))))
}
`

func TestE2ENativeSelectAtComputedIndexProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("select_index.oak", nativeSelectIndexProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "select_index", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit get_page_entry: proven equal to its Oak body (linear normal form 1*s.pages[") {
		t.Fatalf("get_page_entry must be proven in the linear normal form over its read:\n%s", joined)
	}
}
