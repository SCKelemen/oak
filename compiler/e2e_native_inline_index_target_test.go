package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// A leaf helper called in an index-assignment's target (docs/spec/90-backend.md
// §9, "Inlining as a source transformation"): `pages[cell(t, j)] = u64(0)`
// — the os pilot's page-zeroing loop — is inlined like a call in the
// value, so the native unit keeps no `bl cell` in its loop and the C
// backend agrees on the values.
const nativeInlineIndexTargetProgram = `
entries: u32 = u32(8)

cell: (table: u16, idx: u32): u32 { u32(table) * entries + idx }

clear_table: (pages: [*]u64, table: u16): () {
  j: u32 = 0
  while j < entries {
    pages[cell(table, j)] = u64(0)
    j = j + u32(1)
  }
}

main: (): i32 {
  pages: [16]u64 = [16]u64{ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 }
  clear_table(span(&pages), u16(1))
  // The first table keeps its eight ones; the second is zeroed.
  i32_bits_u32(u32_trunc_u64(pages[0] + pages[7] + pages[8] + pages[15]) * u32(10) + u32(2))
}
`

func TestE2ENativeInlineIndexTarget(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("iit.oak", nativeInlineIndexTargetProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	// The emitting stages run the inliner; the semantic model inspected
	// here asks for it explicitly.
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, fn := range model.AsmFunctions {
		if fn.Name != "clear_table" {
			continue
		}
		for _, item := range fn.Items {
			if ins, isIns := item.(asm.Instruction); isIns && ins.Mnemonic == "bl" {
				t.Errorf("clear_table must inline the index helper, found %v", ins)
			}
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "native_inline_index_target", comp)
	if abnormal || code != 22 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 22\n%s", code, abnormal, strings.Join(infos, "\n"))
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_inline_index_target_c", New().WithSource("iit.oak", nativeInlineIndexTargetProgram)); abnormal || code != 22 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 22", code, abnormal)
	}
}
