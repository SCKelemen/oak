package compiler

import (
	"os"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
)

const nativeTableViewProgram = `
TABLE: [12]u32 = [12]u32{0, 9, 3, 10, 10, 2, 11, 12, 3, 13, 13, 1}

lookup: (scalar: u32): u32 {
  table: []u32 = view(&TABLE)
  entries: u32 = len(table) / u32(3)
  low: u32 = 0
  high: u32 = entries
  while low < high {
    mid: u32 = low + (high - low) / u32(2)
    table[mid * u32(3) + u32(1)] < scalar ? { low = mid + u32(1) } | { high = mid }
  }
  low < entries && table[low * u32(3)] <= scalar ? { table[low * u32(3) + u32(2)] } | { u32(0) }
}

at: (i: u32): u32 {
  table: []u32 = view(&TABLE)
  i < len(table) ? table[i] | u32(0)
}

slice_len: (): u32 {
  table: []u32 = view(&TABLE)
  tail: []u32 = subslice(table, u32(3), u32(2))
  len(tail)
}

main: (): i32 {
  assert(slice_len() == u32(2))
  assert(at(u32(0)) == u32(0) && at(u32(11)) == u32(1) && at(u32(12)) == u32(0))
  assert(lookup(u32(0)) == u32(3) && lookup(u32(9)) == u32(3))
  assert(lookup(u32(10)) == u32(2) && lookup(u32(12)) == u32(3))
  assert(lookup(u32(13)) == u32(1) && lookup(u32(14)) == u32(0))
  assert(lookup(u32(4294967295)) == u32(0))
  i32(42)
}
`

func TestE2ENativeTableViews(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "lookup,at,slice_len")
	comp := New().WithSource("table_view.oak", nativeTableViewProgram).WithNativeBodies().WithNativeAsm()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"at", "slice_len"} {
		if verdict, ok := model.NativeVerdicts[name]; !ok || verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s not proven: %+v", name, verdict)
		}
	}
}

// Pin the actual large-table workload, not just a simplified lookup. The
// small lookup above exercises execution; its loop coupling remains outside
// the currently proven subset. No witness verdict substitutes for this proof.
func TestE2ENativeGraphemeTableViewProven(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "grapheme_class")
	data, err := os.ReadFile("../stdlib/grapheme.oak")
	if err != nil {
		t.Fatal(err)
	}
	text := string(data)
	start := strings.Index(text, "pub grapheme_table:")
	end := strings.Index(text, "// grapheme_gcb:")
	if start < 0 || end <= start {
		t.Fatal("grapheme fixture boundaries missing")
	}
	source := text[start:end] + "\nmain: (): i32 = 0\n"
	model, err := New().WithSource("grapheme_view.oak", source).WithNativeBodies().WithNativeAsm().Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if verdict, ok := model.NativeVerdicts["grapheme_class"]; !ok || verdict.Kind != asm.VerdictProven {
		t.Fatalf("grapheme_class not proven: %+v", verdict)
	}
	for _, body := range model.AsmFunctions {
		if body.Name == "grapheme_class" {
			text := nativegen.Describe(body)
			if strings.Contains(text, "udiv ") {
				t.Fatalf("known table extent still divided at runtime:\n%s", text)
			}
			return
		}
	}
	t.Fatal("missing selected grapheme_class body")
}

func TestE2ENativeTableViewExecution(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "lookup,at,slice_len")
	for _, native := range []bool{false, true} {
		comp := New().WithSource("table_view.oak", nativeTableViewProgram)
		if native {
			comp = comp.WithNativeBodies().WithNativeAsm()
		}
		if _, code, abnormal := buildAndRunFrom(t, "table_view", comp); abnormal || code != 42 {
			t.Fatalf("native=%v: exit=%d abnormal=%v", native, code, abnormal)
		}
	}
}
