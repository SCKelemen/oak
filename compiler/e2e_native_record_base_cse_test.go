package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
)

// The large leading field makes each record wider than sixteen immediate
// bits, matching the OS stage-2 state record. Repeated field accesses would
// otherwise each materialize the stride and multiply the domain index.
const nativeRecordBaseCSEProgram = `
Big: type = struct { pad: [8192]u64, a: u64, b: u64, c: u64, d: u64 }
touch: (rows: [*]Big, dom: u32, choose: Bool): u64 {
  x: u64 = rows[dom].a
  choose ? {
    rows[dom].b = x + u64(1)
  } | {
    rows[dom].c = x + u64(2)
  }
  y: u64 = rows[dom].b + rows[dom].c
  rows[dom].d = y
  y
}
main: (): i32 {
  rows: [2]Big
  rows[1].a = u64(10)
  rows[1].b = u64(20)
  rows[1].c = u64(30)
  assert(touch(span(&rows), u32(1), true) == u64(41))
  assert(rows[1].b == u64(11))
  assert(rows[1].c == u64(30))
  assert(rows[1].d == u64(41))
  assert(touch(span(&rows), u32(1), false) == u64(23))
  assert(rows[1].b == u64(11))
  assert(rows[1].c == u64(12))
  assert(rows[1].d == u64(23))
  42
}
`

func TestE2ENativeRecordBaseCSE(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "touch")
	comp := New().WithSource("record_base_cse.oak", nativeRecordBaseCSEProgram).WithNativeBodies().WithNativeAsm()
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if v := model.NativeVerdicts["touch"]; v.Kind != asm.VerdictProven {
		t.Fatalf("touch: %s: %s", v.Kind, v.Message)
	}
	var selected *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "touch" {
			selected = fn
		}
	}
	if selected == nil {
		t.Fatal("missing native touch")
	}
	if nativegen.SharedRecordBases(selected) == 0 {
		t.Fatalf("the proven record base must be shared:\n%s", nativegen.Describe(selected))
	}
	_, code, abnormal := buildAndRunFrom(t, "record_base_cse", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit=(%d, abnormal=%v), want 42", code, abnormal)
	}
	_, code, abnormal = buildAndRunFrom(t, "record_base_cse_c", New().WithSource("record_base_cse.oak", nativeRecordBaseCSEProgram))
	if abnormal || code != 42 {
		t.Fatalf("C: exit=(%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRecordBaseCSETrap(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "touch")
	source := strings.Replace(nativeRecordBaseCSEProgram, "touch(span(&rows), u32(1), true)", "touch(span(&rows), u32(2), true)", 1)
	for _, native := range []bool{false, true} {
		comp := New().WithSource("record_base_cse_trap.oak", source)
		if native {
			comp = comp.WithNativeBodies().WithNativeAsm()
			comp.options.InlineHelpers = true
			model, err := comp.Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			if v := model.NativeVerdicts["touch"]; v.Kind != asm.VerdictProven {
				t.Fatalf("touch lost proof: %s", v.Message)
			}
		}
		if _, code, abnormal := buildAndRunFrom(t, "record_base_cse_trap", comp); !abnormal {
			t.Fatalf("native=%v: out-of-range call returned %d instead of trapping", native, code)
		}
	}
}
