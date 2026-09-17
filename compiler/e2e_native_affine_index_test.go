package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
)

// The OS page-zeroing shape: a guarded record field, indexed by a table
// number times a page's entries plus a unit-stride loop counter. There is
// no assumption that a table number loaded from a free list is in range.
const nativeAffineIndexProgram = `
Pool: type = struct { words: [6144]u64, tag: u64 }
zero_page: (p: [*]Pool, dom: u32, table: u16): () {
  i: u32 = 0
  while i < u32(2048) {
    p[dom].words[u32(table) * u32(2048) + i] = u64(0)
    i = i + u32(1)
  }
}

main: (): i32 {
  pools: [2]Pool
  pools[0].words[2048] = u64(99)
  pools[1].words[0] = u64(11)
  pools[1].words[2047] = u64(12)
  pools[1].words[2048] = u64(13)
  pools[1].words[3071] = u64(14)
  pools[1].words[4095] = u64(15)
  pools[1].words[4096] = u64(16)
  pools[1].tag = u64(42)
  zero_page(span(&pools), u32(1), u16(1))
  assert(pools[0].words[2048] == u64(99))
  assert(pools[1].words[0] == u64(11))
  assert(pools[1].words[2047] == u64(12))
  assert(pools[1].words[2048] == u64(0))
  assert(pools[1].words[3071] == u64(0))
  assert(pools[1].words[4095] == u64(0))
  assert(pools[1].words[4096] == u64(16))
  assert(pools[1].tag == u64(42))
  42
}
`

func TestE2ENativeAffineIndexLoop(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "zero_page")
	comp := New().WithSource("affine_index.oak", nativeAffineIndexProgram).WithNativeBodies().WithNativeAsm()
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if v := model.NativeVerdicts["zero_page"]; v.Kind != asm.VerdictProven {
		t.Fatalf("zero_page: %s: %s", v.Kind, v.Message)
	}
	var selected *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "zero_page" {
			selected = fn
		}
	}
	if selected == nil {
		t.Fatal("missing native zero_page")
	}
	if nativegen.CarriedLoopIndices(selected) != 1 {
		t.Fatalf("the proven carried index must win:\n%s", nativegen.Describe(selected))
	}
	metrics := nativegen.Metrics(selected)
	if len(metrics.LoopBodies) != 1 || metrics.LoopBodies[0].Instructions != 6 || metrics.LoopBodies[0].Stores != 1 || metrics.LoopBodies[0].Guards != 1 {
		t.Fatalf("want six instructions, one scalar store and the original bounds guard: %+v", metrics.LoopBodies)
	}
	_, code, abnormal := buildAndRunFrom(t, "affine_index", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit=(%d, abnormal=%v), want 42", code, abnormal)
	}
	_, code, abnormal = buildAndRunFrom(t, "affine_index_c", New().WithSource("affine_index.oak", nativeAffineIndexProgram))
	if abnormal || code != 42 {
		t.Fatalf("C: exit=(%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeAffineIndexLoopTraps(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "zero_page")
	for name, call := range map[string]string{
		"bad table":  "zero_page(span(&pools), u32(1), u16(3))",
		"bad domain": "zero_page(span(&pools), u32(2), u16(1))",
	} {
		t.Run(name, func(t *testing.T) {
			source := strings.Replace(nativeAffineIndexProgram, "zero_page(span(&pools), u32(1), u16(1))", call, 1)
			for _, native := range []bool{false, true} {
				comp := New().WithSource("affine_trap.oak", source)
				if native {
					comp = comp.WithNativeBodies().WithNativeAsm()
					comp.options.InlineHelpers = true
					model, err := comp.Check().Get()
					if err != nil {
						t.Fatal(err)
					}
					if v := model.NativeVerdicts["zero_page"]; v.Kind != asm.VerdictProven {
						t.Fatalf("zero_page lost proof: %s", v.Message)
					}
				}
				if _, code, abnormal := buildAndRunFrom(t, "affine_trap", comp); !abnormal {
					t.Fatalf("native=%v: out-of-range call returned %d instead of trapping", native, code)
				}
			}
		})
	}
}
