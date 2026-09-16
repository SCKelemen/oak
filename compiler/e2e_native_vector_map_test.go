package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// Map vectorization (docs/spec/94-assembler.md §9 "Map vectorization";
// nativegen/vector_map.go, the `vectorize-maps` candidate). An
// element-wise map over spans — two of equal length under the guard, or
// one in place — runs its main loop one vector a trip: a `ldr q`, the
// lane-wise operations, a `str q`, no scalar element access; the
// remainder loop stays as written; the body is proven against the
// rewritten source with the span memory it writes. A float map's lanes
// round as its scalar does, so it vectorizes too; a zip reads several
// spans of one length; byte and halfword maps run sixteen and eight
// lanes a trip.
const nativeVectorMapProgram = `
add_k: (dst: [*]u32, a: []u32, k: u32) -> () {
  len(dst) == len(a) ? {
    i: u32 = u32(0)
    while i < len(a) {
      dst[i] = a[i] + k
      i = i + u32(1)
    }
  } | { }
}

bump: (v: [*]u32, k: u32) -> () {
  i: u32 = u32(0)
  while i < len(v) {
    v[i] = (v[i] ^ k) + u32(1)
    i = i + u32(1)
  }
}

mask64: (dst: [*]u64, a: []u64, m: u64) -> () {
  len(dst) == len(a) ? {
    i: u32 = u32(0)
    while i < len(a) {
      dst[i] = a[i] & m
      i = i + u32(1)
    }
  } | { }
}

fadd_k: (dst: [*]f32, a: []f32, k: f32) -> () {
  len(dst) == len(a) ? {
    i: u32 = u32(0)
    while i < len(a) {
      dst[i] = a[i] * k + 0.5
      i = i + u32(1)
    }
  } | { }
}

xor_mask: (dst: [*]u8, a: []u8, m: u8) -> () {
  len(dst) == len(a) ? {
    i: u32 = u32(0)
    while i < len(a) {
      dst[i] = a[i] ^ m
      i = i + u32(1)
    }
  } | { }
}

fill16: (v: [*]u16, x: u16) -> () {
  i: u32 = u32(0)
  while i < len(v) {
    v[i] = x
    i = i + u32(1)
  }
}

sum_ab: (dst: [*]u32, a: []u32, b: []u32) -> () {
  len(dst) == len(a) && len(b) == len(a) ? {
    i: u32 = u32(0)
    while i < len(a) {
      dst[i] = a[i] + b[i]
      i = i + u32(1)
    }
  } | { }
}

main: (): i32 {
  xs: [11]u32 = [11]u32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 }
  ys: [11]u32 = [11]u32{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }
  zs: [5]u64 = [5]u64{ 15, 255, 4095, 65535, 1048575 }
  ws: [5]u64 = [5]u64{ 0, 0, 0, 0, 0 }
  fs: [3]f32 = [3]f32{ 0.5, 1.5, 2.0 }
  gs: [3]f32 = [3]f32{ 0.0, 0.0, 0.0 }
  bs: [19]u8 = [19]u8{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19 }
  cs: [19]u8 = [19]u8{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }
  hs: [9]u16 = [9]u16{ 0, 0, 0, 0, 0, 0, 0, 0, 0 }
  add_k(span(&ys), view(&xs), u32(3))
  bump(span(&ys), u32(1))
  mask64(span(&ws), view(&zs), u64(255))
  fadd_k(span(&gs), view(&fs), 2.0)
  sum_ab(span(&ys), view(&xs), view(&ys))
  xor_mask(span(&cs), view(&bs), u8(255))
  fill16(span(&hs), u16(7))
  // ys = ((x + 3) ^ 1) + 1 over 1..11 sums to 111, plus xs again: 177;
  // ws sums to 1035; gs[2] is 2.0 * 2.0 + 0.5; cs[0] is 254, cs[18] is
  // 236, hs[8] is 7.
  drop: u32 = gs[2] == 4.5 ? u32(7) | u32(0)
  narrow: u32 = u32(cs[0]) + u32(cs[18]) + u32(hs[8])
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(ys) {
    acc = acc + ys[i]
    i = i + u32(1)
  }
  j: u32 = u32(0)
  wsum: u64 = u64(0)
  while j < len(ws) {
    wsum = wsum + ws[j]
    j = j + u32(1)
  }
  i32_bits_u32((acc + u32_trunc_u64(wsum) + narrow) - drop)
}
`

func TestE2ENativeVectorMap(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("vecmap.oak", nativeVectorMapProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	for _, name := range []string{"add_k", "bump", "mask64", "fadd_k", "sum_ab", "xor_mask", "fill16"} {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven equal to its Oak body") {
			t.Errorf("%s must be proven; diagnostics:\n%s", name, joined)
		}
	}
	// Each integer map's main loop: one vector load, one vector store, no
	// scalar element access; the map is reported as vectorized.
	for _, shape := range []struct {
		unit, arrangement string
	}{{"add_k", "4s"}, {"bump", "4s"}, {"mask64", "2d"}, {"fadd_k", "4s"}, {"sum_ab", "4s"}, {"xor_mask", "16b"}, {"fill16", "8h"}} {
		if n := nativegen.VectorizedMaps(units[shape.unit]); n != 1 {
			t.Errorf("%s must be vectorized once, got %d:\n%s", shape.unit, n, joined)
		}
		vecLoads, vecStores, scalarAccesses := 0, 0, 0
		for _, ins := range mainLoopOf(units[shape.unit]) {
			if len(ins.Operands) == 0 {
				continue
			}
			reg, isReg := ins.Operands[0].(asm.Register)
			switch {
			case ins.Mnemonic == "ldr" && isReg && reg.Vec == "q":
				vecLoads++
			case ins.Mnemonic == "str" && isReg && reg.Vec == "q":
				vecStores++
			case ins.Mnemonic == "ldr" || ins.Mnemonic == "str" || ins.Mnemonic == "ldp" || ins.Mnemonic == "stp":
				scalarAccesses++
			}
		}
		wantLoads := 1
		switch shape.unit {
		case "sum_ab":
			wantLoads = 2 // the zip reads two spans
		case "fill16":
			wantLoads = 0 // a fill reads nothing
		}
		if vecLoads != wantLoads || vecStores != 1 || scalarAccesses != 0 {
			t.Errorf("%s's main loop must be %d vector load(s) and one vector store, got %d, %d, and %d scalar accesses:\n%s", shape.unit, wantLoads, vecLoads, vecStores, scalarAccesses, nativegen.Describe(units[shape.unit]))
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "native_vector_map", comp)
	if abnormal || code != (177+1035+497-7)%256 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want %d\n%s", code, abnormal, (177+1035+497-7)%256, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_vector_map_c", New().WithSource("vecmap.oak", nativeVectorMapProgram)); abnormal || code != (177+1035+497-7)%256 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want %d", code, abnormal, (177+1035+497-7)%256)
	}
}
