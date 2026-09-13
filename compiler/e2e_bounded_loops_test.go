package compiler

import (
	"regexp"
	"strings"
	"testing"
)

// Bounded loops over a fixed array stay check-free (docs/spec/50-borrowing.md,
// extent facts): the count guarded by a literal around the loop, folded
// into the loop condition, clamped by saturation, taken as the minimum of
// the count and the length through a conditional (the OS pilot's resync
// loop, Zig's bounded slice loop spelled in Oak), and read twice per
// iteration. Every element access is proven, so the emitted C carries no
// oak_index, and the program runs.
const boundedLoopProgram = `// A: the guard around a while over a parameter-bounded count.
resync_a: (buf: [8]u8, n: u32) -> u32 {
  acc: u32 = u32(0)
  n <= u32(8) ? {
    i: u32 = u32(0)
    while i < n {
      acc = acc + u32(buf[i])
      i = i + u32(1)
    }
  } | { }
  acc
}

// B: the bound folded into the loop condition.
resync_b: (buf: [8]u8, n: u32) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < n && i < u32(8) {
    acc = acc + u32(buf[i])
    i = i + u32(1)
  }
  acc
}

// C: the count clamped by saturation before the loop.
resync_c: (buf: [8]u8, n: u64) -> u32 {
  acc: u32 = u32(0)
  count: u32 = u32_saturating_u64(n)
  i: u32 = u32(0)
  while i < count && count <= u32(8) {
    acc = acc + u32(buf[i])
    i = i + u32(1)
  }
  acc
}

// D: the bound read from len(buf) through a binding.
resync_d: (buf: [8]u8, n: u32) -> u32 {
  acc: u32 = u32(0)
  limit: u32 = n < len(buf) ? n | len(buf)
  i: u32 = u32(0)
  while i < limit {
    acc = acc + u32(buf[i])
    i = i + u32(1)
  }
  acc
}

// E: a guard on the parameter, the loop in the same block, the index a u64.
resync_e: (buf: [8]u8, n: u32) -> u32 {
  acc: u32 = u32(0)
  n <= u32(8) ? {
    i: u32 = u32(0)
    while i < n {
      acc = acc + u32(buf[i]) + u32(buf[i])
      i = i + u32(1)
    }
  } | { }
  acc
}

main: (): i32 {
  data: [8]u8
  i32_bits_u32(resync_a(data, u32(3)) + resync_b(data, u32(3)) + resync_c(data, u64(3)) + resync_d(data, u32(3)) + resync_e(data, u32(3)))
}
`

func TestE2EBoundedLoopsAreCheckFree(t *testing.T) {
	code, err := New().WithSource("bounded.oak", boundedLoopProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, fn := range []string{"resync_a", "resync_b", "resync_c", "resync_d", "resync_e"} {
		body := regexp.MustCompile(`(?s)oak_` + fn + `\(.*?\n}\n`).FindString(code)
		if body == "" {
			t.Fatalf("%s not emitted", fn)
		}
		if strings.Contains(body, "oak_index") || strings.Contains(body, "oak_lv_idx") {
			t.Errorf("%s carries a bounds check:\n%s", fn, body)
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "bounded_loops", New().WithSource("bounded.oak", boundedLoopProgram)); abnormal || exit != 0 {
		t.Fatalf("bounded loops: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}
