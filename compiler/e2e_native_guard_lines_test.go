package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A refused elision falls back one source line at a time
// (docs/spec/94-assembler.md §9 "Check elision"): in a binary search the
// outer loop's probe read is proven and admitted by the seam checker off
// the loop's own exit test, while the inner loop's key read is proven by
// the decreasing-bound law the checker cannot read at the seam; the
// compiler keeps the guard of the key read's line and leaves the probe
// read unguarded, and the verifier still judges the body. The C backend's
// realization is the oracle for the value.
const nativeGuardLinesProgram = `
count_hits: (keys: []u64, probes: []u64): u32 {
  hits: u32 = 0
  p: u32 = 0
  while p < len(probes) {
    target: u64 = probes[p]
    lo: u32 = 0
    hi: u32 = len(keys)
    found: Bool = false
    while lo < hi && !found {
      mid: u32 = lo + (hi - lo) / u32(2)
      k: u64 = keys[mid]
      k == target ? { found = true }
      | k < target ? { lo = mid + u32(1) }
      | { hi = mid }
    }
    found ? { hits = hits + u32(1) }
    p = p + u32(1)
  }
  hits
}

main: (): i32 {
  keys: [8]u64 = [u64(1), u64(3), u64(5), u64(7), u64(9), u64(11), u64(13), u64(15)]
  probes: [5]u64 = [u64(3), u64(4), u64(9), u64(15), u64(16)]
  i32_bits_u32(count_hits(view(&keys), view(&probes))) + 39
}
`

func TestE2ENativeGuardLines(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("guards.oak", nativeGuardLinesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_guard_lines", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native guard lines: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "count_hits: 1 element guard(s) elided under the checker's own facts, the guards of line(s) 12 kept") {
		t.Errorf("the probe read must stay elided while the key read's line keeps its guard; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "count_hits keeps its element guards") {
		t.Errorf("the body must not fall back to every guard; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit count_hits: proven equal to its Oak body") && !strings.Contains(joined, "asm unit count_hits: agrees with its Oak body") {
		t.Errorf("count_hits must keep its verdict; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_guard_lines_c", New().WithSource("guards.oak", nativeGuardLinesProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
