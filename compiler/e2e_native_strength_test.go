package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Strength reduction on the AArch64 lane (docs/spec/90-backend.md §16,
// docs/spec/94-assembler.md §9): a multiplication by a power of two is a
// shift, an unsigned division by one a shift and a remainder a mask, and
// a nonzero constant divisor needs no zero test; a variable divisor keeps
// its test and its division. The verifier proves every body against the
// Oak semantics — the reduction is reported with its count only when the
// verdict is proven — and the C backend's realization is the oracle.
const nativeStrengthProgram = `
midpoint: (lo: u32, hi: u32) -> u32 = lo + (hi - lo) / u32(2)
page_of: (index: u32) -> u32 = index * u32(512) + index % u32(8)
thirds: (n: u32) -> u32 = n / u32(3) + n % u32(3)
halves: (n: i32) -> i32 = n / 4
divide: (n: u32, d: u32) -> u32 = n / d

search: (keys: []u32, target: u32) -> u32 {
  lo: u32 = u32(0)
  hi: u32 = len(keys)
  found: u32 = u32(0)
  while lo < hi && found == u32(0) {
    mid: u32 = midpoint(lo, hi)
    k: u32 = keys[mid]
    k == target ? { found = mid + u32(1) } | {
      k < target ? { lo = mid + u32(1) } | { hi = mid }
    }
  }
  found
}

main: (): i32 {
  keys: [8]u32 = [8]u32{ u32(2), u32(3), u32(5), u32(7), u32(11), u32(13), u32(17), u32(19) }
  assert(search(view(&keys), u32(11)) == u32(5))
  assert(search(view(&keys), u32(4)) == u32(0))
  assert(midpoint(u32(3), u32(10)) == u32(6))
  assert(page_of(u32(13)) == u32(6656) + u32(5))
  assert(thirds(u32(10)) == u32(4))
  assert(halves(-9) == -2)
  assert(divide(u32(9), u32(2)) == u32(4))
  42
}
`

func TestE2ENativeStrengthReduction(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("strength.oak", nativeStrengthProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_strength", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native strength reduction: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"midpoint", "page_of", "thirds", "halves", "divide", "search"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	// The reduced bodies prove: the shift and the mask meet the Oak
	// semantics in the verifier, and the untested constant division too.
	for fn, want := range map[string]string{"midpoint": "1 constant operation(s) strength-reduced, proven", "page_of": "2 constant operation(s) strength-reduced, proven", "thirds": "2 constant operation(s) strength-reduced, proven", "halves": "1 constant operation(s) strength-reduced, proven"} {
		if !strings.Contains(joined, fn+": "+want) {
			t.Errorf("%s: want %q; diagnostics:\n%s", fn, want, joined)
		}
	}
	if strings.Contains(joined, "divide: 1 constant operation") || strings.Contains(joined, "keeps its plain arithmetic") {
		t.Errorf("a variable divisor must keep its test, and no body may fall back; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_strength_c", New().WithSource("strength.oak", nativeStrengthProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
