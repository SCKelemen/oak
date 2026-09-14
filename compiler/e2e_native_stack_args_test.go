package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Arguments beyond the eight integer registers (docs/spec/94-assembler.md
// §9, twenty-sixth increment): the ninth and later integer-class arguments
// travel in the caller's outgoing area under the target's convention
// (asm.LayoutArguments: Apple's packing on Darwin, 8-byte slots
// elsewhere), the callee reads them above its frame in the prologue, and
// the seam checker holds both sides to its own reading of the layout. A
// native caller reaching a C-compiled callee (one the backend leaves to C,
// here for its array result) and a C-compiled main reaching a native
// callee cross the same convention, so the platform's C compiler is the
// oracle for the layout itself; the C build of the whole program is the
// oracle for the values.
const nativeStackArgsProgram = `
Pair: type = struct { lo: u32, hi: u32 }
Big: type = struct { a: u64, b: u64, c: u64 }

// Nine scalars of mixed widths: the ninth (a narrow one) is on the stack.
nine: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32, i: u8) -> u32 = a + b + c + d + e + f + g + h + u32(i)

// Twelve: three stack arguments of three widths, plus a Bool.
twelve: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32, i: u8, j: u16, k: u64, m: Bool) -> u64 = u64(a + b + c + d + e + f + g + h) + u64(i) + u64(j) + k + (m ? u64(1) | u64(0))

// A view whose pair lands on the stack, walked in a loop.
tail_sum: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, v: []u32) -> u32 {
  acc: u32 = a + b + c + d + e + f + g
  i: u32 = u32(0)
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}

// A small record's chunk and a large record's reference on the stack.
records_last: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32, p: Pair, q: Big) -> u64 = u64(a + b + c + d + e + f + g + h + p.lo + p.hi) + q.a + q.b + q.c

// Left to the C backend (a foreign pointer local is outside the native
// subset): a native caller reaches it with two stack arguments.
c_side: (p1: u32, p2: u32, p3: u32, p4: u32, p5: u32, p6: u32, p7: u32, p8: u32, p9: u32, p10: u16) -> u32 {
  nothing: c.Ptr = c.null()
  _ = nothing
  p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9 + u32(p10)
}

through_c: (base: u32) -> u32 = c_side(base, base, base, base, base, base, base, base, u32(100), u16(7))

main: (): i32 {
  assert(nine(u32(1), u32(2), u32(3), u32(4), u32(5), u32(6), u32(7), u32(8), u8(9)) == u32(45))
  assert(twelve(u32(1), u32(2), u32(3), u32(4), u32(5), u32(6), u32(7), u32(8), u8(9), u16(300), u64(1000), true) == u64(1346))
  buf: [3]u32 = [u32(10), u32(20), u32(30)]
  assert(tail_sum(u32(1), u32(1), u32(1), u32(1), u32(1), u32(1), u32(1), view(&buf)) == u32(67))
  p: Pair = Pair { lo: u32(5), hi: u32(6) }
  q: Big = Big { a: u64(100), b: u64(200), c: u64(300) }
  assert(records_last(u32(1), u32(1), u32(1), u32(1), u32(1), u32(1), u32(1), u32(1), p, q) == u64(619))
  assert(through_c(u32(2)) == u32(123))
  42
}
`

func TestE2ENativeStackArgs(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("stackargs.oak", nativeStackArgsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_stack_args", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native stack args: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"nine", "twelve", "tail_sum", "records_last", "through_c", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	// The byte parameter on the stack is read from its frame slot
	// (docs/spec/94-assembler.md §8, thirty-second increment).
	for _, fn := range []string{"nine", "tail_sum"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven by the verifier; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "c_side left to the C backend") {
		t.Errorf("c_side should stay with the C backend (the mixed-ABI leg); diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_stack_args_c", New().WithSource("stackargs.oak", nativeStackArgsProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_stack_args_portable", New().WithSource("stackargs.oak", nativeStackArgsProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
