package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// A loop whose exit test reads memory under an element guard
// (docs/spec/94-assembler.md §9, "Exit tests that read memory"): `while
// n > 0 && digits[n-1] == 48` lowers to a header holding the guard's
// branch to the trap and the guarded load before the second exit branch.
// The recognizer takes it as a loop and the summary couples it, so the
// body is proven or witnessed rather than unrolled past the path budget.
const nativeLoopHeaderLoadsProgram = `trim_zeros: (digits: []u8, n: u32) -> u32 {
  nd: u32 = n
  while nd > u32(0) && digits[nd - u32(1)] == u8(48) {
    nd = nd - u32(1)
  }
  nd
}

skip_spaces: (text: []u8, at: u32) -> u32 {
  i: u32 = at
  while i < len(text) && text[i] == u8(32) {
    i = i + u32(1)
  }
  i
}

// pub keeps is_blank a call (the source-level inliner leaves exported
// functions), so the loop's exit test and body call a program function,
// summarized on the iteration's fresh symbols.
pub is_blank: (b: u8) -> Bool = b == u8(32) || b == u8(9)

pub weight: (b: u8) -> u32 = u32(b) & u32(3)

skip_blank: (text: []u8, at: u32) -> u32 {
  i: u32 = at
  while i < len(text) && is_blank(text[i]) {
    i = i + u32(1)
  }
  i
}

weigh: (text: []u8) -> u32 {
  i: u32 = u32(0)
  total: u32 = u32(0)
  while i < len(text) {
    total = total + weight(text[i])
    i = i + u32(1)
  }
  total
}

main: (): i32 {
  buf: [6]u8 = [6]u8{49, 50, 48, 48, 32, 32}
  i32_bits_u32(trim_zeros(view(&buf), u32(4)) + skip_spaces(view(&buf), u32(4)) + skip_blank(view(&buf), u32(4)) + weigh(view(&buf)) - u32(2) - u32(6) - u32(6) - u32(3))
}
`

func TestE2ENativeLoopHeaderLoads(t *testing.T) {
	for _, tname := range []string{"freestanding/arm64", "linux/riscv64"} {
		tgt, err := target.Parse(tname)
		if err != nil {
			t.Fatal(err)
		}
		var native []string
		sink := func(d *diagnostic.Diagnostic) {
			if strings.HasPrefix(d.Message, "native backend: ") {
				native = append(native, d.Message)
			}
		}
		comp := New().WithSource("header_loads.oak", nativeLoopHeaderLoadsProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(sink)
		if _, err := comp.EmitC().Get(); err != nil {
			t.Fatalf("%s: native build: %v", tname, err)
		}
		joined := strings.Join(native, "\n")
		for _, fn := range []string{"trim_zeros", "skip_spaces", "skip_blank", "weigh"} {
			verdict := ""
			for _, m := range native {
				if strings.Contains(m, "asm unit "+fn+":") {
					verdict = m
				}
			}
			if verdict == "" {
				t.Errorf("%s: %s: no native verdict:\n%s", tname, fn, joined)
				continue
			}
			if strings.Contains(verdict, "more paths than the verifier's budget") || strings.Contains(verdict, "not verified") {
				t.Errorf("%s: %s must be decided by the loop summary, not trusted: %s", tname, fn, verdict)
			}
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "native_loop_header_loads", New().WithSource("header_loads.oak", nativeLoopHeaderLoadsProgram)); abnormal || exit != 0 {
		t.Fatalf("program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}
