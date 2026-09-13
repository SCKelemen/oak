package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// The OS pilot's N1 (docs/notes/os-language-requests-2026-09.md): a
// function that reads constant top-level bindings — `page_shift`, `mask`,
// the page-table walk's `page_size` and `entries` — lowers through the
// native backend, the reads folded to their typed literals; the C emitter
// keeps the `static const`. A binding some statement writes is not a
// constant and its reader stays with the C backend.
const nativeConstantsProgram = `
page_shift: u64 = u64(14)
mask: u64 = u64(511)
entries: u32 = 512
counter: u32 = u32(0)

index_of: (va: u64): u32 = u32_trunc_u64((va >> page_shift) & mask)
capacity: (): u32 = entries * u32(2)
bump: (): u32 {
  counter = counter + u32(1)
  counter
}

main: (): i32 {
  i32_bits_u32(index_of(u64(16384) * u64(700)) + capacity() + bump())
}
`

func TestE2ENativeConstantReads(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("consts.oak", nativeConstantsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_constants", comp)
	joined := strings.Join(infos, "\n")
	// 700 % 512 = 188, plus 1024, plus 1 = 1213; the process exit code
	// carries the low byte, 189.
	if abnormal || code != 1213%256 {
		t.Fatalf("exit = (%d, abnormal=%v), want %d\n%s", code, abnormal, 1213%256, joined)
	}
	for _, fn := range []string{"index_of", "capacity"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s reads constants and must lower natively; diagnostics:\n%s", fn, joined)
		}
	}
	// A written global is addressed storage (docs/spec/94-assembler.md §9,
	// the OS pilot's N3): its writer lowers too, trusted against the C
	// oracle.
	if !strings.Contains(joined, "asm unit bump:") {
		t.Errorf("bump writes a global and must lower natively through its address; diagnostics:\n%s", joined)
	}
	emitted, err := New().WithSource("consts.oak", nativeConstantsProgram).WithNativeBodies().EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(emitted, "static const u64 page_shift") {
		t.Errorf("the C keeps the constant global:\n%s", emitted[:min(len(emitted), 400)])
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_constants_c", New().WithSource("consts.oak", nativeConstantsProgram)); abnormal || code != 1213%256 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want %d", code, abnormal, 1213%256)
	}
}

// Constant globals through the native backend (docs/spec/94-assembler.md
// §9, sixteenth increment): a typed scalar top-level binding with a
// constant initializer that nothing writes — the C backend's `static const`
// rule (90-backend.md §8a) — is folded by the compiler and materialized as
// an immediate; the verifier reads the identifier as the same constant, so
// the functions over them are proven. A global some statement writes stays
// a mutable static in C, and a function reading it stays with the C
// backend. The program also holds the shapes the seam checker had refused
// before this increment: a short-circuit chain whose first operand is a
// call (the call spilled scratch registers allocated for the enclosing
// results but never written), a span walked in one arm of a function
// whose other arm placed the result in the span's base register, and a
// unit function whose last statement is a conditional. The C backend's
// realization of the same program is the oracle.
const nativeConstantProgram = `
LIMIT: u32 = 40
STEP: u32 = 2
MASK: u64 = u64(0xFF00) | u64(0x00FF)
NEG: i32 = -3
SMALL: u8 = 200
FLAG: Bool = true
T_PIPE: u32 = 17
DOUBLED: u32 = STEP * LIMIT
counter: u32 = 0

scale: (x: u32) -> u32 = x * STEP + LIMIT
low_bytes: (x: u64) -> u64 = x & MASK
shift_neg: (x: i32) -> i32 = x + NEG
is_pipe: (k: u32) -> Bool = k == T_PIPE
pick: (x: u32) -> u32 = FLAG ? x | u32(0)
narrow: (b: u8) -> u8 = b + SMALL
doubled: (): u32 = DOUBLED

bump: (): () { counter = counter + u32(1) }
read_counter: (): u32 = counter

// A unit function whose last statement is a conditional (no call inside,
// so the inliner leaves it as written).
report: (out: [*]u32, k: u32): () {
  k == T_PIPE ? { out[0] = u32(1) } | { out[0] = u32(2) }
}

is_digit: (b: u32) -> Bool = b >= u32(48) && b <= u32(57)
// The first operand of the chain is a call: the enclosing results are
// allocated but unwritten when it spills.
is_hex: (b: u32) -> Bool = is_digit(b) || (b >= u32(97) && b <= u32(102)) || (b >= u32(65) && b <= u32(70))

// The result of one arm lands in x0, the base of dst; the other arm walks dst.
copy_into: (dst: [*]u8, src: []u8) -> u32 {
  n: u32 = len(src)
  len(dst) < n ? { u32(0) } | {
    i: u32 = u32(0)
    while i < n {
      dst[i] = src[i]
      i = i + u32(1)
    }
    n
  }
}

main: (): i32 {
  assert(scale(u32(1)) == u32(42))
  assert(low_bytes(u64(0x12345678)) == u64(0x5678))
  assert(shift_neg(i32(1)) == i32(-2))
  assert(is_pipe(T_PIPE))
  assert(!is_pipe(u32(16)))
  assert(pick(u32(7)) == u32(7))
  assert(narrow(u8(100)) == u8(44))
  assert(doubled() == u32(80))
  flags: [1]u32
  report(span(&flags), T_PIPE)
  assert(flags[0] == u32(1))
  report(span(&flags), u32(0))
  assert(flags[0] == u32(2))
  bump()
  bump()
  assert(read_counter() == u32(2))
  assert(is_hex(u32(65)))
  assert(is_hex(u32(102)))
  assert(!is_hex(u32(103)))
  a: [4]u8 = [u8(1), u8(2), u8(3), u8(4)]
  b: [4]u8
  assert(copy_into(span(&b), view(&a)) == u32(4))
  assert(b[3] == u8(4))
  c: [2]u8
  assert(copy_into(span(&c), view(&a)) == u32(0))
  42
}
`

func TestE2ENativeConstants(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("constants.oak", nativeConstantProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_constants", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native constants: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	// (main calls bump, which the inliner folds into it, so main itself
	// stays with the C backend beside the global it then writes.)
	for _, fn := range []string{"scale", "low_bytes", "shift_neg", "is_pipe", "pick", "narrow", "doubled", "report", "is_hex", "copy_into"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	// The constants are the verifier's too: the functions over them are
	// proven against their Oak bodies, the narrow one at its 8-bit contract.
	for _, fn := range []string{"scale", "low_bytes", "shift_neg", "is_pipe", "pick", "narrow", "doubled"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body; diagnostics:\n%s", fn, joined)
		}
	}
	// A written global is no constant: it is addressed storage
	// (docs/spec/94-assembler.md §9). Its writer lowers, trusted against the
	// C oracle; its reader is proven over the cell's entry value.
	for _, fn := range []string{"bump", "read_counter"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s touches the mutable global counter and must lower through its address; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit read_counter: proven equal to its Oak body (linear normal form 1*global:counter + 0") {
		t.Errorf("read_counter must be proven over the global's entry value; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_constants_c", New().WithSource("constants.oak", nativeConstantProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_constants_portable", New().WithSource("constants.oak", nativeConstantProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
