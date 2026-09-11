package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// runDeadline bounds the execution of a compiled test program.
const runDeadline = 60 * time.Second

// End-to-end execution: the full real pipeline — Oak source through
// Compilation.EmitC, compiled and linked by the system C compiler, executed
// as a native binary, with behavior asserted via exit status. Trap paths
// (bounds violations, failed assertions) must terminate abnormally: the
// never-UB guarantee, verified in running machine code.

func buildAndRun(t *testing.T, name, src string) (exitCode int, abnormal bool) {
	t.Helper()
	_, exitCode, abnormal = buildAndRunOutput(t, name, src)
	return exitCode, abnormal
}

// buildAndRunOutput additionally captures the binary's stdout and accepts
// extra cc flags (the differential intrinsic tests force the portable
// lowering with -DOAK_PORTABLE_INTRINSICS).
func buildAndRunOutput(t *testing.T, name, src string, ccFlags ...string) (stdout string, exitCode int, abnormal bool) {
	t.Helper()
	return buildAndRunFrom(t, name, New().WithSource(name+".oak", src), ccFlags...)
}

// buildAndRunFrom runs a fully configured compilation (asm units, profiles)
// through cc and executes the result.
func buildAndRunFrom(t *testing.T, name string, comp Compilation, ccFlags ...string) (stdout string, exitCode int, abnormal bool) {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}

	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}

	dir := t.TempDir()
	cPath := filepath.Join(dir, name+".c")
	binPath := filepath.Join(dir, name)
	if err := os.WriteFile(cPath, []byte(output), 0o644); err != nil {
		t.Fatal(err)
	}
	args := append([]string{"-std=c99", "-O1", "-ffp-contract=off"}, ccFlags...)
	args = append(args, "-o", binPath, cPath, "-lm")
	compile := exec.Command(cc, args...)
	if combined, err := compile.CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s\n--- generated C ---\n%s", err, combined, output)
	}

	// A program that does not finish within the deadline is a hang, reported
	// as such rather than stalling the whole package's test binary.
	ctx, cancel := context.WithTimeout(context.Background(), runDeadline)
	defer cancel()
	run := exec.CommandContext(ctx, binPath)
	var captured strings.Builder
	run.Stdout = &captured
	err = run.Run()
	if ctx.Err() == context.DeadlineExceeded {
		t.Fatalf("compiled program %s did not finish within %s (killed)", name, runDeadline)
	}
	if err == nil {
		return captured.String(), 0, false
	}
	if exitErr, ok := err.(*exec.ExitError); ok {
		if exitErr.ExitCode() >= 0 {
			return captured.String(), exitErr.ExitCode(), false
		}
		return captured.String(), -1, true // killed by a signal: the trap fired
	}
	t.Fatalf("failed to run binary: %v", err)
	return "", 0, false
}

func TestE2EExitCodePassthrough(t *testing.T) {
	code, abnormal := buildAndRun(t, "exitcode", `
main: (): i32 = 42
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2EFactorialLoopLowering(t *testing.T) {
	code, abnormal := buildAndRun(t, "factorial", `
fact: (n, acc: i32): i32 = n ?
  | 0 -> acc
  | _ -> fact(n - 1, acc * n)

main: (): i32 = fact(5, 1)
`)
	if abnormal || code != 120 {
		t.Fatalf("exit = (%d, abnormal=%v), want 120 (5! via loop-lowered recursion)", code, abnormal)
	}
}

func TestE2EBoundedLoopIndexingSum(t *testing.T) {
	code, abnormal := buildAndRun(t, "indexsum", `
sum: (buf: [8]u8): i32 {
  v: []u8 = buf[0:8]
  n: u32 = len(v)
  total: i32 = 0
  i: u32 = 0
  while i < n {
    total = total + i32(v[i])
    i = i + 1
  }
  total
}

main: (): i32 {
  data: [8]u8
  sum(data) + 7
}
`)
	// Zero-initialized array sums to 0; exit is the +7 sentinel proving the
	// loop, len, and bounds-checked indexing all executed.
	if abnormal || code != 7 {
		t.Fatalf("exit = (%d, abnormal=%v), want 7", code, abnormal)
	}
}

func TestE2EVariadicIteration(t *testing.T) {
	code, abnormal := buildAndRun(t, "variadic", `
total: (base: i32, rest: ...i32): i32 {
  acc: i32 = base
  n: u32 = len(rest)
  i: u32 = 0
  while i < n {
    acc = acc + rest[i]
    i = i + 1
  }
  acc
}

main: (): i32 = total(1, 2, 3, 4)
`)
	if abnormal || code != 10 {
		t.Fatalf("exit = (%d, abnormal=%v), want 10 (1+2+3+4 over the bundled view)", code, abnormal)
	}
}

func TestE2EDeclarationFormCallsAndAssertSuccess(t *testing.T) {
	code, abnormal := buildAndRun(t, "declform", `
addi32: (a, b: i32): i32 = a + b

scale: (base, factor: i32) -> i32 {
  assert(base < 1000)
  addi32(base * factor, 1)
}

main: (): i32 = scale(10, 5)
`)
	if abnormal || code != 51 {
		t.Fatalf("exit = (%d, abnormal=%v), want 51", code, abnormal)
	}
}

// The never-UB guarantee, live: an out-of-bounds index traps the process.
func TestE2EOutOfBoundsIndexTraps(t *testing.T) {
	_, abnormal := buildAndRun(t, "oob", `
pick: (buf: [4]u8, i: u32): u8 {
  v: []u8 = buf[0:4]
  v[i]
}

main: (): i32 {
  data: [4]u8
  i32(pick(data, 9))
}
`)
	if !abnormal {
		t.Fatal("out-of-bounds index must trap, not return normally")
	}
}

// A failed assertion traps in every build mode.
func TestE2EFailedAssertTraps(t *testing.T) {
	_, abnormal := buildAndRun(t, "assertfail", `
main: (): i32 {
  x: i32 = 5
  assert(x == 6)
  0
}
`)
	if !abnormal {
		t.Fatal("failed assert must trap, not return normally")
	}
}

// ADT construction and match, executed: tagged-union lowering with payload
// bindings guarded strictly by the tag.
func TestE2EADTConstructAndMatch(t *testing.T) {
	code, abnormal := buildAndRun(t, "adt", `
Shape: type =
  | Circle: i32
  | Square: i32
  | Empty

area2: (s: Shape): i32 = s ?
  | .Circle(r) -> r * 3
  | .Square(w) -> w * w
  | .Empty -> 0

main: (): i32 {
  c: Shape = .Circle(5)
  q: Shape = .Square(4)
  e: Shape = .Empty
  area2(c) + area2(q) + area2(e)
}
`)
	if abnormal || code != 31 {
		t.Fatalf("exit = (%d, abnormal=%v), want 31 (15 + 16 + 0)", code, abnormal)
	}
}

// Span writes, executed: fill an array through a writable span in a bounded
// loop, then read the elements back — and an out-of-bounds store traps.
func TestE2ESpanWritesRoundTrip(t *testing.T) {
	code, abnormal := buildAndRun(t, "spanwrite", `
fill: (s: [*]u8): i32 {
  n: u32 = len(s)
  i: u32 = 0
  while i < n {
    s[i] = u8(7)
    i = i + 1
  }
  i32(s[0]) + i32(s[1]) + i32(s[2]) + i32(s[3])
}

main: (): i32 {
  data: [4]u8
  s: [*]u8 = span(&data)
  fill(s) + 2
}
`)
	if abnormal || code != 30 {
		t.Fatalf("exit = (%d, abnormal=%v), want 30 (4*7 written through the span + 2)", code, abnormal)
	}
}

// The C boundary, executed: an extern binding to libc putchar writes real
// bytes to stdout through the c interface library (docs/spec/92-ffi.md).
func TestE2EExternPutchar(t *testing.T) {
	stdout, code, abnormal := buildAndRunOutput(t, "externputchar", `
putchar: (ch: c.Int): c.Int = c.extern("putchar")

main: (): i32 {
  putchar(c.Int(79))
  putchar(c.Int(75))
  putchar(c.Int(10))
  0
}
`)
	if abnormal || code != 0 {
		t.Fatalf("exit = (%d, abnormal=%v), want 0", code, abnormal)
	}
	if stdout != "OK\n" {
		t.Fatalf("stdout = %q, want %q (bytes through the extern boundary)", stdout, "OK\n")
	}
}

// The abstract assembly interface, executed on both lowerings: the default
// build takes the AArch64 instructions on this host, and the second build
// forces the portable C sequences (-DOAK_PORTABLE_INTRINSICS). Both must
// satisfy the Oak.Intrinsics laws on the same inputs — the differential
// witness of docs/spec/92-ffi.md section 3.3.
func TestE2EArm64Intrinsics(t *testing.T) {
	src := `
main: (): i32 {
  assert(arm64.clz64(u64(1)) == u64(63))
  assert(arm64.clz32(u32(0)) == u32(32))
  assert(arm64.clz64(u64(0)) == u64(64))
  assert(arm64.rev32(u32(287454020)) == u32(1144201745))
  v: u32 = u32(2864434397)
  assert(arm64.rev32(arm64.rev32(v)) == v)
  w: u64 = u64(81985529216486895)
  assert(arm64.rev64(arm64.rev64(w)) == w)
  assert(arm64.rbit32(u32(1)) == u32(2147483648))
  assert(arm64.rbit64(arm64.rbit64(u64(1234567890))) == u64(1234567890))
  assert(arm64.clz64(u64(255)) == u64(56))
  56
}
`
	for _, variant := range []struct {
		name  string
		flags []string
	}{
		{"instruction", nil},
		{"portable", []string{"-DOAK_PORTABLE_INTRINSICS"}},
	} {
		t.Run(variant.name, func(t *testing.T) {
			_, code, abnormal := buildAndRunOutput(t, "arm64"+variant.name, src, variant.flags...)
			if abnormal || code != 56 {
				t.Fatalf("exit = (%d, abnormal=%v), want 56 (clz64(255))", code, abnormal)
			}
		})
	}
}

// Portable SIMD, executed on both lowerings (NEON and the portable C
// sequences): the canonical byte-search kernel (eq + any), lane arithmetic,
// masks, vector stores through a span, and the arm64 horizontal
// instructions — all asserting the Oak.Simd laws on concrete values.
func TestE2ESimdKernels(t *testing.T) {
	src := `
main: (): i32 {
  zeros: [16]u8
  v: []u8 = view(&zeros)
  chunk: simd.U8x16 = simd.load_u8x16(v, u32(0))
  assert(simd.all_u8x16(simd.eq_u8x16(chunk, simd.splat_u8x16(u8(0)))))
  assert(simd.any_u8x16(simd.eq_u8x16(chunk, simd.splat_u8x16(u8(7)))) == false)

  a: simd.U8x16 = simd.splat_u8x16(u8(65))
  b: simd.U8x16 = simd.add_u8x16(a, simd.splat_u8x16(u8(1)))
  assert(arm64.uaddlv_u8x16(b) == u32(1056))
  assert(arm64.umaxv_u8x16(simd.max_u8x16(a, b)) == u8(66))
  assert(arm64.uminv_u8x16(simd.min_u8x16(a, b)) == u8(65))

  counted: simd.U8x16 = arm64.cnt_u8x16(simd.splat_u8x16(u8(255)))
  assert(arm64.uaddlv_u8x16(counted) == u32(128))

  wide: simd.U64x2 = simd.max_u64x2(simd.splat_u64x2(u64(5)), simd.splat_u64x2(u64(9)))
  assert(simd.all_u64x2(simd.eq_u64x2(wide, simd.splat_u64x2(u64(9)))))
  assert(simd.any_u32x4(simd.xor_u32x4(simd.splat_u32x4(u32(3)), simd.splat_u32x4(u32(3)))) == false)

  out: [16]u8
  s: [*]u8 = span(&out)
  simd.store_u8x16(s, u32(0), b)
  s[9] = u8(88)
  i32(s[0]) + i32(s[9])
}
`
	for _, variant := range []struct {
		name  string
		flags []string
	}{
		{"instruction", nil},
		{"portable", []string{"-DOAK_PORTABLE_INTRINSICS"}},
	} {
		t.Run(variant.name, func(t *testing.T) {
			_, code, abnormal := buildAndRunOutput(t, "simd"+variant.name, src, variant.flags...)
			if abnormal || code != 66+88 {
				t.Fatalf("exit = (%d, abnormal=%v), want %d (stored lanes read back)", code, abnormal, 66+88)
			}
		})
	}
}

// A vector load that would read past the view traps at runtime — the
// never-UB guarantee extends to SIMD (docs/spec/93-simd.md section 1.2).
func TestE2ESimdOutOfBoundsLoadTraps(t *testing.T) {
	_, abnormal := buildAndRun(t, "simdoob", `
main: (): i32 {
  data: [8]u8
  v: []u8 = view(&data)
  chunk: simd.U8x16 = simd.load_u8x16(v, u32(0))
  hit: Bool = simd.any_u8x16(chunk)
  assert(hit == false)
  0
}
`)
	if !abnormal {
		t.Fatal("16-lane load from an 8-element view must trap, not return normally")
	}
}

// Records, executed: struct construction, field access, nesting, and
// pass/return by value — with the proven natural layout
// (Oak.RecordLayoutRefinement) enforced by static assertions inside the
// generated C, so the exit code below only exists if the C compiler agreed
// with the proof about every offset and size.
func TestE2ERecordsEndToEnd(t *testing.T) {
	code, abnormal := buildAndRun(t, "records", `
Point: type = struct {
  x: i32
  y: i32
}

Rect: type = struct {
  a: Point
  b: Point
  tag: u8
}

shift: (p: Point, dx: i32): Point = Point { x: p.x + dx, y: p.y }

main: (): i32 {
  p: Point = Point { x: 11, y: 31 }
  q: Point = shift(p, 9)
  r: Rect = Rect { a: p, b: q, tag: u8(3) }
  assert(r.b.x == 20)
  r.a.x + r.b.y + i32(r.tag)
}
`)
	if abnormal || code != 45 {
		t.Fatalf("exit = (%d, abnormal=%v), want 45 (11 + 31 + 3 through nested records)", code, abnormal)
	}
}

// The colon-less definition form and '=' block bodies
// (docs/spec/10-syntax.md §3): add(l, r: u32): u32 = { body } is the same
// declaration, executed.
func TestE2EColonlessDefinitionForm(t *testing.T) {
	code, abnormal := buildAndRun(t, "colonless", `
add(l: i32, r: i32): i32 = {
  total: i32 = l + r
  total
}

twice(n: i32) -> i32 = n + n

main: (): i32 = add(twice(10), 2)
`)
	if abnormal || code != 22 {
		t.Fatalf("exit = (%d, abnormal=%v), want 22", code, abnormal)
	}
}

// Statement-position conditionals through the ? match sugar, short-circuit
// connectives, and record fields as Bool operands — the exact shapes the
// hypervisor evaluation found inexpressible. There are no if/else
// keywords: a Bool condition is a two-arm match (docs/spec/10-syntax.md
// §3a). ackHighest-style kernel scan, executed.
func TestE2EIfStatementsAndLogicalOperators(t *testing.T) {
	code, abnormal := buildAndRun(t, "ifops", `
Flags: type = struct {
  pending: Bool
  masked: Bool
}

deliverable: (f: Flags): Bool = f.pending && !f.masked

pick_highest: (v: [*]u8): i32 {
  best: i32 = 0 - 1
  bestPriority: u8 = u8(255)
  n: u32 = len(v)
  i: u32 = 0
  while i < n {
    v[i] < bestPriority ? {
      best = i32_bits_u32(i)
      bestPriority = v[i]
    }
    i = i + 1
  }
  best
}

classify: (n: i32): i32 {
  result: i32 = 1
  n < 0 ? {
    result = 0 - 1
  } | {
    n == 0 ? {
      result = 0
    }
  }
  result
}

main: (): i32 {
  hot: Flags = Flags { pending: true, masked: false }
  cold: Flags = Flags { pending: true, masked: true }
  assert(deliverable(hot))
  assert(!deliverable(cold))
  assert(deliverable(hot) || deliverable(cold))
  assert(!(deliverable(cold) && deliverable(hot)))

  prio: [4]u8
  s: [*]u8 = span(&prio)
  s[0] = u8(9)
  s[1] = u8(3)
  s[2] = u8(7)
  s[3] = u8(3)
  found: i32 = pick_highest(s)
  assert(found == 1)

  classify(0 - 5) + classify(0) + classify(40) + found + 41
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (-1 + 0 + 1 + 1 + 41)", code, abnormal)
	}
}

// Explicit integer conversions, executed: same-width cross-sign bits
// reinterpretation round-trips, truncation wraps mod 2^N, saturation
// clamps — total semantics, no implementation-defined C.
func TestE2EIntegerConversions(t *testing.T) {
	code, abnormal := buildAndRun(t, "conversions", `
main: (): i32 {
  negOne: i32 = i32_bits_u32(u32(4294967295))
  assert(negOne == 0 - 1)
  assert(u32_bits_i32(negOne) == u32(4294967295))
  assert(i32_bits_u32(u32_bits_i32(0 - 12345)) == 0 - 12345)

  assert(u8_trunc_u32(u32(300)) == u8(44))
  assert(i8_trunc_i32(0 - 300) == i8(0 - 44))

  assert(u8_saturating_u32(u32(300)) == u8(255))
  assert(u8_saturating_u32(u32(200)) == u8(200))
  assert(i8_saturating_i32(300) == i8(127))
  assert(u8_bits_i8(i8_saturating_i32(0 - 300)) == u8(128))

  i32(u8_trunc_u32(u32(299)))
}
`)
	if abnormal || code != 43 {
		t.Fatalf("exit = (%d, abnormal=%v), want 43 (299 mod 256)", code, abnormal)
	}
}

func TestE2EOutOfBoundsStoreTraps(t *testing.T) {
	_, abnormal := buildAndRun(t, "oobstore", `
main: (): i32 {
  data: [4]u8
  s: [*]u8 = span(&data)
  s[9] = u8(1)
  0
}
`)
	if !abnormal {
		t.Fatal("out-of-bounds store must trap, not return normally")
	}
}
