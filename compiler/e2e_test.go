package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

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
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}

	output, err := New().WithSource(name+".oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}

	dir := t.TempDir()
	cPath := filepath.Join(dir, name+".c")
	binPath := filepath.Join(dir, name)
	if err := os.WriteFile(cPath, []byte(output), 0o644); err != nil {
		t.Fatal(err)
	}
	args := append([]string{"-std=c99", "-O1"}, ccFlags...)
	args = append(args, "-o", binPath, cPath)
	compile := exec.Command(cc, args...)
	if combined, err := compile.CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s\n--- generated C ---\n%s", err, combined, output)
	}

	run := exec.Command(binPath)
	var captured strings.Builder
	run.Stdout = &captured
	err = run.Run()
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
