package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

// End-to-end execution: the full real pipeline — Oak source through
// Compilation.EmitC, compiled and linked by the system C compiler, executed
// as a native binary, with behavior asserted via exit status. Trap paths
// (bounds violations, failed assertions) must terminate abnormally: the
// never-UB guarantee, verified in running machine code.

func buildAndRun(t *testing.T, name, src string) (exitCode int, abnormal bool) {
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
	compile := exec.Command(cc, "-std=c99", "-O1", "-o", binPath, cPath)
	if combined, err := compile.CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s\n--- generated C ---\n%s", err, combined, output)
	}

	run := exec.Command(binPath)
	err = run.Run()
	if err == nil {
		return 0, false
	}
	if exitErr, ok := err.(*exec.ExitError); ok {
		if exitErr.ExitCode() >= 0 {
			return exitErr.ExitCode(), false
		}
		return -1, true // killed by a signal: the trap fired
	}
	t.Fatalf("failed to run binary: %v", err)
	return 0, false
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
