package compiler

import (
	"bytes"
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// buildAndRunStderr compiles one source through cc and runs it, returning
// the binary's stderr and whether it trapped: the channel a failed
// assertion reports on (docs/spec/85-discipline.md section 5).
func buildAndRunStderr(t *testing.T, name, src string) (stderr string, trapped bool, exitCode int) {
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
	if combined, err := exec.Command(cc, "-std=c99", "-O1", "-o", binPath, cPath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s", err, combined)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	run := exec.CommandContext(ctx, binPath)
	var captured bytes.Buffer
	run.Stderr = &captured
	err = run.Run()
	if err == nil {
		return captured.String(), false, 0
	}
	if exitErr, ok := err.(*exec.ExitError); ok {
		if exitErr.ExitCode() >= 0 {
			return captured.String(), false, exitErr.ExitCode()
		}
		return captured.String(), true, -1
	}
	t.Fatalf("failed to run binary: %v", err)
	return "", false, 0
}

// E3: a failed assert_eq names both values and its source position; a
// passing one is silent.
func TestE2EAssertEqNamesBothValues(t *testing.T) {
	cases := []struct{ name, body, want string }{
		{"u32", `assert_eq(u32(2) + u32(3), u32(4))`, "got 5, want 4"},
		{"i64", `assert_eq(i64(0) - i64(3), i64(4))`, "got -3, want 4"},
		{"bool", `assert_eq(u32(1) < u32(2), false)`, "got true, want false"},
		{"f64", `assert_eq(0.1 + 0.2, 0.3)`, "got 0.30000000000000004, want 0.29999999999999999"},
		{"ne", `assert_ne(u8(7), u8(7))`, "got 7, want anything but 7"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			src := "main: (): i32 {\n  " + c.body + "\n  42\n}\n"
			stderr, trapped, _ := buildAndRunStderr(t, "assert_values_"+c.name, src)
			if !trapped {
				t.Fatalf("expected the assertion to trap; stderr:\n%s", stderr)
			}
			if !strings.Contains(stderr, "oak: assertion failed at assert_values_"+c.name+".oak:2: "+c.want) {
				t.Fatalf("unexpected message:\n%s", stderr)
			}
		})
	}
}

func TestE2EAssertEqPassesSilently(t *testing.T) {
	stderr, trapped, code := buildAndRunStderr(t, "assert_values_pass", `
main: (): i32 {
  assert_eq(u32(2) + u32(3), u32(5))
  assert_ne(i16(1), i16(2))
  assert_eq(true, u8(1) == u8(1))
  assert_eq(f32(1.5) * f32(2.0), f32(3.0))
  42
}
`)
	if trapped || code != 42 || stderr != "" {
		t.Fatalf("exit=%d trapped=%v stderr=%q", code, trapped, stderr)
	}
}

// Operands must share one comparable type; the checker names the mismatch
// with OAK-T0601 instead of letting the C compiler promote silently.
func TestE2EAssertEqRejectsMismatchedOperands(t *testing.T) {
	for _, src := range []string{
		"main: (): i32 {\n  assert_eq(u32(1), u64(1))\n  0\n}\n",
		"main: (): i32 {\n  assert_eq(u32(1), 1.0)\n  0\n}\n",
		"main: (): i32 {\n  x: [2]u8\n  assert_eq(view(&x), view(&x))\n  0\n}\n",
		"main: (): i32 {\n  assert_ne(u32(1))\n  0\n}\n",
	} {
		_, err := New().WithSource("assert_values_reject.oak", src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), "OAK-T0601") {
			t.Fatalf("expected OAK-T0601 for\n%s\ngot: %v", src, err)
		}
	}
}
