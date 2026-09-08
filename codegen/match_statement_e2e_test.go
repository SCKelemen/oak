package codegen_test

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/compiler"
)

// Exercise the real frontend and native C execution. In particular, nested
// matches must not re-evaluate a condition after an arm mutates its inputs.
func TestStatementMatchSelectsOneArm(t *testing.T) {
	cases := []struct{ name, source string }{
		{"nested_mutable_bool", `
main: (): i32 {
  phase: u32 = 0
  outer: Bool = true
  outer ? {
    phase == u32(0) ? { phase = u32(1) }
    | { phase = u32(99) }
  }
  assert(phase == u32(1))
  42
}`},
		{"nested_false_condition_called_once", `
probe: (calls: [*]u32): Bool {
  calls[0] = calls[0] + u32(1)
  false
}
main: (): i32 {
  calls: [1]u32
  calls[0] = u32(0)
  selected: u32 = 0
  outer: Bool = true
  outer ? {
    probe(span(&calls)) ? { selected = u32(99) }
    | { selected = u32(7) }
  }
  assert(calls[0] == u32(1))
  assert(selected == u32(7))
  42
}`},
		{"nested_bounds_guard", `
main: (): i32 {
  bytes: [1]u8
  bytes[0] = u8(10)
  pos: u32 = 0
  pos < u32(1) ? {
    bytes[pos] == u8(10) ? { pos = pos + u32(1) }
    | { pos = u32(99) }
  }
  assert(pos == u32(1))
  42
}`},
		{"scalar_mutation_and_fallback", `
main: (): i32 {
  value: u32 = 1
  selected: u32 = 0
  value ?
    | 1 => { value = u32(2); selected = u32(7) }
    | 2 => { selected = u32(98) }
    | _ => { selected = u32(99) }
  assert(value == u32(2))
  assert(selected == u32(7))
  42
}`},
		{"adt_mutation", `
State: type = First | Second
main: (): i32 {
  state: State = .First
  selected: u32 = 0
  state ?
    | .First => { state = .Second; selected = u32(7) }
    | .Second => { selected = u32(99) }
  assert(selected == u32(7))
  42
}`},
		{"adt_payload_and_fallback", `
State: type = First: u32 | Second
main: (): i32 {
  state: State = .First(u32(7))
  selected: u32 = 0
  state ?
    | .First(value) => { state = .Second; selected = value }
    | _ => { selected = u32(99) }
  assert(selected == u32(7))
  42
}`},
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for match execution regressions")
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			generated, err := compiler.New().WithSource("statement_match.oak", test.source).EmitC().Get()
			if err != nil {
				t.Fatalf("Oak compilation: %v", err)
			}
			if strings.Contains(generated, "OAK_UNSUPPORTED") {
				t.Fatalf("unsupported C lowering:\n%s", generated)
			}
			dir := t.TempDir()
			input, binary := filepath.Join(dir, "match.c"), filepath.Join(dir, "match")
			if err := os.WriteFile(input, []byte(generated), 0o600); err != nil {
				t.Fatal(err)
			}
			ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
			defer cancel()
			if output, err := exec.CommandContext(ctx, cc, "-std=c99", "-O2", input, "-o", binary).CombinedOutput(); err != nil {
				t.Fatalf("C compilation: %v\n%s\n%s", err, output, generated)
			}
			output, err := exec.CommandContext(ctx, binary).CombinedOutput()
			exit, ok := err.(*exec.ExitError)
			if ctx.Err() != nil || !ok || exit.ExitCode() != 42 {
				t.Fatalf("native execution: want exit 42, got %v (%v)\n%s\n%s", err, ctx.Err(), output, generated)
			}
		})
	}
}
