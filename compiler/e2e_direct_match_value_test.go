package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"syscall"
	"testing"
	"time"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

const directMatchPrelude = `Pick: type = First | Second
Choice: type = Some: u32 | None
Pair: type = struct { x: u32, y: u32 }
Row: type = struct { cells: [2]u32 }
next: (s: [*]u32): u32 {
  s[0] = s[0] + u32(1)
  s[0]
}
probe: (s: [*]u32): Choice = Choice.Some(next(s))
borrow_rows[R]: (rows: Span[Row, R], calls: [*]u32): Span[Row, R] {
  calls[0] = calls[0] + u32(1)
  rows
}
inc: (x: i32): i32 = x + 1
dec: (x: i32): i32 = x - 1
escape: (p: Pick): u32 {
  p ? | .First => { return u32(42) } | .Second => {}
  u32(99)
}
`

// These operands stay direct matches: naming their results in Oak would bypass
// the unsupported C expression path that originally broke assert(reader(...)).
// Every fixture is checked and interpreted, then the same source is emitted as
// portable C, compiled once and executed. A missing C compiler is a failure.
func TestE2EDirectADTMatchValues(t *testing.T) {
	cases := []struct{ name, body string }{
		{"direct_assert_payload", `value: Choice = .Some(u32(7))
assert(value ? | .Some(n) => n == u32(7) | .None => false)`},
		{"direct_assert_no_payload", `assert(p ? | .First => true | .Second => false)
q: Pick = .Second
assert(q ? | .First => false | .Second => true)`},
		{"subject_once", `assert(probe(span(&s)) ? | .Some(n) => n == u32(1) | .None => false)
assert(s[0] == u32(1))`},
		{"left_to_right_siblings", `assert(next(span(&s)) * u32(100) + (probe(span(&s)) ? | .Some(n) => n * u32(10) | .None => u32(0)) + next(span(&s)) == u32(123))
assert(s[0] == u32(3))`},
		{"read_before_match_write", `assert(s[0] * u32(10) + (probe(span(&s)) ? | .Some(n) => n | .None => u32(0)) == u32(1))`},
		{"branch_scope_and_mutation", `value: Choice = .Some(u32(7))
n: u32 = 80
assert(value ? | .Some(n) => { value = .None; n == u32(7) } | .None => false)
assert(n == u32(80))
assert(value ? | .Some(_) => false | .None => true)`},
		{"nested_subject", `assert((p ? | .First => Choice.Some(u32(42)) | .Second => Choice.None) ? | .Some(n) => n == u32(42) | .None => false)`},
		{"nested_selected_arm", `assert(p ? | .First => { probe(span(&s)) ? | .Some(n) => n == u32(1) | .None => false } | .Second => { next(span(&s)); false })
assert(s[0] == u32(1))`},
		{"short_circuit_skips", `assert((false && (probe(span(&s)) ? | .Some(_) => true | .None => false)) == false)
assert(true || (probe(span(&s)) ? | .Some(_) => true | .None => false))
assert(s[0] == u32(0))`},
		{"short_circuit_enters", `assert(s[0] == u32(0) && (probe(span(&s)) ? | .Some(n) => n == u32(1) | .None => false))
assert(s[0] == u32(0) || (probe(span(&s)) ? | .Some(n) => n == u32(2) | .None => false))
assert(s[0] == u32(2))`},
		{"while_rechecks", `while (probe(span(&s)) ? | .Some(n) => n < u32(3) | .None => false) {
  _ = 0
}
assert(s[0] == u32(3))`},
		{"wildcard_only_subject", `assert((probe(span(&s)) ? | _ => u32(42)) == u32(42))
assert(s[0] == u32(1))`},
		{"whole_subject_binding", `assert(p ? | whole => { p = .Second; whole ? | .First => true | .Second => false })
assert(p ? | .First => false | .Second => true)`},
		{"callable_result", `assert((p ? | .First => inc | .Second => dec)(41) == 42)`},
		{"record_result", `assert((p ? | .First => Pair { x: u32(40), y: u32(2) } | .Second => Pair { x: u32(99), y: u32(0) }).x == u32(40))`},
		{"array_result", `assert((p ? | .First => [2]u32{ 40, 2 } | .Second => [2]u32{ 99, 99 })[1] == u32(2))`},
		{"record_and_array_operands", `v: Pair = Pair { x: next(span(&s)), y: (probe(span(&s)) ? | .Some(n) => n | .None => u32(0)) }
a: [2]u32 = [2]u32{ next(span(&s)), (probe(span(&s)) ? | .Some(n) => n | .None => u32(0)) }
assert(v.x == u32(1) && v.y == u32(2) && a[0] == u32(3) && a[1] == u32(4))`},
		{"constructor_payload", `v: Choice = .Some(p ? | .First => u32(42) | .Second => u32(99))
assert(v ? | .Some(n) => n == u32(42) | .None => false)`},
		{"index_and_slice_operands", `a: [3]u32 = [3]u32{ 10, 20, 30 }
assert(a[p ? | .First => u32(1) | .Second => u32(0)] == u32(20))
v: []u32 = view(&a)
w: []u32 = v[(p ? | .First => u32(1) | .Second => u32(0)):(p ? | .First => u32(3) | .Second => u32(2))]
assert(len(w) == u32(2) && w[0] == u32(20))`},
		{"nested_store_address_order", `rows: [2]Row
phase: u32 = 0
rows[p ? | .First => { phase = phase * u32(10) + u32(1); u32(0) } | .Second => u32(1)].cells[p ? | .First => { phase = phase * u32(10) + u32(2); u32(0) } | .Second => u32(1)] = p ? | .First => { phase = phase * u32(10) + u32(3); u32(42) } | .Second => u32(99)
assert(phase == u32(123))
assert(rows[0].cells[0] == u32(42) && rows[1].cells[0] == u32(0))`},
		{"field_store_address_order", `rows: [2]Pair
rows[(probe(span(&s)) ? | .Some(n) => n - u32(1) | .None => u32(1))].x = probe(span(&s)) ? | .Some(n) => n | .None => u32(99)
assert(s[0] == u32(2) && rows[0].x == u32(2) && rows[1].x == u32(0))`},
		{"span_base_evaluates_once", `rows: [1]Row
borrow_rows(span(&rows), span(&s))[0].cells[0] = u32(42)
assert(s[0] == u32(1) && rows[0].cells[0] == u32(42))
assert(p ? | .First => true | .Second => false)`},
		{"match_span_destination", `left: [1]u32
right: [1]u32;
(probe(span(&s)) ? | .Some(_) => span(&left) | .None => span(&right))[0] = u32(42)
q: Choice = .None;
(q ? | .Some(_) => span(&left) | .None => span(&right))[0] = u32(7)
assert(s[0] == u32(1) && left[0] == u32(42) && right[0] == u32(7))`},
		{"ordinary_assignment", `answer: u32 = 0
answer = u32(1) + (p ? | .First => u32(41) | .Second => u32(99))
assert(answer == u32(42))`},
		{"break_exits_surrounding_loop", `after: u32 = 0
i: u32 = 0
while i < u32(1) {
  ignored: u32 = p ? | .First => { break; u32(0) } | .Second => u32(7)
  after = u32(99)
  i = i + u32(1)
}
assert(after == u32(0))
assert(p ? | .First => true | .Second => false)`},
		{"return_exits_function", `assert(escape(p) == u32(42))
assert(p ? | .First => true | .Second => false)`},
		{"reserved_names", `oak_seq: u32 = 1
default: Choice = .Some(u32(41))
assert(default ? | .Some(oak_assert) => oak_assert + oak_seq == u32(42) | .None => false)`},
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for direct ADT match execution regressions")
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			source := directMatchPrelude + "main: (): i32 {\n  p: Pick = .First\n  s: [1]u32\n" + test.body + "\n  42\n}\n"
			if got := interpretChecked(t, source); got != 42 {
				t.Fatalf("interpreter returned %d, want 42", got)
			}
			generated, err := New().WithSource("direct_match.oak", source).EmitC().Get()
			if err != nil {
				t.Fatalf("Oak compilation: %v", err)
			}
			for _, forbidden := range []string{"/* match expression */", "__typeof__", "OAK_UNSUPPORTED", "({"} {
				if strings.Contains(generated, forbidden) {
					t.Fatalf("generated C contains unsupported expression form %q", forbidden)
				}
			}
			if !strings.Contains(generated, "oak__seq_") {
				t.Fatal("direct fixture did not exercise value sequencing")
			}
			if test.name == "span_base_evaluates_once" && strings.Count(generated, "= oak_borrow_rows(") != 1 {
				t.Fatal("effectful span base must survive inlining and be captured exactly once")
			}
			_, err = runDirectMatchC(t, cc, generated)
			status, ok := err.(*exec.ExitError)
			if !ok || status.ExitCode() != 42 {
				t.Fatalf("compiled program: %v, want exit 42", err)
			}
		})
	}
}

func TestDirectADTMatchFrontendRejections(t *testing.T) {
	for _, test := range []struct{ name, body string }{
		{"non_exhaustive", `assert(p ? | .First => true)`},
		{"wrong_variant", `assert(p ? | .Missing => true | _ => false)`},
		{"inconsistent_result", `assert(p ? | .First => true | .Second => u32(1))`},
	} {
		t.Run(test.name, func(t *testing.T) {
			source := "Pick: type = First | Second\nmain: (): i32 { p: Pick = .First; " + test.body + "; 42 }\n"
			if _, err := New().WithSource("invalid_match.oak", source).Check().Get(); err == nil {
				t.Fatal("invalid match unexpectedly passed the public checker")
			}
		})
	}
}

// Bound diagnostics independently of an outer test runner's log policy.
type directMatchOutput struct {
	bytes    []byte
	overflow bool
}

func (out *directMatchOutput) Write(p []byte) (int, error) {
	n := len(p)
	left := 64*1024 - len(out.bytes)
	if len(p) > left {
		p = p[:left]
		out.overflow = true
	}
	out.bytes = append(out.bytes, p...)
	return n, nil
}
func runDirectMatchC(t *testing.T, cc, generated string) (string, error) {
	t.Helper()
	if len(generated) > 8*1024*1024 {
		t.Fatal("generated C exceeds the fixture cap")
	}
	dir := t.TempDir()
	input, binary := filepath.Join(dir, "match.c"), filepath.Join(dir, "match")
	if err := os.WriteFile(input, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
	defer cancel()
	var compileOutput directMatchOutput
	compile := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-ffp-contract=off", input, "-lm", "-o", binary)
	compile.Stdout, compile.Stderr = &compileOutput, &compileOutput
	if err := compile.Run(); err != nil || compileOutput.overflow {
		t.Fatalf("cc: %v, output overflow=%v\n%s", err, compileOutput.overflow, compileOutput.bytes)
	}
	info, err := os.Stat(binary)
	if err != nil || info.Size() > 8*1024*1024 {
		t.Fatalf("generated binary exceeds fixture cap or is absent: %v", err)
	}
	var output directMatchOutput
	command := exec.CommandContext(ctx, binary)
	command.Dir = dir
	command.Stdout, command.Stderr = &output, &output
	err = command.Run()
	if ctx.Err() != nil || output.overflow {
		t.Fatalf("program deadline/output bound: %v overflow=%v", ctx.Err(), output.overflow)
	}
	return string(output.bytes), err
}

// Target.Left is evaluated before the RHS; the final store's bounds check is
// after its value. A selected RHS assertion identifies which boundary ran.
const directMatchTrapControl = "int main(void) { __builtin_trap(); }\n"

func requireDirectMatchTrap(t *testing.T, err error) {
	t.Helper()
	exit, ok := err.(*exec.ExitError)
	if !ok {
		t.Fatalf("expected SIGILL, got %v", err)
	}
	status, ok := exit.Sys().(syscall.WaitStatus)
	if !ok || !status.Signaled() || status.Signal() != syscall.SIGILL {
		t.Fatalf("expected SIGILL from __builtin_trap, got %v (status %v)", err, exit.Sys())
	}
}

func TestE2EDirectADTMatchAssignmentTraps(t *testing.T) {
	if runtime.GOOS != "linux" || runtime.GOARCH != "amd64" {
		t.Skip("trap-signal contract is scoped to Linux/amd64; positive value cases remain portable")
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for assignment trap ordering")
	}
	// Establish the expected signal using the same actual compiler, flags,
	// bounded helper and host as the two Oak-generated trap fixtures.
	controlOutput, controlErr := runDirectMatchC(t, cc, directMatchTrapControl)
	requireDirectMatchTrap(t, controlErr)
	if controlOutput != "" {
		t.Fatalf("unexpected trap control output: %s", controlOutput)
	}
	for _, test := range []struct {
		name, target string
		rhsRuns      bool
	}{
		{"intermediate_index", "rows[i].cells[0]", false},
		{"final_index", "rows[0].cells[i]", true},
	} {
		t.Run(test.name, func(t *testing.T) {
			source := `Pick: type = First | Second
Row: type = struct { cells: [2]u32 }
direct_match_store_probe: (rows: [*]Row, i: u32, p: Pick): () {
  ` + test.target + ` = p ? | .First => { assert(false); u32(42) } | .Second => u32(99)
}
main: (): i32 { rows: [1]Row; direct_match_store_probe(span(&rows), u32(3), Pick.First); 42 }
`
			model, err := New().WithSource("assignment_trap.oak", source).Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			env := object.NewEnvironment()
			env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
			if result := evaluator.Eval(model.Tree.Root, env); result != nil {
				if failure, ok := result.(*object.Error); ok {
					t.Fatalf("interpreter setup: %s", failure.Message)
				}
			}
			call := parser.New(layout.New(scanner.New("main()")))
			result := evaluator.Eval(call.ParseProgram(), env)
			failure, ok := result.(*object.Error)
			if !ok {
				t.Fatalf("interpreter must reject the access, got %T", result)
			}
			if strings.Contains(failure.Message, "assertion failed") != test.rhsRuns {
				t.Fatalf("interpreter RHS executed=%v, want %v: %s", strings.Contains(failure.Message, "assertion failed"), test.rhsRuns, failure.Message)
			}
			generated, err := New().WithSource("assignment_trap.oak", source).EmitC().Get()
			if err != nil {
				t.Fatal(err)
			}
			output, err := runDirectMatchC(t, cc, generated)
			requireDirectMatchTrap(t, err)
			if !test.rhsRuns && output != "" {
				t.Fatalf("unexpected intermediate bounds-trap output: %s", output)
			}
			if strings.Contains(output, "assertion failed") != test.rhsRuns {
				t.Fatalf("RHS executed=%v, want %v: %s", strings.Contains(output, "assertion failed"), test.rhsRuns, output)
			}
		})
	}
}
