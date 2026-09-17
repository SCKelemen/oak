package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func runAggregateGeneratedC(t *testing.T, name, output string) (exitCode int, abnormal bool) {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}

	dir := t.TempDir()
	cPath := filepath.Join(dir, name+".c")
	binPath := filepath.Join(dir, name)
	if err := os.WriteFile(cPath, []byte(output), 0o644); err != nil {
		t.Fatal(err)
	}
	compile := exec.Command(cc, "-std=c99", "-O1", "-ffp-contract=off", "-o", binPath, cPath, "-lm")
	if combined, err := compile.CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s\n--- generated C ---\n%s", err, combined, output)
	}

	ctx, cancel := context.WithTimeout(context.Background(), runDeadline)
	defer cancel()
	run := exec.CommandContext(ctx, binPath)
	err = run.Run()
	if ctx.Err() == context.DeadlineExceeded {
		t.Fatalf("compiled program %s did not finish within %s (killed)", name, runDeadline)
	}
	if err == nil {
		return 0, false
	}
	if exitErr, ok := err.(*exec.ExitError); ok {
		if exitErr.ExitCode() >= 0 {
			return exitErr.ExitCode(), false
		}
		return -1, true
	}
	t.Fatalf("run failed: %v", err)
	return -1, true
}

// Indexes inside aggregate literals are still ordinary bounds-checked value
// expressions. In particular a span cannot reach the C emitter as the invalid
// raw expression `span[index]` merely because the value is an array element.
func TestE2EAggregateLiteralIndexesLowerRecursively(t *testing.T) {
	source := `
Inner: type = struct { values: [2]u32 }
Box: type = struct {
  from_span: [2]u32
  from_view: [2]u32
  nested: Inner
}
next: (counter: [*]u32): u32 {
  counter[0] = counter[0] + u32(1)
  counter[0]
}
gather: (mutable: [*]u32, readonly: []u32, i: u32): Box {
  Box {
    from_span: [2]u32{ mutable[i], mutable[i + u32(1)] },
    from_view: [2]u32{ readonly[i], readonly[i + u32(1)] },
    nested: Inner { values: [2]u32{ mutable[i], readonly[i + u32(1)] } }
  }
}
main: (): i32 {
  mutable: [2]u32 = [2]u32{ 1, 2 }
  readonly: [2]u32 = [2]u32{ 8, 12 }
  counter: [1]u32
  box: Box = gather(span(&mutable), view(&readonly), u32(0))
  ordered: [2]u32 = [2]u32{
    mutable[next(span(&counter)) - u32(1)],
    readonly[next(span(&counter)) - u32(1)]
  }
  ok: Bool = box.from_span[0] == u32(1) && box.from_span[1] == u32(2)
  ok = ok && box.from_view[0] == u32(8) && box.from_view[1] == u32(12)
  ok = ok && box.nested.values[0] == u32(1) && box.nested.values[1] == u32(12)
  ok = ok && ordered[0] == u32(1) && ordered[1] == u32(12)
  ok = ok && counter[0] == u32(2)
  ok ? { 42 } | { 1 }
}
`
	output, err := New().WithSource("aggregate_index.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"oak_span_index_u32(", "oak_view_index_u32("} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks checked aggregate access %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "OAK_UNSUPPORTED") {
		t.Fatalf("aggregate access fell through C lowering:\n%s", output)
	}
	if code, abnormal := runAggregateGeneratedC(t, "aggregate_index", output); abnormal || code != 42 {
		t.Fatalf("C backend: exit=(%d, abnormal=%v), want 42\n%s", code, abnormal, output)
	}
	const fixedIndex = "#define oak_index(base, len, i) ((base)[oak_lv_idx((u64)(i), (u64)(len))])"
	const duplicatedIndex = "#define oak_index(base, len, i) ((u64)(i) < (u64)(len) ? (base)[(i)] : (base)[oak_bounds_trap()])"
	mutated := strings.Replace(output, fixedIndex, duplicatedIndex, 1)
	if mutated == output {
		t.Fatalf("generated C lacks the single-evaluation owned-array index macro:\n%s", output)
	}
	if code, abnormal := runAggregateGeneratedC(t, "aggregate_index_duplicated", mutated); !abnormal {
		t.Fatalf("duplicated-index mutant did not trap: exit=%d", code)
	}
	if got := interpretChecked(t, source); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
}

func aggregateIndexInterpreterTraps(t *testing.T, source string) {
	t.Helper()
	model, err := New().WithSource("aggregate_oob.oak", source).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if result := evaluator.Eval(model.Tree.Root, env); isEvalError(result) {
		t.Fatalf("defining the program failed: %s", result.Inspect())
	}
	call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
	if result := evaluator.Eval(call, env); !isEvalError(result) {
		t.Fatalf("interpreter returned %v, want dynamic bounds error", result)
	}
}

func TestE2EAggregateLiteralDynamicIndexTraps(t *testing.T) {
	for _, test := range []struct {
		name      string
		parameter string
		argument  string
	}{
		{name: "span", parameter: "[*]u32", argument: "span(&values)"},
		{name: "view", parameter: "[]u32", argument: "view(&values)"},
	} {
		t.Run(test.name, func(t *testing.T) {
			source := `
read: (values: ` + test.parameter + `, i: u32): [1]u32 {
  [1]u32{ values[i] }
}
main: (): i32 {
  values: [1]u32 = [1]u32{ 42 }
  index: u32 = u32(1)
  result: [1]u32 = read(` + test.argument + `, index)
  i32_bits_u32(result[0])
}
`
			if code, abnormal := buildAndRun(t, "aggregate_oob_"+test.name, source); !abnormal {
				t.Fatalf("C backend did not trap: exit=%d", code)
			}
			aggregateIndexInterpreterTraps(t, source)
		})
	}
}
