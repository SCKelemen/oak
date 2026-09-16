package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/codegen/lean"
)

const leanFunctionArgumentsProgram = `
hits: u32 = 0
inc: (x: u32): u32 { hits = hits + 1; x + 1 }
twice: (x: u32): u32 = x * 2
apply: (x: u32, f: (u32) -> u32 effects { }): u32 = f(x)
relay: (x: u32, f: (u32) -> u32 effects { }): u32 = apply(x, f)
compose: (x: u32, f: (u32) -> u32 effects { }, g: (u32) -> u32 effects { }): u32 = g(f(x))
recur: (n: u32, x: u32, f: (u32) -> u32 effects { }): u32 = n == 0 ? x | recur(n - 1, f(x), f)
writer: (dst: [*]u32, by: u32): () { dst[0] = dst[0] + by }
mutate: (dst: [*]u32, f: ([*]u32, u32) -> () effects { }): () { f(dst, 3) }
drive: (): u32 {
  buf: [1]u32
  i: u32 = 0
  while i < 2 {
    buf[0] = buf[0] + relay(i, inc)
    mutate(span(&buf), writer)
    i = i + 1
  }
  a: u32 = compose(3, inc, twice)
  b: u32 = compose(3, twice, inc)
  r: u32 = recur(3, 0, inc)
  buf[0] + a + b + r + hits
}
main: (): i32 = drive() == 34 ? 42 | 1
`

// F28: the same body instantiated at distinct named callbacks must carry
// the correct callback's state. Forwarding, recursion, two function slots,
// and a writer callback inside a loop exercise the specialization graph.
func TestE2ELeanFunctionArguments(t *testing.T) {
	if code, abnormal := buildAndRun(t, "function_arguments", leanFunctionArgumentsProgram); abnormal || code != 42 {
		t.Fatalf("C exit=(%d,%v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, leanFunctionArgumentsProgram); got != 42 {
		t.Fatalf("interpreter result=%d, want 42", got)
	}
	comp := New().WithSource("function_arguments.oak", leanFunctionArgumentsProgram)
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	before := model.Tree.Root.String()
	extracted, err := lean.Emit(model.Tree.Root, model.TypeChecker, "Oak.FunctionArguments", map[string]bool{"drive": true})
	if err != nil {
		t.Fatal(err)
	}
	// The same checked tree remains available to other backends and to
	// another extraction; specialization is local to the emitter.
	if model.Tree.Root.String() != before {
		t.Fatal("extraction rewrote the checked program")
	}
	again, err := lean.Emit(model.Tree.Root, model.TypeChecker, "Oak.FunctionArguments", map[string]bool{"drive": true})
	if err != nil || again != extracted {
		t.Fatalf("repeated extraction changed: %v", err)
	}
	t.Run("Lean", func(t *testing.T) {
		checkFunctionArgumentLean(t, extracted+`
open Oak.FunctionArguments
example : drive hits_init 20 = some (34, 7) := by decide
example : drive hits_init 0 = none := by decide
`, false)
	})
}

func TestE2ELeanFunctionArgumentsFailClosed(t *testing.T) {
	for _, tt := range []struct{ name, body, root, want string }{
		{"dynamic", `apply: (x: u32, f: (u32) -> u32): u32 = f(x)
drive: (flag: Bool): u32 = apply(3, flag ? inc | twice)`, "drive", "must be a named Oak function"},
		{"unbound_root", `apply: (x: u32, f: (u32) -> u32 effects { }): u32 = f(x)`, "apply", "must be bound by a call"},
		{"reassigned", `apply: (x: u32, f: (u32) -> u32 effects { }): u32 { f = twice; f(x) }
drive: (): u32 = apply(3, inc)`, "drive", "reassigning function parameter"},
	} {
		t.Run(tt.name, func(t *testing.T) {
			source := `inc: (x: u32): u32 = x + 1
twice: (x: u32): u32 = x * 2
` + tt.body + "\nmain: (): i32 = 0\n"
			comp := New().WithSource("function_arguments.oak", source)
			if _, err := comp.Check().Get(); err != nil {
				t.Fatalf("fixture must be valid Oak: %v", err)
			}
			if _, err := comp.EmitLeanRoots("Oak.FunctionArguments", []string{tt.root}).Get(); err == nil || !strings.Contains(err.Error(), tt.want) {
				t.Fatalf("want extraction error containing %q, got %v", tt.want, err)
			}
		})
	}
}

func TestE2ELeanFunctionArgumentLocalLibraryName(t *testing.T) {
	source := `package main
import(std)
identity: (x: u8): u8 = x
apply: (x: u8, f: (u8) -> u8 effects { }): u8 = f(x)
drive: (): u8 {
  ascii_lower: (u8) -> u8 effects { } = identity
  apply(u8(65), ascii_lower)
}
main: (): i32 = 0
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": source})
	comp := New().WithPackageDir(root)
	if _, err := comp.Check().Get(); err != nil {
		t.Fatalf("fixture must be valid Oak: %v", err)
	}
	if _, err := comp.EmitLeanRoots("Oak.LocalCallback", []string{"drive"}).Get(); err == nil || !strings.Contains(err.Error(), "must be a named Oak function") {
		t.Fatalf("local function value must not resolve to the library declaration: %v", err)
	}
}

func TestE2ELeanReduceLanesFunctionArgument(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/lanes\noak 0.1.0\n",
		"main.oak": `package main
r := import("reduce")
plus: (a: f32, b: f32): f32 = a + b
maximum: (a: f32, b: f32): f32 = a > b ? a | b
check: (count: u32, run: u32): Bool {
  xs: [5]f32 = [1.0, 2.0, 4.0, 8.0, 16.0]
  zero: f32 = 0.0
  total: f32 = r.lanes(view(&xs), zero, plus, count, run)
  largest: f32 = r.lanes(view(&xs), zero, maximum, count, run)
  total == 31.0 && largest == 16.0
}
main: (): i32 = check(1, 1) && check(4, 2) && check(32, 4) && check(256, 1) ? 42 | 1
`,
	})
	comp := New().WithPackageDir(root)
	if code, abnormal := buildPackageAndRun(t, comp); abnormal || code != 42 {
		t.Fatalf("C exit=(%d,%v), want 42", code, abnormal)
	}
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreter result=%d, want 42", got)
	}
	extracted, err := comp.EmitLeanRoots("Oak.LanesArguments", []string{"check"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	t.Run("Lean", func(t *testing.T) {
		checkFunctionArgumentLean(t, extracted+`
def main : IO Unit := do
  for (count, run) in [(1, 1), (4, 2), (32, 4), (256, 1)] do
    unless Oak.LanesArguments.check count run 300 == some true do
      throw (IO.userError "reduce.lanes callback result disagrees")
`, true)
	})
}

func checkFunctionArgumentLean(t *testing.T, source string, run bool) {
	t.Helper()
	lake := findLake()
	if lake == "" {
		t.Skip("lake not found (PATH or ~/.elan/bin)")
	}
	path := filepath.Join(t.TempDir(), "FunctionArguments.lean")
	if err := os.WriteFile(path, []byte(source), 0o644); err != nil {
		t.Fatal(err)
	}
	args := []string{"env", "lean"}
	if run {
		args = append(args, "--run")
	}
	ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, lake, append(args, path)...)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Lean: %v\n%s\n%s", err, out, source)
	}
}
