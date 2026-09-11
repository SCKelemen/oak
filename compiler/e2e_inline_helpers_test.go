package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// assembleC compiles generated C to assembly text with the system C compiler
// at the given optimization level, for inspection by the tests below.
func assembleC(t *testing.T, name, generated string, opt string) string {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	dir := t.TempDir()
	cpath := filepath.Join(dir, name+".c")
	spath := filepath.Join(dir, name+".s")
	if err := os.WriteFile(cpath, []byte(generated), 0644); err != nil {
		t.Fatal(err)
	}
	if output, err := exec.Command(cc, "-std=c99", "-w", opt, "-S", "-o", spath, cpath).CombinedOutput(); err != nil {
		t.Fatalf("cc %s -S: %v\n%s", opt, err, output)
	}
	asm, err := os.ReadFile(spath)
	if err != nil {
		t.Fatal(err)
	}
	return string(asm)
}

// callsTo reports the call instructions targeting an emitted Oak function,
// in the x86-64 (call/callq) and AArch64 (bl) spellings, with or without the
// platform's leading underscore.
func callsTo(asm, cSymbol string) int {
	pattern := regexp.MustCompile(`(?m)^\s*(call|callq|bl)\s+_?` + regexp.QuoteMeta(cSymbol) + `\b`)
	return len(pattern.FindAllString(asm, -1))
}

// Small private helpers are forced inline (docs/spec/90-backend.md section
// 9): naming an operation and composing it costs no call at any
// optimization level, including -O0 where the C compiler's own heuristics
// inline nothing.
func TestE2ESmallHelpersInlineAtEveryLevel(t *testing.T) {
	src := `
is_space: (b: u8): Bool {
  b == 32 || b == 9 || b == 13
}
encoded: (magnitude: u32, sign: u32): u32 {
  e: u32 = (magnitude - 1) * 2
  sign == 1 ? { e + 1 } | { e }
}
pub exported_helper: (n: u32): u32 {
  n + 1
}
count_spaces: (text: []u8): u32 {
  i: u32 = 0
  spaces: u32 = 0
  while i < len(text) {
    is_space(text[i]) ? { spaces = spaces + 1 }
    i = i + 1
  }
  spaces
}
main: (): i32 {
  buffer: [8]u8
  buffer[1] = 32
  buffer[5] = 9
  view: []u8 = buffer[0:8]
  assert(count_spaces(view) == 2)
  assert(encoded(3, 1) == 5)
  assert(encoded(3, 2) == 4)
  assert(is_space(13) && !is_space(65))
  assert(exported_helper(41) == 42)
  42
}
`
	generated, err := New().WithSource("helpers.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"OAK_INLINE Bool oak_is_space( u8 b )", "OAK_INLINE u32 oak_encoded( u32 magnitude, u32 sign )", "\nu32 oak_exported_helper( u32 n )"} {
		if !strings.Contains(generated, want) {
			t.Fatalf("generated C lacks %q", want)
		}
	}
	if strings.Contains(generated, "OAK_INLINE u32 oak_count_spaces") || strings.Contains(generated, "OAK_INLINE i32 oak_main") {
		t.Fatal("a looping function or main was marked inline")
	}
	for _, opt := range []string{"-O0", "-O1", "-O2"} {
		asm := assembleC(t, "helpers", generated, opt)
		for _, helper := range []string{"oak_is_space", "oak_encoded"} {
			if n := callsTo(asm, helper); n != 0 {
				t.Fatalf("%s: %d call(s) to %s remain in assembly", opt, n, helper)
			}
		}
		if callsTo(asm, "oak_exported_helper") == 0 && opt == "-O0" {
			t.Fatalf("%s: the exported helper should stay an ordinary call", opt)
		}
	}
	code, abnormal := buildAndRun(t, "helpers_run", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Recursive or looping functions never get the forced-inline marking, so
// the C compiler is never asked to inline what it cannot.
func TestInlineHelpersExcludeRecursionAndLoops(t *testing.T) {
	generated, err := New().WithSource("shapes.oak", `
countdown: (n: u32): u32 {
  n == 0 ? { 0 } | { countdown(n - 1) }
}
spin: (n: u32): u32 {
  i: u32 = 0
  while i < n { i = i + 1 }
  i
}
uses_helper: (n: u32): u32 {
  spin(n) + 1
}
main: (): i32 {
  assert(countdown(3) == 0)
  assert(uses_helper(4) == 5)
  42
}
`).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"oak_countdown", "oak_spin", "oak_uses_helper"} {
		if strings.Contains(generated, "OAK_INLINE u32 "+name) {
			t.Fatalf("%s was marked inline", name)
		}
	}
}
