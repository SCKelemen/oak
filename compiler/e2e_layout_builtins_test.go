package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

// User-facing layout introspection and compile-time assertion
// (docs/spec/40-records.md §6b): size_of/align_of/offset_of read the real
// emitted type, and static_assert makes cc ratify the author's claim.
func TestE2ELayoutIntrospection(t *testing.T) {
	src := `
Ring: type = struct {
  head: u32
  tail: u32
  buffer: [8]u8
}

Line: type = struct(align: 64) {
  cell: u32
}

static_assert(size_of[Ring]() == u32(16))
static_assert(offset_of[Ring](tail) == u32(4))
static_assert(align_of[Line]() == u32(64))

main: (): i32 {
  static_assert(offset_of[Ring](buffer) == u32(8))
  assert(size_of[Ring]() == u32(16))
  assert(size_of[u64]() == u32(8))
  assert(align_of[Line]() == u32(64))
  assert(offset_of[Ring](tail) == u32(4))
  42
}
`
	output, err := New().WithSource("layoutq.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{"sizeof(oak_Ring)", "offsetof(oak_Ring, tail)", "_Alignof(oak_Line)", "oak_static_assert_0", "oak_static_assert_2"} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	code, abnormal := buildAndRun(t, "layoutq", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A false static_assert is a C compile error, never a passing build.
func TestE2EStaticAssertFailsTheBuild(t *testing.T) {
	output, err := New().WithSource("badassert.oak", `
Ring: type = struct {
  head: u32
  tail: u32
}

static_assert(size_of[Ring]() == u32(64))

main: (): i32 = 42
`).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed before cc: %v", err)
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	dir := t.TempDir()
	cPath := filepath.Join(dir, "badassert.c")
	if err := os.WriteFile(cPath, []byte(output), 0o644); err != nil {
		t.Fatal(err)
	}
	if _, err := exec.Command(cc, "-std=c99", "-c", cPath, "-o", filepath.Join(dir, "badassert.o")).CombinedOutput(); err == nil {
		t.Fatal("a false static_assert must fail the C build")
	}
}

// Section placement for statics (docs/spec/65-machine-memory.md).
func TestE2ESectionPlacement(t *testing.T) {
	section := ".oakring"
	if runtime.GOOS == "darwin" {
		section = "__DATA,oakring"
	}
	src := `
ring: [4]u64 (section: "` + section + `")
counter: u32 (section: "` + section + `") = 40

main: (): i32 {
  ring[u32(1)] = u64(2)
  assert(counter + u32_trunc_u64(ring[u32(1)]) == u32(42))
  42
}
`
	output, err := New().WithSource("section.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if strings.Count(output, `__attribute__((section("`+section+`")))`) != 2 {
		t.Fatalf("section attribute not emitted for both statics:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "section", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// address_of names an asm-backed function's code symbol — the vector-table
// install path — and nothing else.
func TestE2EAddressOfAsmFunction(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("addrof.oak", `
add_asm: (left, right: u32) -> u32

main: (): i32 {
  entry: u64 = address_of(add_asm)
  assert(entry != u64(0))
  assert(add_asm(u32(40), u32(2)) == u32(42))
  42
}
`).WithAsmUnit("add.arm64.oakasm", `
add_asm: (left, right: u32) -> u32 = {
  bind w0 = left
  bind w1 = right
  add w0, w0, w1
  ret
}
`)
	_, code, abnormal := buildAndRunFrom(t, "addrof", comp)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	_, err := New().WithSource("addrbad.oak", "plain: (x: u32): u32 = x\nmain: (): i32 {\n  a: u64 = address_of(plain)\n  42\n}\n").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "admits only asm-backed") {
		t.Fatalf("address_of of an ordinary function must be rejected, got %v", err)
	}
}

func TestLayoutBuiltinRejections(t *testing.T) {
	for name, src := range map[string]string{
		"runtime static_assert": "main: (): i32 {\n  x: u32 = 5\n  static_assert(x == u32(5))\n  42\n}\n",
		"unknown field":         "R: type = struct { a: u32 }\nmain: (): i32 {\n  assert(offset_of[R](b) == u32(0))\n  42\n}\n",
		"section spelling":      "ring: [4]u64 (section: \"bad name\")\nmain: (): i32 = 42\n",
	} {
		if _, err := New().WithSource(name+".oak", src).EmitC().Get(); err == nil {
			t.Fatalf("%s must be rejected", name)
		}
	}
}
