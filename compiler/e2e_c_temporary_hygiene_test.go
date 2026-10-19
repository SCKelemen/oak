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

// C declarators enter scope before their initializer. A realization named
// claimed used to become `u32 oak_claimed = oak_claimed(x)`, which is invalid C.
func TestCDispatchTemporariesAvoidCallableShadowing(t *testing.T) {
	generated, err := New().WithSource("dispatch_names.oak", `
checked: (x: u32): u32 dispatch { crc: claimed } = x
claimed: (x: u32): u32 = x
`).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	// The CRC branch is inert on non-AArch64 hosts. Compile the exact emitted
	// checked block in a scalar harness, without claiming native CRC coverage.
	_, tail, ok := strings.Cut(generated, "\n#ifdef OAK_CHECK_DISPATCH\n    { ")
	if !ok {
		t.Fatal("missing checked dispatch block")
	}
	block, _, ok := strings.Cut(tail, "\n#else\n")
	if !ok || !strings.Contains(block, "oak_dispatch_claimed = oak_claimed(") || !strings.Contains(block, "oak_dispatch_meant = oak_checked__meaning(") {
		t.Fatalf("unexpected checked dispatch block: %s", block)
	}
	harness := `typedef unsigned int u32;
static u32 oak_claimed(u32 x) { return x; }
static u32 oak_checked__meaning(u32 x) { return x; }
static void oak_dispatch_divergence(const char *function, const char *feature) { __builtin_trap(); }
static u32 checked(u32 x) {
{ ` + block + `
}
int main(void) { return (int)checked(42); }
`
	legacy := strings.ReplaceAll(harness, "oak_dispatch_claimed", "oak_claimed")
	legacy = strings.ReplaceAll(legacy, "oak_dispatch_meant", "oak_meant")
	for _, level := range []string{"-O0", "-O2"} {
		t.Run(level, func(t *testing.T) {
			checkTemporarySymbolC(t, harness, level, "")
			checkTemporarySymbolC(t, legacy, level, "oak_claimed")
		})
	}
}

// Grid, argument and loop temporaries must not shadow callable initializers or
// the kernel call. pub keeps both initializer calls visible to the C frontend.
func TestE2CLaunchTemporariesAvoidCallableShadowing(t *testing.T) {
	generated, err := New().WithSource("launch_names.oak", `
pub la1_grid: (): u32 = u32(1)
pub la1_a0: (): u32 = u32(42)
la1_g: (gid: u32, value: u32, output: [*]u32): () (kernel) = {
  output[gid] = value
}
main: (): i32 {
  output: [1]u32
  test_launch(la1_g, la1_grid(), la1_a0(), span(&output))
  i32_bits_u32(output[0])
}
`).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"oak_host_la1_grid = oak_la1_grid(", "oak_host_la1_a0 = oak_la1_a0(", "oak_la1_g(oak_host_la1_g"} {
		if !strings.Contains(generated, want) {
			t.Fatalf("missing callable/temporary boundary %q", want)
		}
	}
	// The real test host supplies these recorder hooks. Here the complete
	// emitted host launch still executes its kernel and the result must be 42.
	harness := generated + `
void oak_test_host_launch_begin(const char *kernel, uint32_t grid) { if (grid != 1) __builtin_trap(); }
void oak_test_host_launch_arg(const char *name, const char *kind, const char *element, const void *base, uint32_t bytes) {}
void oak_test_host_launch_out(const char *name, const void *base, uint32_t bytes) {}
void oak_test_host_launch_end(void) {}
`
	legacy := strings.ReplaceAll(harness, "oak_host_la1_", "oak_la1_")
	for _, level := range []string{"-O0", "-O2"} {
		t.Run(level, func(t *testing.T) {
			checkTemporarySymbolC(t, harness, level, "")
			checkTemporarySymbolC(t, legacy, level, "oak_la1_grid")
		})
	}
}

// The negative control changes only emitted temporary spellings. A successful
// build there would mean the regression stopped exercising C identifier scope.
func checkTemporarySymbolC(t *testing.T, source, level, rejectedSymbol string) {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_CC") == "1" {
			t.Fatal("OAK_REQUIRE_CC=1 requires a C compiler on PATH")
		}
		t.Skip("no C compiler on PATH")
	}
	dir := t.TempDir()
	input, binary := filepath.Join(dir, "names.c"), filepath.Join(dir, "names")
	if err := os.WriteFile(input, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()
	out, err := exec.CommandContext(ctx, cc, "-std=c99", level, "-o", binary, input, "-lm").CombinedOutput()
	if ctx.Err() != nil {
		t.Fatal("temporary-symbol C compilation exceeded deadline")
	}
	if rejectedSymbol != "" {
		if err == nil || !strings.Contains(string(out), rejectedSymbol) {
			t.Fatalf("legacy temporary must fail C compilation at %s: %v\n%s", rejectedSymbol, err, out)
		}
		return
	}
	if err != nil {
		t.Fatalf("C compilation failed: %v\n%s", err, out)
	}
	out, err = exec.CommandContext(ctx, binary).CombinedOutput()
	status, exited := err.(*exec.ExitError)
	if ctx.Err() != nil || !exited || status.ExitCode() != 42 {
		t.Fatalf("C execution must exit 42: %v\n%s", err, out)
	}
}
