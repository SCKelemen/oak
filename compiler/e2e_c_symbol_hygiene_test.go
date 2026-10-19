package compiler

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/typechecker"
)

// Keep the legal three-argument store spelling: renaming this fixture only
// hides the collision with the four-argument oak_store runtime macro.
func TestE2ECCallablesAvoidRuntimeSymbols(t *testing.T) {
	const source = `
store: (s: [*]u32, i: u32, value: u32): u32 { s[i] = value; s[i] }
bounds_trap: (x: u32): u32 = x + u32(1)
add_u32: (x: u32, y: u32): u32 = x + y + u32(1)
view_u8: (): u32 = u32(2)
fn_at: (): u32 = u32(3)
main: (): i32 {
  data: [2]u32
  put := store
  bump := bounds_trap
  add := add_u32
  view_name := view_u8
  at := fn_at
  assert(store(span(&data), u32(0), u32(20)) == u32(20))
  assert(put(span(&data), u32(1), u32(15)) == u32(15))
  assert(add(bump(data[0]), data[1]) + view_name() + at() == u32(42))
  42
}
`
	comp := New().WithSource("runtime_symbols.oak", source)
	generated, err := comp.EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"store", "bounds_trap", "add_u32", "view_u8", "fn_at"} {
		symbol := typechecker.CFunctionSymbol("main", name)
		if !strings.Contains(generated, symbol+"(") {
			t.Errorf("missing escaped declaration/definition for %s", name)
		}
		generator := codegen.New("main", nil)
		if generator.CFunctionName(name) != symbol || generator.AsmSymbol(name) != symbol {
			t.Errorf("native/C symbol disagreement for %s", name)
		}
	}
	for _, helper := range []string{"#define oak_store(", "static inline u64 oak_bounds_trap(", "oak_add_u32", "oak_view_u8"} {
		if !strings.Contains(generated, helper) {
			t.Errorf("runtime helper was removed or renamed: %s", helper)
		}
	}
	for _, level := range []string{"-O0", "-O2"} {
		t.Run(level, func(t *testing.T) {
			_, code, abnormal := buildAndRunFrom(t, "runtime_symbols", comp, level)
			if abnormal || code != 42 {
				t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
			}
		})
	}
}

func TestE2EEscapedCallableHeaderAndABI(t *testing.T) {
	for _, test := range []struct{ name, option, declaration, fn string }{
		{"root", "main", "", "store"},
		{"option", "view", "", "read"},
		{"source", "ignored", "package view\n", "read"},
	} {
		t.Run(test.name, func(t *testing.T) {
			pkg := test.option
			if test.declaration != "" {
				pkg = "view"
			}
			symbol := typechecker.CFunctionSymbol(pkg, test.fn)
			source := test.declaration + fmt.Sprintf(`
pub %s: (x: i32): i32 = x + 1
export("stable_entry") pub bridge: (x: i32): i32 = %s(x)
probe: (): c.Int32 = c.extern("probe_symbols")
main: (): i32 = i32(probe())
`, test.fn, test.fn)
			comp := New().WithPackageName(test.option).WithSource("symbols.oak", source)
			header, err := comp.EmitHeader().Get()
			if err != nil {
				t.Fatal(err)
			}
			if !strings.Contains(header, "i32 "+symbol+"( i32 x );") || !strings.Contains(header, "i32 stable_entry( i32 x );") {
				t.Fatalf("header and callable ABI disagree:\n%s", header)
			}
			dir := t.TempDir()
			if err := os.WriteFile(filepath.Join(dir, "symbols.h"), []byte(header), 0600); err != nil {
				t.Fatal(err)
			}
			consumer := fmt.Sprintf("#include \"symbols.h\"\nint32_t probe_symbols(void) { return %s(19) + stable_entry(21); }\n", symbol)
			consumerPath := filepath.Join(dir, "consumer.c")
			if err := os.WriteFile(consumerPath, []byte(consumer), 0600); err != nil {
				t.Fatal(err)
			}
			_, code, abnormal := buildAndRunFrom(t, "symbols", comp, "-I"+dir, consumerPath)
			if abnormal || code != 42 {
				t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
			}
		})
	}
}

func TestCReservedExplicitABISymbolsRejected(t *testing.T) {
	for _, symbol := range []string{"oak_store", "oak_add_u32", "oak_view_u8", "oak_0f_p0__nstore", "__oak_cas_u32_seq_cst", "OAK_INLINE", "core_slice",
		"oak_test_host_unknown", "oak_test_host_fail_extra", "oak_test_host_command_limits", "oak_host_read"} {
		for _, kind := range []string{"extern", "export"} {
			t.Run(kind+"/"+symbol, func(t *testing.T) {
				source := fmt.Sprintf("export(%q) pub entry: (x: i32): i32 = x\n", symbol)
				if kind == "extern" {
					source = fmt.Sprintf("entry: (x: c.Int32): c.Int32 = c.extern(%q)\n", symbol)
				}
				_, err := New().WithSource("collision.oak", source).Check().Get()
				if err == nil || !strings.Contains(err.Error(), "reserved by the C backend") || !strings.Contains(err.Error(), symbol) {
					t.Fatalf("expected explicit ABI collision diagnostic, got %v", err)
				}
			})
		}
	}
}

func TestCRuntimeHostHooksRemainExternOnly(t *testing.T) {
	for _, symbol := range []string{
		"oak_host_write_call", "oak_host_write", "oak_measured_value",
		"oak_test_host_launch_begin", "oak_test_host_launch_arg", "oak_test_host_launch_out", "oak_test_host_launch_end",
		"oak_test_host_dispatch_divergence", "oak_test_host_fail", "oak_test_host_fail_values",
		"oak_test_host_discard", "oak_test_host_classify", "oak_test_host_liveness", "oak_test_host_trace",
		"oak_test_host_command", "oak_test_host_command_limit",
	} {
		t.Run(symbol, func(t *testing.T) {
			// Existing host contracts remain references to exactly their ABI
			// spelling; the callable escape must not change an extern target.
			if typechecker.ReservedCExternSymbol(symbol) {
				t.Fatalf("documented host hook %s was rejected", symbol)
			}
			reference := fmt.Sprintf("entry: (): c.Int32 = c.extern(%q)\n", symbol)
			if _, err := New().WithSource("host_reference.oak", reference).Check().Get(); err != nil {
				t.Fatalf("runtime hook reference must be accepted: %v", err)
			}
			source := fmt.Sprintf("export(%q) pub entry: (): i32 = 1\n", symbol)
			_, err := New().WithSource("host_export.oak", source).Check().Get()
			if err == nil || !strings.Contains(err.Error(), "reserved by the C backend") {
				t.Fatalf("runtime hook export must be rejected: %v", err)
			}
		})
	}
}

// The actual testing module must typecheck and keep its exact host ABI in
// both ordinary and simulation compilations. Each of its eight imports is
// called with distinguishable arguments and linked against the real C types.
func TestE2ETestingHostRuntimeSymbolsPreserveABI(t *testing.T) {
	const source = `import(testing)
main: (): i32 {
  testing_fail_host(c.UInt32(1))
  testing_fail_values_host(c.UInt32(2), c.UInt64(3), c.UInt64(4), c.UInt32(5))
  testing_discard()
  testing_classify_host(c.UInt32(6))
  testing_liveness_host(c.UInt32(7))
  testing_trace_host(c.UInt32(8), c.UInt64(9), c.UInt64(10))
  testing_command_host(c.UInt32(11), c.UInt32(12), c.UInt32(13))
  i32_bits_u32(u32(testing_command_limit_host()))
}
`
	const host = `#include <stdint.h>
#include <stdlib.h>
static uint32_t seen;
void oak_test_host_fail(uint32_t id) { if (id != 1) abort(); seen |= 1; }
void oak_test_host_fail_values(uint32_t id, uint64_t got, uint64_t want, uint32_t kind) {
  if (id != 2 || got != 3 || want != 4 || kind != 5) abort(); seen |= 2;
}
void oak_test_host_discard(void) { seen |= 4; }
void oak_test_host_classify(uint32_t id) { if (id != 6) abort(); seen |= 8; }
void oak_test_host_liveness(uint32_t id) { if (id != 7) abort(); seen |= 16; }
void oak_test_host_trace(uint32_t id, uint64_t a, uint64_t b) {
  if (id != 8 || a != 9 || b != 10) abort(); seen |= 32;
}
void oak_test_host_command(uint32_t kind, uint32_t target, uint32_t value) {
  if (kind != 11 || target != 12 || value != 13) abort(); seen |= 64;
}
uint32_t oak_test_host_command_limit(void) { return seen == 127 ? 42 : 1; }
`
	dir := t.TempDir()
	hostPath := filepath.Join(dir, "testing_host.c")
	if err := os.WriteFile(hostPath, []byte(host), 0600); err != nil {
		t.Fatal(err)
	}
	for _, simulation := range []bool{false, true} {
		t.Run(fmt.Sprintf("simulation=%v", simulation), func(t *testing.T) {
			comp := New().WithSource("testing_host.oak", source)
			if simulation {
				comp = comp.WithSimulation(nil)
			}
			_, code, abnormal := buildAndRunFrom(t, "testing_host", comp, hostPath)
			if abnormal || code != 42 {
				t.Fatalf("host ABI execution = (%d, abnormal=%v), want 42", code, abnormal)
			}
		})
	}
}
