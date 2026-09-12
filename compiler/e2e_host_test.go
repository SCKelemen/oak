package compiler

import (
	"strings"
	"testing"
)

// The host package (stdlib/host.oak; docs/spec/90-backend.md §2a): a
// program writes through the host boundary's one write hook. Hosted, the
// code generator defines the hook over the C library, so the bytes reach
// stdout; freestanding, the firmware defines it (compiler/e2e_mcu_test.go
// puts a UART behind it) and the same C compiles with no libc symbol.
const hostProgram = `package main

import("host")

main: (): i32 {
  line: [6]u8 = [6]u8{ u8(104), u8(101), u8(108), u8(108), u8(111), u8(10) }
  wrote: i64 = host.host_write(host.host_stdout(), view(&line))
  all: Bool = host.host_write_all(host.host_stdout(), view(&line))
  empty: [1]u8
  ev: []u8 = view(&empty)
  none: i64 = host.host_write(host.host_stdout(), subslice(ev, u32(0), u32(0)))
  wrote == i64(6) && all && none == i64(0) ? 0 | 1
}
`

func hostModule(t *testing.T) Compilation {
	t.Helper()
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/hostwrite\noak 0.1.0\n",
		"main.oak": hostProgram,
	})
	return New().WithPackageDir(root)
}

func TestE2EHostWriteReachesStdout(t *testing.T) {
	stdout, code, abnormal := buildAndRunFrom(t, "hostwrite", hostModule(t))
	if abnormal || code != 0 {
		t.Fatalf("exit = (%d, abnormal=%v), want 0; stdout %q", code, abnormal, stdout)
	}
	if stdout != "hello\nhello\n" {
		t.Fatalf("stdout = %q, want two hello lines", stdout)
	}
}

func TestE2EHostWriteDeclaresTheHookOnce(t *testing.T) {
	output, err := hostModule(t).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// One boundary signature, from emitHostBoundary; the binding's own
	// prototype (void * for c.Ptr) is not emitted, so nothing conflicts.
	if strings.Count(output, "int64_t oak_host_write(int64_t fd, const uint8_t *buf, size_t len)") < 2 {
		t.Fatalf("host boundary declaration missing:\n%s", output)
	}
	if strings.Contains(output, "extern int64_t oak_host_write_call(") || strings.Contains(output, "void *data") {
		t.Fatalf("the binding's own prototype was emitted:\n%s", output)
	}
	if !strings.Contains(output, "if (&oak_host_write == 0) { return 0; }") {
		t.Fatalf("freestanding shim missing its null check:\n%s", output)
	}
	if !strings.Contains(output, "#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n#include <stdio.h>\nint64_t oak_host_write") {
		t.Fatalf("hosted definition not guarded:\n%s", output)
	}
}

// Freestanding, the program compiles for a Cortex-M4 with the hook as its
// only host symbol: the hosted definition and its <stdio.h> sit behind the
// hosted guard.
func TestE2EHostWriteFreestandingObjectIsLibcFree(t *testing.T) {
	code, err := hostModule(t).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if ok, out := crossCompile(t, "thumbv7em-none-eabi", "cortex-m4", code); !ok {
		t.Fatalf("cortex-m4 build failed:\n%s", out)
	}
}
