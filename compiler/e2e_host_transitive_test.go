package compiler

import (
	"strings"
	"testing"
)

// The hosted definition of oak_host_write is emitted when any package of
// the program — not only the root — binds the hook through import("host")
// (docs/notes/oak-requests-2026-09-13.md finding 4).
func TestE2EHostHookEmittedForLibraryImport(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/hostuse\noak 0.1.0\n",
		"out/out.oak": `package out

import("host")

pub say: (line: []u8): i64 = host.host_write(host.host_stdout(), line)
`,
		"main.oak": `package main

import("example.com/hostuse/out")

main: (): i32 {
  line: [3]u8 = [3]u8{ u8(111), u8(107), u8(10) }
  wrote: i64 = out.say(view(&line))
  wrote == i64(3) ? 42 | 1
}
`,
	})
	output, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "int64_t oak_host_write(int64_t fd, const uint8_t *buf, size_t len) {") {
		t.Fatalf("hosted oak_host_write definition missing when the hook is bound from a library package:\n%s", output)
	}
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
