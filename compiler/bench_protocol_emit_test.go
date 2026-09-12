package compiler

import (
	"os"
	"path/filepath"
	"testing"
)

// TestEmitStateMachineBenchmarkSource regenerates the Oak-compiled half of
// benchmarks/state-machines: the UTF-8 protocol of
// e2e_protocol_lowering_test.go with `utf8_run` exported, as the C the
// backend emits. Run with OAK_UPDATE_BENCH=1; benchmarks/state-machines/
// README.md explains how the driver times it against the hand-written
// lowerings in lowerings.c.
func TestEmitStateMachineBenchmarkSource(t *testing.T) {
	if os.Getenv("OAK_UPDATE_BENCH") == "" {
		t.Skip("set OAK_UPDATE_BENCH=1 to regenerate benchmarks/state-machines/utf8_protocol.c")
	}
	// main also calls the is_valid_utf8 builtin so the backend emits its
	// scalar validator beside the protocol's tables; the cross-language
	// harness times both.
	src := "package main\nutf8 := import(\"utf8\")\n" + utf8Machine + `
// The three validators the harness times: the protocol machine's
// utf8_run, the scalar builtin, and the stdlib's SIMD validator.
pub scalar_valid: (bytes: []u8): Bool = is_valid_utf8(bytes)
pub simd_valid: (bytes: []u8): Bool = utf8.valid(bytes)
main: (): u32 {
  text: [4]u8 = [u8(104), u8(105), u8(195), u8(169)]
  scalar_valid(view(&text)) && simd_valid(view(&text)) ? u32(0) | u32(1)
}
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	c, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	out := filepath.Join("..", "benchmarks", "state-machines", "utf8_protocol.c")
	if err := os.WriteFile(out, []byte(c), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join("..", "benchmarks", "state-machines", "utf8_protocol.oak"), []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
}
