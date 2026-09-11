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
	src := utf8Machine + "\nmain: (): u32 = u32(0)\n"
	c, err := New().WithSource("utf8_protocol.oak", src).EmitC().Get()
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
