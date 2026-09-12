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
// A scalar transliteration of Unicode Table 3-7 in Oak, the oracle the
// vector validator is checked against: byte by byte, each lead's required
// continuations, nothing else.
utf8_cont: (b: u8): Bool = b >= u8(128) && b <= u8(191)
utf8_second3: (b0: u8, b1: u8): Bool =
  b0 == u8(224) ? (b1 >= u8(160) && b1 <= u8(191))
  | b0 == u8(237) ? (b1 >= u8(128) && b1 <= u8(159))
  | utf8_cont(b1)
utf8_second4: (b0: u8, b1: u8): Bool =
  b0 == u8(240) ? (b1 >= u8(144) && b1 <= u8(191))
  | b0 == u8(244) ? (b1 >= u8(128) && b1 <= u8(143))
  | utf8_cont(b1)
utf8_scalar: (v: []u8): Bool {
  n: u32 = len(v)
  i: u32 = u32(0)
  ok: Bool = true
  while ok && i < n {
    b0: u8 = v[i]
    b0 <= u8(127) ? { i = i + u32(1) }
    | b0 >= u8(194) && b0 <= u8(223) ? {
      i + u32(1) < n && utf8_cont(v[i + u32(1)]) ? { i = i + u32(2) } | { ok = false }
    }
    | b0 >= u8(224) && b0 <= u8(239) ? {
      i + u32(2) < n && utf8_second3(b0, v[i + u32(1)]) && utf8_cont(v[i + u32(2)]) ? { i = i + u32(3) } | { ok = false }
    }
    | b0 >= u8(240) && b0 <= u8(244) ? {
      i + u32(3) < n && utf8_second4(b0, v[i + u32(1)]) && utf8_cont(v[i + u32(2)]) && utf8_cont(v[i + u32(3)]) ? { i = i + u32(4) } | { ok = false }
    }
    | { ok = false }
  }
  ok
}
pub scalar_valid: (bytes: []u8): Bool = utf8_scalar(bytes)
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
