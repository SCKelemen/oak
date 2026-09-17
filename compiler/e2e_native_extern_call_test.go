package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// An extern binding under a host-only effect row lowers to a fresh
// result with no effect on Oak memory (docs/spec/94-assembler.md §9):
// the prover's write family flushes its buffer through
// host_write_all, whose loop calls the extern oak_host_write, and every
// caller stopped at "a call". The shape is that flush: a top-level
// buffer, a push, a flush through the host, and a caller of the three.
const nativeExternCallProgram = `
import("host")

buf: [16]u8
pos: u32

push: (b: u8): () {
  pos < u32(16) ? {
    buf[pos] = b
    pos = pos + u32(1)
  } | { }
}

flush: (): () {
  chunk: [16]u8
  k: u32 = u32(0)
  while k < pos {
    chunk[k] = buf[k]
    k = k + u32(1)
  }
  piece: []u8 = view(&chunk)
  host.host_write_all(host.host_stdout(), subslice(piece, u32(0), pos)) ? { } | { }
  pos = u32(0)
}

emit: (a: u8, b: u8): () {
  push(a)
  push(b)
  flush()
}

main: (): i32 {
  emit(u8(72), u8(10))
  pos == u32(0) ? 42 | 1
}
`

// The same flush through a 4096-byte chunk, the prover's write_flush's
// size: the chunk is a span memory on both sides (largeArrayElements), so
// the copy loop couples through it and the call summary binds the
// subslice handed to host_write_all as an alias of the local span; the
// flush itself proves.
const nativeExternLargeChunkProgram = `
import("host")

buf: [16]u8
pos: u32

push: (b: u8): () {
  pos < u32(16) ? {
    buf[pos] = b
    pos = pos + u32(1)
  } | { }
}

flush: (): () {
  chunk: [4096]u8
  k: u32 = u32(0)
  while k < pos {
    chunk[k] = buf[k]
    k = k + u32(1)
  }
  piece: []u8 = view(&chunk)
  host.host_write_all(host.host_stdout(), subslice(piece, u32(0), pos)) ? { } | { }
  pos = u32(0)
}

emit: (a: u8, b: u8): () {
  push(a)
  push(b)
  flush()
}

main: (): i32 {
  emit(u8(72), u8(10))
  pos == u32(0) ? 42 | 1
}
`

func TestE2ENativeExternFlushLargeChunkProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/externchunk\noak 0.1.0\n",
		"main.oak": nativeExternLargeChunkProgram,
	})
	comp := New().WithPackageDir(root).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	stdout, code, abnormal := buildAndRunFrom(t, "native_extern_chunk", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("extern flush through a large chunk: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if stdout != "H\n" {
		t.Errorf("the flush must reach stdout: got %q", stdout)
	}
	// emit's summary of flush lowers flush's Oak body with the chunk as a
	// span memory: the copy loop and host_write_all's loop couple through
	// it (the prover's write family reaches write_flush the same way).
	if !strings.Contains(joined, "asm unit emit: proven equal to its Oak body at the bit level — 2 data-dependent loops coupled inductively") {
		t.Errorf("emit must be proven with flush's chunk as a span memory; diagnostics:\n%s", joined)
	}
	// flush itself has a 4192-byte frame, past the native backend's own
	// limit: the C backend keeps it, as it keeps the prover's write_flush.
	if !strings.Contains(joined, "flush left to the C backend (a frame of 4192 bytes)") {
		t.Errorf("flush's frame is past the native backend's limit and must be left to the C backend; diagnostics:\n%s", joined)
	}
}

func TestE2ENativeExternCallProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/externcall\noak 0.1.0\n",
		"main.oak": nativeExternCallProgram,
	})
	comp := New().WithPackageDir(root).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	stdout, code, abnormal := buildAndRunFrom(t, "native_extern_call", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("extern call: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if stdout != "H\n" {
		t.Errorf("the flush must reach stdout: got %q", stdout)
	}
	// emit's call to flush is summarized at flush's Oak body, whose flush
	// through host_write_all meets the extern: proven relative to it.
	if !strings.Contains(joined, "asm unit emit: proven equal to its Oak body") {
		t.Errorf("emit reaches the host through host_write_all's extern and must be proven; diagnostics:\n%s", joined)
	}
	// flush itself hands host_write_all a subslice of its frame array
	// with a symbolic length, which the call summary does not bind yet
	// (asm/span_args.go frameArrayArgument: the length must be a
	// constant); until it does, the reason is that and nothing about
	// the extern.
	if !strings.Contains(joined, "asm unit flush: not verified (a call to host__host_uwrite_uall: the span argument bytes is not one of the caller's span parameters passed whole (its length is not a constant))") {
		t.Errorf("flush must stop at the summary's constant-length binding, not at the extern; diagnostics:\n%s", joined)
	}
}
