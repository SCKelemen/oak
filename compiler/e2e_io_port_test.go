package compiler

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// The IO port (docs/spec/120-io.md): one program text against
// `import("io")`, two realizations selected by `replace io => iosim` or
// `replace io => ionative`. The consumer opens a file, writes eight bytes
// linked to an fsync, reads them back, takes a short read past the end,
// syncs the directory, and closes. Both realizations must complete every
// tag with the same results and errors (order is unordered except along
// the link chain, which the consumer checks by tag).
const ioPortConsumer = `package main
import(std)
import("io")

// "oak_io_t.bin" followed by NUL, and "." followed by NUL.
io_path: (region: [*]u8): () {
  bytes: [13]u8 = [u8(111), u8(97), u8(107), u8(95), u8(105), u8(111), u8(95), u8(116), u8(46), u8(98), u8(105), u8(110), u8(0)]
  i: u32 = u32(0)
  while i < u32(13) {
    region[i] = bytes[i]
    i = i + u32(1)
  }
  region[96] = u8(46)
  region[97] = u8(0)
}

find_tag: (completions: [*]io.IoCompletion, count: u32, tag: u64): u32 {
  i: u32 = u32(0)
  found: u32 = u32(4294967295)
  while i < count {
    completions[i].tag == tag ? { found = i } | { }
    i = i + u32(1)
  }
  found
}

main: (): i32 {
  ring_store: [1]io.IoRing
  req_store: [8]io.IoRequest
  cq_store: [8]io.IoCompletion
  region_store: [128]u8
  tape: [4]u8
  ring: [*]io.IoRing = span(&ring_store)
  requests: [*]io.IoRequest = span(&req_store)
  completions: [*]io.IoCompletion = span(&cq_store)
  region: [*]u8 = span(&region_store)
  io.io_attach(view(&tape), u32(0))
  io.io_open_region(ring, region, u32(2))
  io_path(region)
  i: u32 = u32(0)
  while i < u32(8) {
    region[u32(32) + i] = u8_trunc_u32(i + u32(1))
    i = i + u32(1)
  }

  // open slot 0 (tag 1)
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_open(), u32(0), u64(0), u32(0), u32(13), u64(1), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].tag == u64(1) && completions[0].error == u32(0) && completions[0].result == u32(0))

  // pwrite linked to fsync (tags 2, 3)
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_pwrite(), u32(0), u64(0), u32(32), u32(8), u64(2), true)))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_fsync(), u32(0), u64(0), u32(0), u32(0), u64(3), false)))
  n: u32 = io.io_wait(ring, requests, completions, region, u32(2))
  assert(n == u32(2))
  w: u32 = find_tag(completions, n, u64(2))
  f: u32 = find_tag(completions, n, u64(3))
  assert(w < n && f < n)
  assert(completions[w].error == u32(0) && completions[w].result == u32(8))
  assert(completions[f].error == u32(0))
  // along the chain the write completes first
  assert(w < f)

  // pread back (tag 4)
  c: io.IoCompletion = io.io_pread_sync(ring, requests, completions, region, u32(0), u64(0), io.io_buffer(u32(64), u32(8)), u64(4))
  assert(c.tag == u64(4) && c.error == u32(0) && c.result == u32(8))
  i = u32(0)
  while i < u32(8) {
    assert(region[u32(64) + i] == u8_trunc_u32(i + u32(1)))
    i = i + u32(1)
  }

  // a read past the end is short (tag 5)
  c = io.io_pread_sync(ring, requests, completions, region, u32(0), u64(8), io.io_buffer(u32(80), u32(8)), u64(5))
  assert(c.error == u32(0) && c.result == u32(0))

  // a read from an unopened slot is Closed (tag 6)
  c = io.io_pread_sync(ring, requests, completions, region, u32(1), u64(0), io.io_buffer(u32(80), u32(8)), u64(6))
  assert(c.error == io.io_err_closed())

  // directory sync (tag 7) and close (tag 8)
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_fsyncdir(), u32(0), u64(0), u32(96), u32(2), u64(7), false)))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_close(), u32(0), u64(0), u32(0), u32(0), u64(8), false)))
  n = io.io_wait(ring, requests, completions, region, u32(2))
  assert(n == u32(2))
  assert(completions[find_tag(completions, n, u64(7))].error == u32(0))
  assert(completions[find_tag(completions, n, u64(8))].error == u32(0))
  assert(ring[0].submitted == u32(8) && ring[0].completed == u32(8) && ring[0].pending == u32(0))
  42
}
`

// ioPortModule lays the consumer down as a module whose manifest selects
// the realization: the only line that differs between the two builds.
func ioPortModule(t *testing.T, realization string) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"oak.mod":  "module example.com/io_port_check\noak 0.1.0\nreplace io => " + realization + "\n",
		"main.oak": ioPortConsumer,
	})
}

func TestE2EIoPortSimulated(t *testing.T) {
	model, err := New().WithPackageDir(ioPortModule(t, "iosim")).Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	result := evaluator.Eval(model.Tree.Root, env)
	if e, isErr := result.(*object.Error); isErr {
		t.Fatalf("interpreter error evaluating program: %s", e.Message)
	}
	call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
	result = evaluator.Eval(call, env)
	if e, isErr := result.(*object.Error); isErr {
		t.Fatalf("interpreter error in main(): %s", e.Message)
	}
	integer, ok := result.(*object.Integer)
	if !ok || integer.Value != 42 {
		t.Fatalf("main() returned %s, want 42", result.Inspect())
	}
}

func TestE2EIoPortNative(t *testing.T) {
	shim, err := filepath.Abs(filepath.Join("..", "stdlib", "native", "oak_io_host.c"))
	if err != nil {
		t.Fatal(err)
	}
	os.Remove("oak_io_t.bin")
	defer os.Remove("oak_io_t.bin")
	_, code, abnormal := buildAndRunFrom(t, "ioport", New().WithPackageDir(ioPortModule(t, "ionative")), shim)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A Sim test package rejects the native realization: its externs are
// undeclared there, so the operating system cannot be linked into a
// simulation by mistake.
func TestE2EIoPortNativeRejectedInSimulation(t *testing.T) {
	_, err := New().WithPackageDir(ioPortModule(t, "ionative")).WithSimulation(nil).Check().Get()
	if err == nil {
		t.Fatal("the native realization must be rejected under the simulation profile")
	}
}
