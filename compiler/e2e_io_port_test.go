package compiler

import (
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
// syncs the directory, and closes; then exercises the directory and
// metadata operations — exclusive create and its Exists, stat, truncate
// both ways, rename, readdir, unlink. Both realizations must complete every
// tag with the same results and errors (order is unordered except along
// the link chain, which the consumer checks by tag).
const ioPortConsumer = `package main
import(std)
import("io")

// "oak_io_t.bin" followed by NUL at 0, "." followed by NUL at 96 and at
// 160, "oak_io_a.bin" NUL at 128 and "oak_io_b.bin" NUL at 141 (so the
// rename window is [128, 154) split at 13).
io_path: (region: [*]u8): () {
  bytes: [13]u8 = [u8(111), u8(97), u8(107), u8(95), u8(105), u8(111), u8(95), u8(116), u8(46), u8(98), u8(105), u8(110), u8(0)]
  i: u32 = u32(0)
  while i < u32(13) {
    region[i] = bytes[i]
    region[u32(128) + i] = bytes[i]
    region[u32(141) + i] = bytes[i]
    i = i + u32(1)
  }
  region[135] = u8(97)
  region[148] = u8(98)
  region[96] = u8(46)
  region[97] = u8(0)
  region[160] = u8(46)
  region[161] = u8(0)
}

// Whether the NUL-separated names in region[start, start + n) include the
// name at region[name_base, name_base + name_len) (NUL included).
lists_name: (region: [*]u8, start: u32, n: u32, name_base: u32, name_len: u32): Bool {
  found: Bool = false
  at: u32 = start
  while at < start + n && !found {
    i: u32 = u32(0)
    same: Bool = true
    while same && i < name_len && at + i < start + n {
      same = region[at + i] == region[name_base + i]
      i = i + u32(1)
    }
    same && i == name_len ? { found = true }
    while at < start + n && region[at] != u8(0) {
      at = at + u32(1)
    }
    at = at + u32(1)
  }
  found
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
  region_store: [256]u8
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

  // exclusive create of A into slot 0 (tag 9); a second create is Exists (tag 10)
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_create(), u32(0), u64(0), u32(128), u32(13), u64(9), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0) && completions[0].result == u32(0))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_create(), u32(1), u64(0), u32(128), u32(13), u64(10), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == io.io_err_exists())

  // write eight bytes (tag 11); stat says eight, in the result and in the window (tag 12)
  c = io.io_pwrite_sync(ring, requests, completions, region, u32(0), u64(0), io.io_buffer(u32(32), u32(8)), u64(11))
  assert(c.error == u32(0) && c.result == u32(8))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_stat(), u32(0), u64(0), u32(64), u32(8), u64(12), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0) && completions[0].result == u32(8))
  assert(region[64] == u8(8) && region[65] == u8(0) && region[71] == u8(0))

  // truncate to four (tag 13): stat says four (tag 14), a read is short with the first four bytes (tag 15)
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_truncate(), u32(0), u64(4), u32(0), u32(0), u64(13), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_stat(), u32(0), u64(0), u32(0), u32(0), u64(14), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0) && completions[0].result == u32(4))
  c = io.io_pread_sync(ring, requests, completions, region, u32(0), u64(0), io.io_buffer(u32(80), u32(8)), u64(15))
  assert(c.error == u32(0) && c.result == u32(4))
  assert(region[80] == u8(1) && region[83] == u8(4))

  // truncate up to six (tag 16): the tail reads as zeros (tag 17)
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_truncate(), u32(0), u64(6), u32(0), u32(0), u64(16), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0))
  region[84] = u8(9)
  region[85] = u8(9)
  c = io.io_pread_sync(ring, requests, completions, region, u32(0), u64(0), io.io_buffer(u32(80), u32(8)), u64(17))
  assert(c.error == u32(0) && c.result == u32(6))
  assert(region[83] == u8(4) && region[84] == u8(0) && region[85] == u8(0))

  // close A (tag 18); rename A to B (tag 19); create B is Exists (tag 20); unlink A is NotFound (tag 21)
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_close(), u32(0), u64(0), u32(0), u32(0), u64(18), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_rename(), u32(0), u64(13), u32(128), u32(26), u64(19), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_create(), u32(0), u64(0), u32(141), u32(13), u64(20), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == io.io_err_exists())
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_unlink(), u32(0), u64(0), u32(128), u32(13), u64(21), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == io.io_err_not_found())

  // readdir of "." (tag 22): the window is "." then the output; B is listed, A is not
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_readdir(), u32(0), u64(2), u32(160), u32(96), u64(22), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0) && completions[0].result > u32(0))
  listed: u32 = completions[0].result
  assert(lists_name(region, u32(162), listed, u32(141), u32(13)))
  assert(!lists_name(region, u32(162), listed, u32(128), u32(13)))

  // unlink B (tag 23), then create B again succeeds (tag 24), close (tag 25), unlink (tag 26)
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_unlink(), u32(0), u64(0), u32(141), u32(13), u64(23), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_create(), u32(0), u64(0), u32(141), u32(13), u64(24), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  assert(completions[0].error == u32(0))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_close(), u32(0), u64(0), u32(0), u32(0), u64(25), false)))
  assert(io.io_submit(ring, requests, io.io_request(io.io_op_unlink(), u32(0), u64(0), u32(141), u32(13), u64(26), false)))
  assert(io.io_wait(ring, requests, completions, region, u32(2)) == u32(2))
  assert(completions[find_tag(completions, u32(2), u64(25))].error == u32(0))
  assert(completions[find_tag(completions, u32(2), u64(26))].error == u32(0))
  assert(ring[0].submitted == u32(26) && ring[0].completed == u32(26) && ring[0].pending == u32(0))
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
	// The consumer names files in its working directory and lists it, so
	// it runs in a directory of its own.
	module := ioPortModule(t, "ionative")
	t.Chdir(t.TempDir())
	_, code, abnormal := buildAndRunFrom(t, "ioport", New().WithPackageDir(module), shim)
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
