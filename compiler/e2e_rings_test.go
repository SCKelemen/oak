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

// The rings package (stdlib/rings.oak; docs/spec/65-machine-memory.md §1,
// dbs ask 8): SPSC and MPSC rings over caller-owned storage as consumers of
// the memory model. Sequentially, both rings are FIFO, refuse a push when
// full, answer None when empty, and wrap their positions (Oak.Rings.
// pop_returns_pushed, count_le_cap, wrapped_difference); the interpreter
// and the compiled program agree on the checksum.
const ringsSequentialProgram = `package main

import("rings")

main: (): i32 {
  state: [1]rings.SpscCursor
  data: [4]u32
  cursor: [*]rings.SpscCursor = span(&state)
  storage: [*]u32 = span(&data)
  acc: u32 = 0
  round: u32 = 0
  while round < u32(100) {
    assert(rings.spsc_push[u32](cursor, storage, round * u32(3) + u32(1)))
    assert(rings.spsc_push[u32](cursor, storage, round * u32(3) + u32(2)))
    assert(rings.spsc_push[u32](cursor, storage, round * u32(3) + u32(3)))
    assert(rings.spsc_count(cursor) == u32(3))
    a: u32 = option_or[u32](rings.spsc_pop[u32](cursor, storage), u32(0))
    assert(a == round * u32(3) + u32(1))
    assert(rings.spsc_push[u32](cursor, storage, u32(77)))
    assert(rings.spsc_push[u32](cursor, storage, u32(78)))
    // four items fill the ring of four; the fifth is refused unchanged
    assert(!rings.spsc_push[u32](cursor, storage, u32(79)))
    assert(rings.spsc_count(cursor) == u32(4))
    b: u32 = option_or[u32](rings.spsc_pop[u32](cursor, storage), u32(0))
    c: u32 = option_or[u32](rings.spsc_pop[u32](cursor, storage), u32(0))
    d: u32 = option_or[u32](rings.spsc_pop[u32](cursor, storage), u32(0))
    e: u32 = option_or[u32](rings.spsc_pop[u32](cursor, storage), u32(0))
    assert(b == round * u32(3) + u32(2) && c == round * u32(3) + u32(3) && d == u32(77) && e == u32(78))
    assert(option_or[u32](rings.spsc_pop[u32](cursor, storage), u32(0)) == u32(0))
    acc = acc * u32(31) + a + b + c + d + e
    round = round + 1
  }
  mstate: [1]rings.MpscCursor
  mseqs: [8]Atomic[u32]
  mdata: [8]u32
  mcursor: [*]rings.MpscCursor = span(&mstate)
  mseqv: [*]Atomic[u32] = span(&mseqs)
  mstorage: [*]u32 = span(&mdata)
  rings.mpsc_init(mcursor, mseqv)
  round = u32(0)
  while round < u32(50) {
    k: u32 = 0
    while k < u32(8) {
      assert(rings.mpsc_push[u32](mcursor, mseqv, mstorage, round * u32(8) + k))
      k = k + 1
    }
    assert(!rings.mpsc_push[u32](mcursor, mseqv, mstorage, u32(99)))
    k = u32(0)
    while k < u32(8) {
      assert(option_or[u32](rings.mpsc_pop[u32](mcursor, mseqv, mstorage), u32(4000000000)) == round * u32(8) + k)
      k = k + 1
    }
    assert(option_or[u32](rings.mpsc_pop[u32](mcursor, mseqv, mstorage), u32(5)) == u32(5))
    round = round + 1
  }
  qstate: [1]rings.MpmcCursor
  qseqs: [8]Atomic[u32]
  qdata: [8]u32
  qcursor: [*]rings.MpmcCursor = span(&qstate)
  qseqv: [*]Atomic[u32] = span(&qseqs)
  qstorage: [*]u32 = span(&qdata)
  rings.mpmc_init(qcursor, qseqv)
  round = u32(0)
  while round < u32(50) {
    k: u32 = 0
    while k < u32(8) {
      assert(rings.mpmc_push[u32](qcursor, qseqv, qstorage, round * u32(8) + k))
      k = k + 1
    }
    assert(!rings.mpmc_push[u32](qcursor, qseqv, qstorage, u32(99)))
    k = u32(0)
    while k < u32(8) {
      assert(option_or[u32](rings.mpmc_pop[u32](qcursor, qseqv, qstorage), u32(4000000000)) == round * u32(8) + k)
      k = k + 1
    }
    assert(option_or[u32](rings.mpmc_pop[u32](qcursor, qseqv, qstorage), u32(5)) == u32(5))
    round = round + 1
  }
  istate: [1]rings.IntrusiveCursor
  inodes: [5]rings.IntrusiveNode
  icursor: [*]rings.IntrusiveCursor = span(&istate)
  inodev: [*]rings.IntrusiveNode = span(&inodes)
  rings.intrusive_init(icursor, inodev)
  taken: u32 = 0
  round = u32(0)
  while round < u32(30) {
    // nodes 1..4 go in, come back in order, and are pushed again
    rings.intrusive_push(icursor, inodev, u32(1))
    rings.intrusive_push(icursor, inodev, u32(2))
    rings.intrusive_push(icursor, inodev, u32(3))
    rings.intrusive_push(icursor, inodev, u32(4))
    j: u32 = 1
    while j <= u32(4) {
      got: u32 = rings.intrusive_pop(icursor, inodev) ?
        | .Item(id) => id
        | .Empty => u32(100)
        | .Busy => u32(200)
      assert(got == j)
      taken = taken + got
      j = j + 1
    }
    sawEmpty: Bool = rings.intrusive_pop(icursor, inodev) ?
      | .Empty => true
      | .Item(id) => false
      | .Busy => false
    assert(sawEmpty)
    round = round + 1
  }
  assert(taken == u32(300))
  i32_bits_u32(acc % u32(200))
}
`

func ringsModule(t *testing.T, program string) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"oak.mod":  "module example.com/rings_check\noak 0.1.0\n",
		"main.oak": program,
	})
}

func TestE2ERingsSequential(t *testing.T) {
	want := interpretModule(t, ringsModule(t, ringsSequentialProgram))
	exit, abnormal := buildPackageAndRun(t, New().WithPackageDir(ringsModule(t, ringsSequentialProgram)))
	if abnormal || int64(exit) != want {
		t.Fatalf("interpreter %d, compiled exit %d abnormal %v", want, exit, abnormal)
	}
}

// ringsThreadedProgram exports the producer and consumer loops over rings
// the caller owns: the C harness below holds the cursors and the storage
// in static arrays, hands them in as spans, and runs the loops on pthreads.
const ringsThreadedProgram = `package main

import("rings")

pub spsc_produce: (cursor: [*]rings.SpscCursor, storage: [*]u32, n: u32): u32 {
  i: u32 = 0
  spins: u32 = 0
  while i < n {
    rings.spsc_push[u32](cursor, storage, i + u32(1)) ? { i = i + 1 } | { spins = spins + 1 }
  }
  spins
}

// Every item arrives in push order (Oak.Rings.pop_returns_pushed); the sum
// of 1..n is the checksum.
pub spsc_consume: (cursor: [*]rings.SpscCursor, storage: [*]u32, n: u32): u64 {
  expect: u32 = 1
  sum: u64 = 0
  while expect <= n {
    v: u32 = option_or[u32](rings.spsc_pop[u32](cursor, storage), u32(0))
    v == u32(0) ? {
      sum = sum
    } | {
      assert(v == expect)
      sum = sum + u64(v)
      expect = expect + 1
    }
  }
  sum
}

pub mpsc_setup: (cursor: [*]rings.MpscCursor, seqs: [*]Atomic[u32]): () {
  rings.mpsc_init(cursor, seqs)
}

// Producer id pushes id << 24 | k for k in 1..n.
pub mpsc_produce: (cursor: [*]rings.MpscCursor, seqs: [*]Atomic[u32], storage: [*]u32, id: u32, n: u32): u32 {
  k: u32 = 1
  spins: u32 = 0
  while k <= n {
    rings.mpsc_push[u32](cursor, seqs, storage, (id << u32(24)) | k) ? { k = k + 1 } | { spins = spins + 1 }
  }
  spins
}

// Each producer's items arrive in its own order; the checksum is the sum
// of every k.
pub mpsc_consume: (cursor: [*]rings.MpscCursor, seqs: [*]Atomic[u32], storage: [*]u32, total: u32): u64 {
  last: [16]u32
  taken: u32 = 0
  sum: u64 = 0
  while taken < total {
    v: u32 = option_or[u32](rings.mpsc_pop[u32](cursor, seqs, storage), u32(0))
    v == u32(0) ? {
      sum = sum
    } | {
      id: u32 = v >> u32(24)
      k: u32 = v & u32(16777215)
      assert(id < u32(16))
      assert(k == last[id] + u32(1))
      last[id] = k
      sum = sum + u64(k)
      taken = taken + 1
    }
  }
  sum
}

pub mpmc_setup: (cursor: [*]rings.MpmcCursor, seqs: [*]Atomic[u32]): () {
  rings.mpmc_init(cursor, seqs)
}

pub mpmc_produce: (cursor: [*]rings.MpmcCursor, seqs: [*]Atomic[u32], storage: [*]u32, id: u32, n: u32): u32 {
  k: u32 = 1
  spins: u32 = 0
  while k <= n {
    rings.mpmc_push[u32](cursor, seqs, storage, (id << u32(24)) | k) ? { k = k + 1 } | { spins = spins + 1 }
  }
  spins
}

// A consumer takes total items whatever their producers; each producer's
// items still reach the consumers in that producer's order, so a consumer
// sees its share of every producer's sequence strictly increasing.
pub mpmc_consume: (cursor: [*]rings.MpmcCursor, seqs: [*]Atomic[u32], storage: [*]u32, total: u32): u64 {
  last: [16]u32
  taken: u32 = 0
  sum: u64 = 0
  while taken < total {
    v: u32 = option_or[u32](rings.mpmc_pop[u32](cursor, seqs, storage), u32(0))
    v == u32(0) ? {
      sum = sum
    } | {
      id: u32 = v >> u32(24)
      k: u32 = v & u32(16777215)
      assert(id < u32(16))
      assert(k > last[id])
      last[id] = k
      sum = sum + u64(k)
      taken = taken + 1
    }
  }
  sum
}

pub intrusive_setup: (cursor: [*]rings.IntrusiveCursor, nodes: [*]rings.IntrusiveNode): () {
  rings.intrusive_init(cursor, nodes)
}

// Producer id owns nodes first..first+n-1 and writes each payload before
// pushing the node (the link's release publishes it).
pub intrusive_produce: (cursor: [*]rings.IntrusiveCursor, nodes: [*]rings.IntrusiveNode, values: [*]u32, first: u32, n: u32): () {
  k: u32 = 0
  while k < n {
    values[first + k] = (first + k) * u32(2654435761)
    rings.intrusive_push(cursor, nodes, first + k)
    k = k + 1
  }
}

// The consumer takes total nodes: each payload matches its node, and no
// node is taken twice (the consumer clears the payload as it goes).
pub intrusive_consume: (cursor: [*]rings.IntrusiveCursor, nodes: [*]rings.IntrusiveNode, values: [*]u32, total: u32): u64 {
  taken: u32 = 0
  sum: u64 = 0
  busy: u64 = 0
  while taken < total {
    got: u32 = rings.intrusive_pop(cursor, nodes) ?
      | .Item(id) => id
      | .Empty => u32(0)
      | .Busy => u32(0)
    got == u32(0) ? {
      busy = busy + 1
    } | {
      assert(values[got] == got * u32(2654435761))
      values[got] = u32(0)
      sum = sum + u64(got)
      taken = taken + 1
    }
  }
  sum
}
`

const ringsHarness = `
#include <pthread.h>
#include <stdio.h>
#define N 200000u
#define P 4
static oak_rings__SpscCursor spsc_state[1];
static u32 spsc_data[256];
static oak_rings__MpscCursor mpsc_state[1];
static __typeof__(*((oak_span_Atomic_u32 *)0)->base) mpsc_seqs[64];
static u32 mpsc_data[64];
#define SPSC (oak_span_oak_rings_SpscCursor){ spsc_state, 1 }, (oak_span_u32){ spsc_data, 256 }
#define MPSC (oak_span_oak_rings_MpscCursor){ mpsc_state, 1 }, (oak_span_Atomic_u32){ mpsc_seqs, 64 }, (oak_span_u32){ mpsc_data, 64 }
static void *spsc_prod(void *a) { (void)a; oak_spsc_produce(SPSC, N); return NULL; }
static void *spsc_cons(void *a) { *(u64 *)a = oak_spsc_consume(SPSC, N); return NULL; }
static void *mpsc_prod(void *a) { oak_mpsc_produce(MPSC, (u32)(long)a, N); return NULL; }
static void *mpsc_cons(void *a) { *(u64 *)a = oak_mpsc_consume(MPSC, N * P); return NULL; }
#define M 100000u
static oak_rings__MpmcCursor mpmc_state[1];
static __typeof__(*((oak_span_Atomic_u32 *)0)->base) mpmc_seqs[64];
static u32 mpmc_data[64];
#define MPMC (oak_span_oak_rings_MpmcCursor){ mpmc_state, 1 }, (oak_span_Atomic_u32){ mpmc_seqs, 64 }, (oak_span_u32){ mpmc_data, 64 }
static void *mpmc_prod(void *a) { oak_mpmc_produce(MPMC, (u32)(long)a, N); return NULL; }
static void *mpmc_cons(void *a) { *(u64 *)a = oak_mpmc_consume(MPMC, N); return NULL; }
static oak_rings__IntrusiveCursor intr_state[1];
static oak_rings__IntrusiveNode intr_nodes[1 + P * M];
static u32 intr_values[1 + P * M];
#define INTR_QUEUE (oak_span_oak_rings_IntrusiveCursor){ intr_state, 1 }, (oak_span_oak_rings_IntrusiveNode){ intr_nodes, 1 + P * M }
#define INTR INTR_QUEUE, (oak_span_u32){ intr_values, 1 + P * M }
static void *intrusive_prod(void *a) { oak_intrusive_produce(INTR, (u32)(long)a * M + 1, M); return NULL; }
static void *intrusive_cons(void *a) { *(u64 *)a = oak_intrusive_consume(INTR, P * M); return NULL; }
int main(void) {
  pthread_t p, c, ps[P];
  u64 sum = 0;
  if (pthread_create(&c, NULL, spsc_cons, &sum) != 0) return 20;
  if (pthread_create(&p, NULL, spsc_prod, NULL) != 0) return 21;
  pthread_join(p, NULL); pthread_join(c, NULL);
  if (sum != (u64)N * (N + 1) / 2) { printf("spsc sum %llu\\n", (unsigned long long)sum); return 1; }
  oak_mpsc_setup((oak_span_oak_rings_MpscCursor){ mpsc_state, 1 }, (oak_span_Atomic_u32){ mpsc_seqs, 64 });
  sum = 0;
  if (pthread_create(&c, NULL, mpsc_cons, &sum) != 0) return 22;
  for (long i = 0; i < P; i++) if (pthread_create(&ps[i], NULL, mpsc_prod, (void *)(i + 1)) != 0) return 23;
  for (int i = 0; i < P; i++) pthread_join(ps[i], NULL);
  pthread_join(c, NULL);
  if (sum != (u64)P * ((u64)N * (N + 1) / 2)) { printf("mpsc sum %llu\\n", (unsigned long long)sum); return 2; }
  oak_mpmc_setup((oak_span_oak_rings_MpmcCursor){ mpmc_state, 1 }, (oak_span_Atomic_u32){ mpmc_seqs, 64 });
  u64 sums[P] = {0};
  pthread_t cs[P];
  for (long i = 0; i < P; i++) if (pthread_create(&cs[i], NULL, mpmc_cons, &sums[i]) != 0) return 24;
  for (long i = 0; i < P; i++) if (pthread_create(&ps[i], NULL, mpmc_prod, (void *)(i + 1)) != 0) return 25;
  for (int i = 0; i < P; i++) pthread_join(ps[i], NULL);
  sum = 0;
  for (int i = 0; i < P; i++) { pthread_join(cs[i], NULL); sum += sums[i]; }
  if (sum != (u64)P * ((u64)N * (N + 1) / 2)) { printf("mpmc sum %llu\\n", (unsigned long long)sum); return 3; }
  oak_intrusive_setup(INTR_QUEUE);
  sum = 0;
  if (pthread_create(&c, NULL, intrusive_cons, &sum) != 0) return 26;
  for (long i = 0; i < P; i++) if (pthread_create(&ps[i], NULL, intrusive_prod, (void *)i) != 0) return 27;
  for (int i = 0; i < P; i++) pthread_join(ps[i], NULL);
  pthread_join(c, NULL);
  if (sum != (u64)(P * M) * ((u64)(P * M) + 1) / 2) { printf("intrusive sum %llu\\n", (unsigned long long)sum); return 4; }
  printf("rings ok\\n");
  return 0;
}
`

// runRingsHarness compiles the threaded program's C with the harness's
// main and runs it; the exit code is the harness's verdict.
func runRingsHarness(t *testing.T, name string, ccFlags ...string) (string, int) {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	code, err := New().WithPackageDir(ringsModule(t, ringsThreadedProgram)).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	cPath := filepath.Join(dir, name+".c")
	binPath := filepath.Join(dir, name)
	if err := os.WriteFile(cPath, []byte(code+ringsHarness), 0o644); err != nil {
		t.Fatal(err)
	}
	args := append([]string{"-std=c11", "-O2", "-pthread", "-Wno-parentheses-equality"}, ccFlags...)
	args = append(args, "-o", binPath, cPath)
	if out, err := exec.Command(cc, args...).CombinedOutput(); err != nil {
		if len(ccFlags) > 0 {
			t.Skipf("cc does not accept %v: %s", ccFlags, out)
		}
		t.Fatalf("cc: %v\n%s", err, out)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 120*time.Second)
	defer cancel()
	run := exec.CommandContext(ctx, binPath)
	out, err := run.CombinedOutput()
	if ctx.Err() == context.DeadlineExceeded {
		t.Fatalf("%s did not finish (a lost wakeup or a stuck ring):\n%s", name, out)
	}
	if err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			return string(out), exitErr.ExitCode()
		}
		t.Fatal(err)
	}
	return string(out), 0
}

// Two threads through the SPSC ring and five through the MPSC ring: every
// item arrives, in each producer's order, with the expected checksum.
func TestE2ERingsThreaded(t *testing.T) {
	out, code := runRingsHarness(t, "rings_threads")
	if code != 0 || !strings.Contains(out, "rings ok") {
		t.Fatalf("exit %d:\n%s", code, out)
	}
}

// The same run under ThreadSanitizer: the release/acquire pairs the rings
// rely on (Oak.Rings.spsc_payload_race_free, spsc_reuse_race_free,
// mpsc_payload_race_free) are what keeps the slot accesses race-free, and
// TSan reports any pair they fail to order. Skips where cc lacks it.
func TestE2ERingsThreadSanitizer(t *testing.T) {
	out, code := runRingsHarness(t, "rings_tsan", "-fsanitize=thread", "-g", "-O1")
	if code != 0 || !strings.Contains(out, "rings ok") || strings.Contains(out, "WARNING: ThreadSanitizer") {
		t.Fatalf("exit %d:\n%s", code, out)
	}
}

// The borrow admits exactly writable spans of cells or of records holding
// cells (docs/spec/65-machine-memory.md §1): a view cannot carry a cell, an
// element cannot be copied out of the span, and a record holding cells
// still cannot be passed by value.
func TestRingsAtomicBorrowRules(t *testing.T) {
	head := "Cursor: type = struct {\n  tail: Atomic[u32]\n  n: u32\n}\n"
	for name, c := range map[string][2]string{
		"view of cells":      {"f: (cells: []Atomic[u32]): u32 { atomic_load_relaxed(cells[0]) }\nmain: (): u32 { 0 }\n", "borrow it as a span"},
		"record by value":    {head + "f: (c: Cursor): u32 { atomic_load_relaxed(c.tail) }\nmain: (): u32 { 0 }\n", "borrow it as a span"},
		"element copied out": {head + "f: (c: [*]Cursor): u32 {\n  local: Cursor = c[0]\n  local.n\n}\nmain: (): u32 { 0 }\n", "zero-initialized at declaration"},
	} {
		_, err := New().WithSource(name+".oak", c[0]).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c[1]) {
			t.Errorf("%s: %v", name, err)
		}
	}
	accepted := head + "bump: (c: [*]Cursor, cells: [*]Atomic[u32]): u32 {\n  atomic_store_release(c[0].tail, atomic_load_relaxed(cells[0]) + u32(1))\n  atomic_fetch_add_relaxed(cells[0], u32(1))\n}\nmain: (): u32 {\n  state: [1]Cursor\n  cells: [2]Atomic[u32]\n  bump(span(&state), span(&cells)) + bump(span(&state), span(&cells)) + atomic_load_relaxed(state[0].tail)\n}\n"
	if got := interpretChecked(t, accepted); got != 3 {
		t.Fatalf("interpreter: %d, want 3", got)
	}
	if _, exit, abnormal := buildAndRunOutput(t, "rings_borrow", accepted); abnormal || exit != 3 {
		t.Fatalf("compiled: exit %d abnormal %v, want 3", exit, abnormal)
	}
}
