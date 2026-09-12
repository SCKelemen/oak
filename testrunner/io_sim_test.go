package testrunner

import (
	"path/filepath"
	"testing"
)

// The simulated IO realization under the runner (docs/spec/120-io.md §4):
// a small log writes records linked to fsyncs through the port over the
// simulated device with torn, dropped and lost-fsync faults enabled, then
// crashes and restarts. The contract of §3 is checked as the WAL scenario
// states it: every record whose fsync completed is recovered when the
// file's blocks are trusted, and the ledger's fault counts drive the
// classification. The tape is the fault schedule, so a failing run shrinks
// to fewer faults and replays exactly.
//
// The directory is part of the contract: the log's file exists after the
// crash only because log_open syncs the directory after opening it (the
// first version of this scenario did not, and the directory model caught
// it), and a segment created exclusively, written, fsynced, renamed to
// its final name and made durable with fsyncdir is found by readdir at
// recovery under its final name, never under the temporary one.
func TestIoSimLogContract(t *testing.T) {
	dir := fixture(t, map[string]string{
		"oak.mod": "module example.com/iolog\noak 0.1.0\n",
		"log/log.oak": `package log

import("iosim")

// Write record k (eight bytes k+1 .. k+8) at offset 8k and fsync it, linked.
log_append: (ring: [*]iosim.IoRing, requests: [*]iosim.IoRequest, completions: [*]iosim.IoCompletion, region: [*]u8, k: u32): Bool {
  i: u32 = u32(0)
  while i < u32(8) {
    region[u32(32) + i] = u8_trunc_u32(k + i + u32(1))
    i = i + u32(1)
  }
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_pwrite(), u32(0), u64(k * u32(8)), u32(32), u32(8), u64(u32(100) + k), true)))
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_fsync(), u32(0), u64(0), u32(0), u32(0), u64(u32(200) + k), false)))
  n: u32 = iosim.io_wait(ring, requests, completions, region, u32(2))
  ok: Bool = n == u32(2)
  i = u32(0)
  while i < n {
    ok = ok && completions[i].error == u32(0)
    i = i + u32(1)
  }
  ok
}

// Open "l" into slot 0, then sync the directory: a file's name is durable
// only after fsyncdir (docs/spec/120-io.md §3).
log_open: (ring: [*]iosim.IoRing, requests: [*]iosim.IoRequest, completions: [*]iosim.IoCompletion, region: [*]u8): Bool {
  region[0] = u8(108)
  region[1] = u8(0)
  region[2] = u8(46)
  region[3] = u8(0)
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_open(), u32(0), u64(0), u32(0), u32(2), u64(1), false)))
  ok: Bool = iosim.io_wait(ring, requests, completions, region, u32(1)) == u32(1) && completions[0].error == u32(0)
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_fsyncdir(), u32(0), u64(0), u32(2), u32(2), u64(2), false)))
  ok && iosim.io_wait(ring, requests, completions, region, u32(1)) == u32(1) && completions[0].error == u32(0)
}

// A segment: created exclusively as "s.tmp" in slot 1, one record written
// and fsynced (linked), closed, renamed to "s", and the directory synced.
// Region: "s.tmp" NUL at 8..14, "s" NUL at 14..16 (the rename window is
// [8, 16) split at 6), "." NUL at 2.
segment_publish: (ring: [*]iosim.IoRing, requests: [*]iosim.IoRequest, completions: [*]iosim.IoCompletion, region: [*]u8): Bool {
  region[8] = u8(115)
  region[9] = u8(46)
  region[10] = u8(116)
  region[11] = u8(109)
  region[12] = u8(112)
  region[13] = u8(0)
  region[14] = u8(115)
  region[15] = u8(0)
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_create(), u32(1), u64(0), u32(8), u32(6), u64(10), false)))
  ok: Bool = iosim.io_wait(ring, requests, completions, region, u32(1)) == u32(1) && completions[0].error == u32(0)
  i: u32 = u32(0)
  while i < u32(8) {
    region[u32(48) + i] = u8_trunc_u32(u32(200) + i)
    i = i + u32(1)
  }
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_pwrite(), u32(1), u64(0), u32(48), u32(8), u64(11), true)))
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_fsync(), u32(1), u64(0), u32(0), u32(0), u64(12), true)))
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_close(), u32(1), u64(0), u32(0), u32(0), u64(13), true)))
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_rename(), u32(0), u64(6), u32(8), u32(8), u64(14), true)))
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_fsyncdir(), u32(0), u64(0), u32(2), u32(2), u64(15), false)))
  n: u32 = iosim.io_wait(ring, requests, completions, region, u32(5))
  ok = ok && n == u32(5)
  i = u32(0)
  while i < n {
    ok = ok && completions[i].error == u32(0)
    i = i + u32(1)
  }
  ok
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
main: (): i32 = 0
`,
		"log/log_test.oak": `package log

import(testing)
import("iosim")

SimLogRecovery: (data: []u8): () {
  ring_store: [1]iosim.IoRing
  req_store: [8]iosim.IoRequest
  cq_store: [8]iosim.IoCompletion
  region_store: [256]u8
  ring: [*]iosim.IoRing = span(&ring_store)
  requests: [*]iosim.IoRequest = span(&req_store)
  completions: [*]iosim.IoCompletion = span(&cq_store)
  region: [*]u8 = span(&region_store)
  // torn (1), dropped (4), lost fsync (8)
  iosim.io_attach(data, u32(13))
  iosim.io_open_region(ring, region, u32(2))
  test_check(log_open(ring, requests, completions, region), u32(1))
  published: Bool = segment_publish(ring, requests, completions, region)
  acked: u32 = u32(0)
  k: u32 = u32(0)
  while k < u32(3) {
    log_append(ring, requests, completions, region, k) ? { acked = acked + u32(1) } | { }
    k = k + u32(1)
  }
  // The contract applies to a file the ledger trusts before the crash (no
  // dropped write hides behind an acknowledgement) and after it (no torn
  // write or lost fsync on the durable copy).
  trusted_before: Bool = iosim.iosim_trusted(u32(0))
  // Crash and restart: unsynced writes may vanish; synced ones survive on
  // trusted blocks.
  iosim.iosim_crash_at(u64(7))
  test_check(!iosim.iosim_up(), u32(20))
  iosim.iosim_restart()
  test_check(iosim.iosim_up() && iosim.iosim_restarts() == u32(1), u32(21))
  iosim.io_open_region(ring, region, u32(2))
  test_check(log_open(ring, requests, completions, region), u32(2))
  // Recovery lists the directory: the published segment is there under
  // its final name and never under the temporary one, and the log's own
  // file is there because log_open synced the directory.
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_readdir(), u32(0), u64(2), u32(2), u32(126), u64(30), false)))
  test_check(iosim.io_wait(ring, requests, completions, region, u32(1)) == u32(1) && completions[0].error == u32(0), u32(22))
  listed: u32 = completions[0].result
  test_check(lists_name(region, u32(4), listed, u32(0), u32(2)), u32(23))
  test_check(!lists_name(region, u32(4), listed, u32(8), u32(6)), u32(24))
  published ? { test_check(lists_name(region, u32(4), listed, u32(14), u32(2)), u32(25)) } | { }
  test_check(iosim.iosim_max_wait() <= u32(34), u32(26))
  trusted: Bool = trusted_before && iosim.iosim_trusted(u32(0))
  k = u32(0)
  while k < acked {
    c: iosim.IoCompletion = iosim.io_pread_sync(ring, requests, completions, region, u32(0), u64(k * u32(8)), iosim.io_buffer(u32(64), u32(8)), u64(u32(300) + k))
    trusted ? {
      test_check(c.error == u32(0) && c.result == u32(8), u32(3))
      i: u32 = u32(0)
      while i < u32(8) {
        test_check(region[u32(64) + i] == u8_trunc_u32(k + i + u32(1)), u32(4))
        i = i + u32(1)
      }
    } | { }
    k = k + u32(1)
  }
  // The ledger explains the run: every submit has its completion.
  submits: u32 = u32(0)
  completes: u32 = u32(0)
  e: u32 = u32(0)
  while e < iosim.iosim_ledger_len() {
    iosim.iosim_ledger_kind(e) == u64(1) ? { submits = submits + u32(1) } | { completes = completes + u32(1) }
    e = e + u32(1)
  }
  test_check(submits == completes, u32(5))
  iosim.iosim_fault_count(u32(8)) > u32(0) ? { testing_classify(u32(8)) } | { }
  trusted ? { testing_classify(u32(1)) } | { testing_classify(u32(2)) }
}
`,
	})
	code, results, stderr := runCLI(t, "-runs", "64", filepath.Join(dir, "log"))
	if code != 0 || len(results) != 1 || results[0].Status != "pass" {
		t.Fatalf("code %d: %+v\n%s", code, results, stderr)
	}
	if results[0].Cases < 64 {
		t.Fatalf("expected 64 simulated runs, got %d", results[0].Cases)
	}
}
