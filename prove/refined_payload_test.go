package prove

import (
	"strings"
	"testing"
)

// A replication protocol whose payloads are refinements (docs/spec/
// 112-protocols.md section 1): the prover enumerates exactly the admitted
// values — two replicas, two operations, three commit counts — so the
// reachable graph is small and the agreement and commit invariants are
// decided on it. The same protocol over bare u8 payloads has 66304 step
// values and is refused before any is built, with the remedy named.
const refinedReplSource = `
import(std)
Replica: type = u8 where value < u8(2)
Op: type = u8 where value < u8(2)
Count: type = u8 where value <= u8(2)
ReplicaLog: type = struct { entries: [2]u8, len: u8 }
Prepare: type = struct { replica: Replica, op: Op }
Repl: protocol = {
  data { logs: [2]ReplicaLog, commit: [2]u8 }
  init { logs: [2]ReplicaLog{ ReplicaLog { entries: [2]u8{ 0, 0 }, len: u8(0) }, ReplicaLog { entries: [2]u8{ 0, 0 }, len: u8(0) } }, commit: [2]u8{ 0, 0 } }
  initial Normal
  request(op: Op): Normal -> Normal when data.logs[u32(0)].len < u8(2) then { data.logs[u32(0)].entries[u32(data.logs[u32(0)].len)] = u8(op); data.logs[u32(0)].len = data.logs[u32(0)].len + u8(1) }
  prepare(p: Prepare): Normal -> Normal when p.replica != u8(0) && data.logs[u32(p.replica)].len < data.logs[u32(0)].len then { data.logs[u32(p.replica)].entries[u32(data.logs[u32(p.replica)].len)] = data.logs[u32(0)].entries[u32(data.logs[u32(p.replica)].len)]; data.logs[u32(p.replica)].len = data.logs[u32(p.replica)].len + u8(1) }
  commit(n: Count): Normal -> Normal when n > data.commit[u32(0)] && n <= data.logs[u32(0)].len && data.logs[u32(1)].len >= n then { data.commit[u32(0)] = u8(n) }
  learn(n: Count): Normal -> Normal when n <= data.commit[u32(0)] && n <= data.logs[u32(1)].len && n > data.commit[u32(1)] then { data.commit[u32(1)] = u8(n) }
}
agreement: theorem (s: ReplState, d: ReplData) {
  ok: Bool = true
  a: u32 = 0
  while a < u32(2) {
    b: u32 = 0
    while b < u32(2) {
      bound: u8 = d.commit[a] < d.commit[b] ? d.commit[a] | d.commit[b]
      i: u32 = 0
      while i < u32(bound) {
        ok = ok && d.logs[a].entries[i] == d.logs[b].entries[i]
        i = i + u32(1)
      }
      b = b + u32(1)
    }
    a = a + u32(1)
  }
  ok
}
commit_leq_op: theorem (s: ReplState, d: ReplData) = d.commit[u32(0)] <= d.logs[u32(0)].len && d.commit[u32(1)] <= d.logs[u32(1)].len
main: (): i32 = 0
`

func TestRefinedPayloadsDecideAgreement(t *testing.T) {
	results, err := Theorems(check(t, refinedReplSource), 0)
	if err != nil {
		t.Fatal(err)
	}
	found := 0
	for _, r := range results {
		if r.Name == "agreement" || r.Name == "commit_leq_op" {
			found++
			if r.Status != Decided || !strings.Contains(r.Detail, "49 reachable states") {
				t.Fatalf("%s: %s (%s)", r.Name, r.Status, r.Detail)
			}
		}
	}
	if found != 2 {
		t.Fatalf("expected both invariants, results: %v", results)
	}
}

func TestWidePayloadsRefusedBeforeEnumeration(t *testing.T) {
	wide := strings.NewReplacer(
		"Replica: type = u8 where value < u8(2)\n", "",
		"Op: type = u8 where value < u8(2)\n", "",
		"Count: type = u8 where value <= u8(2)\n", "",
		"replica: Replica, op: Op", "replica: u8, op: u8",
		"request(op: Op)", "request(op: u8)",
		"commit(n: Count)", "commit(n: u8)",
		"learn(n: Count)", "learn(n: u8)",
		"p.replica != u8(0) &&", "u32(p.replica) < u32(2) && p.replica != u8(0) &&",
	).Replace(refinedReplSource)
	results, err := Theorems(check(t, wide), 0)
	if err != nil {
		t.Fatal(err)
	}
	for _, r := range results {
		if r.Name == "agreement" {
			if r.Status != Open || !strings.Contains(r.Detail, "step values exceed") || !strings.Contains(r.Detail, "refine the payload types") {
				t.Fatalf("agreement over u8 payloads: %s (%s)", r.Status, r.Detail)
			}
			return
		}
	}
	t.Fatalf("no result for agreement: %v", results)
}
