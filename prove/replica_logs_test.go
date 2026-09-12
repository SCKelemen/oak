package prove

import (
	"strings"
	"testing"
)

// The log-agreement invariant of a replication protocol with per-replica
// logs (docs/spec/112-protocols.md section 1; the dbs pilot's ask 2) is an
// ordinary theorem over the projection: every replica's log is a prefix of
// the leader's. The inductive step cannot be enumerated — the data record
// is far too wide — so the prover decides it on the reachable states.
func TestLogAgreementOnReachableStates(t *testing.T) {
	src := `
import(std)
Entry: type = struct { value: u8 }
Replica: type = struct { log: [3]u8, len: u8 }
Repl: protocol = {
  data { leader: Replica, replicas: [2]Replica }
  init { leader: Replica { log: [3]u8{ 0, 0, 0 }, len: u8(0) }, replicas: [2]Replica{ Replica { log: [3]u8{ 0, 0, 0 }, len: u8(0) }, Replica { log: [3]u8{ 0, 0, 0 }, len: u8(0) } } }
  initial Normal
  propose(e: Entry): Normal -> Normal when u32(e.value) < u32(4) && u32(data.leader.len) < u32(3) then { data.leader.log[u32(data.leader.len)] = e.value; data.leader.len = data.leader.len + u8(1) }
  replicate(who: u8): Normal -> Normal when u32(who) < u32(2) && data.replicas[u32(who)].len < data.leader.len then { data.replicas[u32(who)].log[u32(data.replicas[u32(who)].len)] = data.leader.log[u32(data.replicas[u32(who)].len)]; data.replicas[u32(who)].len = data.replicas[u32(who)].len + u8(1) }
}

agree: theorem (s: ReplState, d: ReplData) {
  ok: Bool = u32(d.replicas[u32(0)].len) <= u32(d.leader.len) && u32(d.replicas[u32(1)].len) <= u32(d.leader.len)
  i: u32 = 0
  while i < u32(2) {
    k: u32 = 0
    while k < u32(d.replicas[i].len) && k < u32(3) {
      ok = ok && d.replicas[i].log[k] == d.leader.log[k]
      k = k + u32(1)
    }
    i = i + u32(1)
  }
  ok
}

main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	for _, r := range results {
		if r.Name == "agree" {
			if r.Status != Decided || !strings.Contains(r.Detail, "reachable") {
				t.Fatalf("agree: %s (%s)", r.Status, r.Detail)
			}
			return
		}
	}
	t.Fatalf("no result for agree: %v", results)
}
