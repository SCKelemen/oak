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

// Per-replica log data (docs/spec/112-protocols.md section 1; the dbs
// pilot's ask 2, second half): a data field that is a record with an array
// inside, and an array of such records, with paths of any depth in guards
// and effects — data.replicas[who].log[data.replicas[who].len] — projected
// into Oak as they are written, into TLA+ as the same paths and one EXCEPT
// per field, and the log-agreement invariant stated as an ordinary theorem
// over the projection that `oak prove` decides on the reachable states.
const replicaLogsSource = `
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
`

func TestE2EProtocolReplicaLogs(t *testing.T) {
	src := replicaLogsSource + `
main: (): i32 {
  store: [1]ReplData
  data: [*]ReplData = span(&store)
  data[0] = repl_initial_data()
  s: ReplState = repl_initial()
  assert(!repl_legal(s, data[0], .Replicate(u8(0))))
  s = repl_next(s, data, .Propose(Entry { value: u8(3) }))
  s = repl_next(s, data, .Propose(Entry { value: u8(1) }))
  assert(data[0].leader.len == u8(2) && data[0].leader.log[u32(0)] == u8(3) && data[0].leader.log[u32(1)] == u8(1))
  s = repl_next(s, data, .Replicate(u8(1)))
  assert(data[0].replicas[u32(1)].len == u8(1) && data[0].replicas[u32(1)].log[u32(0)] == u8(3) && data[0].replicas[u32(0)].len == u8(0))
  s = repl_next(s, data, .Replicate(u8(1)))
  assert(!repl_legal(s, data[0], .Replicate(u8(1))) && data[0].replicas[u32(1)].log[u32(1)] == u8(1))
  42
}
`
	code, abnormal := buildAndRun(t, "protocol_replica_logs", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}

	tree, err := New().WithSource("repl.oak", replicaLogsSource+"main: (): i32 = 0\n").Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decl := Protocols(tree)[0]
	records := RecordDeclarations(tree.Root)
	module, err := ProtocolTLAWithRecords(decl, "repl.oak", records)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"leader = [log |-> [k \\in 0..2 |-> 0], len |-> 0]",
		"replicas = [k \\in 0..1 |-> [log |-> [k1 \\in 0..2 |-> 0], len |-> 0]]",
		"leader' = [leader EXCEPT !.log[leader.len] = e.value, !.len = (leader.len + 1)]",
		"replicas' = [replicas EXCEPT ![who].log[replicas[who].len] = leader.log[replicas[who].len], ![who].len = (replicas[who].len + 1)]",
		"leader \\in [log: [0..2 -> Nat], len: Nat]",
		"replicas \\in [0..1 -> [log: [0..2 -> Nat], len: Nat]]",
	} {
		if !strings.Contains(module, want) {
			t.Fatalf("module lacks %q:\n%s", want, module)
		}
	}
	if _, _, reason := LocateTLC(); reason != "" {
		t.Skip(reason)
	}
	java, jar, _ := LocateTLC()
	dir := t.TempDir()
	cfg := ProtocolTLCConfigWith(decl, records)
	if err := os.WriteFile(filepath.Join(dir, "Repl.tla"), []byte(module), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "Repl.cfg"), []byte(cfg), 0o644); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, java, "-cp", jar, "tlc2.TLC", "-deadlock", "-workers", "1", "Repl.tla")
	cmd.Dir = dir
	out, err := cmd.CombinedOutput()
	if err != nil || !strings.Contains(string(out), "No error has been found") {
		t.Fatalf("TLC: %v\n%s", err, out)
	}
}
