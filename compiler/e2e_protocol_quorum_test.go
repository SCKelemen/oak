package compiler

import (
	"strings"
	"testing"
)

// Quorum predicates and array-of-records data in protocol guards
// (docs/spec/112-protocols.md sections 1 and 4): count/all/any/none over an
// [N]Bool field and over a Bool field of an [N]Record field, projected as
// bounded helpers in Oak and as Cardinality and bounded quantifiers in
// TLA+, so a replication protocol's normal operation and view change are
// declared rather than transliterated.
const replicationProtocolSource = `
import(std)
Peer: type = struct { acked: Bool, term: u32 }
Replication: protocol = {
  data { acks: [3]Bool, peers: [3]Peer, committed: u32 }
  init { acks: [3]Bool{ false, false, false }, peers: [3]Peer{ Peer { acked: false, term: u32(0) }, Peer { acked: false, term: u32(0) }, Peer { acked: false, term: u32(0) } }, committed: u32(0) }
  initial Normal
  ack(who: u8): Normal -> Normal when u32(who) < u32(3) && !data.acks[u32(who)] then { data.acks[u32(who)] = true; data.peers[u32(who)].acked = true }
  commit: Normal -> Normal when count(data.acks) >= u32(2) && any(data.peers, acked) then { data.committed = data.committed + u32(1); data.acks[u32(0)] = false; data.acks[u32(1)] = false; data.acks[u32(2)] = false }
  suspect: Normal -> ViewChange when none(data.acks) && data.committed > u32(0)
  recover: ViewChange -> Normal when all(data.peers, acked) then { data.peers[u32(0)].acked = false; data.peers[u32(1)].acked = false; data.peers[u32(2)].acked = false }
}
`

func TestE2EProtocolQuorumGuards(t *testing.T) {
	src := replicationProtocolSource + `
main: (): i32 {
  store: [1]ReplicationData
  data: [*]ReplicationData = span(&store)
  data[0] = replication_initial_data()
  s: ReplicationState = replication_initial()
  assert(!replication_legal(s, data[0], .Commit))
  s = replication_next(s, data, .Ack(u8(0)))
  assert(replication_count_acks(data[0]) == u32(1))
  assert(!replication_legal(s, data[0], .Commit))
  s = replication_next(s, data, .Ack(u8(2)))
  assert(replication_count_acks(data[0]) == u32(2))
  assert(replication_any_peers_acked(data[0]))
  assert(replication_legal(s, data[0], .Commit))
  s = replication_next(s, data, .Commit)
  assert(data[0].committed == u32(1) && replication_none_acks(data[0]))
  assert(replication_legal(s, data[0], .Suspect))
  s = replication_next(s, data, .Suspect)
  // Recovery needs every peer acknowledged: two of three is not all.
  assert(!replication_legal(s, data[0], .Recover))
  data[0].peers[u32(1)].acked = true
  assert(replication_all_peers_acked(data[0]))
  s = replication_next(s, data, .Recover)
  normal: Bool = s ? | .Normal => true | _ => false
  normal && !data[0].peers[u32(0)].acked ? { 42 } | { 0 }
}
`
	code, abnormal := buildAndRun(t, "protocol_quorum", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretChecked(t, src); got != 42 {
		t.Fatalf("interpreter returned %d, want 42", got)
	}
}

func TestProtocolQuorumTLAModule(t *testing.T) {
	tree, err := New().WithSource("replication.oak", replicationProtocolSource).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	module, err := ProtocolTLAWithRecords(Protocols(tree)[0], "replication.oak", RecordDeclarations(tree.Root))
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"EXTENDS Naturals, FiniteSets",
		"Cardinality({k \\in 0..2 : acks[k]}) >= 2",
		"(\\E k \\in 0..2 : peers[k].acked)",
		"(\\A k \\in 0..2 : ~acks[k])",
		"(\\A k \\in 0..2 : peers[k].acked)",
		"peers' = [peers EXCEPT ![who].acked = TRUE]",
		"/\\ peers \\in [0..2 -> [acked: BOOLEAN, term: Nat]]",
		"/\\ peers = [k \\in 0..2 |-> [acked |-> FALSE, term |-> 0]]",
	} {
		if !strings.Contains(module, want) {
			t.Errorf("module lacks %q:\n%s", want, module)
		}
	}
}

func TestProtocolQuorumShapeErrors(t *testing.T) {
	for name, tc := range map[string]struct{ guard, want string }{
		"not an array":     {"count(data.committed) > u32(0)", "not a fixed array"},
		"records need sub": {"all(data.peers)", "name the Bool field"},
		"non-Bool sub":     {"count(data.peers, term) > u32(0)", "has no Bool field"},
		"unknown field":    {"any(data.nobody)", "does not declare"},
		"not a data field": {"count(committed) > u32(0)", "takes data.field"},
	} {
		t.Run(name, func(t *testing.T) {
			src := strings.Replace(replicationProtocolSource, "when none(data.acks) && data.committed > u32(0)", "when "+tc.guard, 1)
			_, err := New().WithSource("bad.oak", src+"\nmain: (): i32 = 0\n").Check().Get()
			if err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("expected a shape error mentioning %q, got %v", tc.want, err)
			}
		})
	}
}
