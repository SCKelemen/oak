package compiler

import (
	"strings"
	"testing"
)

// The predicate form of the quantifiers (docs/spec/112-protocols.md §1;
// the dbs pilot's round-five item 8): `count(data.peers, p, p.acked &&
// u32(p.view) == data.view)` binds each element and folds the predicate,
// so a quorum over an indexed path is declared once and read by the Oak
// gate (a projected helper) and the model checker (Cardinality over the
// predicate at k) alike.
const quorumPredicateSource = `
import(std)
Peer: type = struct { acked: Bool, view: u8 }
Quorum: protocol = {
  data { peers: [3]Peer, view: u32, committed: Bool }
  init { peers: [3]Peer{ Peer { acked: false, view: u8(0) }, Peer { acked: false, view: u8(0) }, Peer { acked: false, view: u8(0) } }, view: u32(1), committed: false }
  initial Open
  ack(who: u8): Open -> Open when u32(who) < u32(3) then { data.peers[u32(who)].acked = true; data.peers[u32(who)].view = u8(1) }
  commit: Open -> Done when count(data.peers, p, p.acked && u32(p.view) == data.view) >= u32(2) && !any(data.peers, p, p.acked && u32(p.view) > data.view) then { data.committed = true }
}
`

func TestE2EProtocolQuantifierPredicateForm(t *testing.T) {
	src := quorumPredicateSource + `
is_done: (s: QuorumState): Bool = s ? | .Done => true | _ => false
main: (): i32 {
  store: [1]QuorumData
  data: [*]QuorumData = span(&store)
  data[0] = quorum_initial_data()
  s: QuorumState = quorum_initial()
  assert(!quorum_legal(s, data[0], .Commit))
  s = quorum_next(s, data, .Ack(u8(0)))
  assert(!quorum_legal(s, data[0], .Commit))
  s = quorum_next(s, data, .Ack(u8(2)))
  assert(quorum_legal(s, data[0], .Commit))
  s = quorum_next(s, data, .Commit)
  is_done(s) && data[0].committed ? 42 | 1
}
`
	if got := interpretChecked(t, src); got != 42 {
		t.Fatalf("interpreter: %d, want 42", got)
	}
	code, abnormal := buildAndRun(t, "protocol_quantifier_predicate", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	tree, err := New().WithSource("quorum.oak", quorumPredicateSource+"main: (): i32 = 0\n").Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decl := Protocols(tree)[0]
	records := RecordDeclarations(tree.Root)
	module, err := ProtocolTLAWithRecords(decl, "quorum.oak", records)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"Cardinality({k \\in 0..2 : (peers[k].acked /\\ (peers[k].view = view))})",
		"~((\\E k \\in 0..2 : (peers[k].acked /\\ (peers[k].view > view))))",
		"EXTENDS Naturals, FiniteSets",
	} {
		if !strings.Contains(module, want) {
			t.Fatalf("module lacks %q:\n%s", want, module)
		}
	}
	self, err := ProtocolConformance(decl, module, records)
	if err != nil {
		t.Fatal(err)
	}
	if !self.Conforms {
		t.Fatalf("self-conformance with predicate quantifiers:\n%s", FormatTLAConformance(self))
	}
}

// Shape errors of the predicate form: a predicate that reads the payload,
// nests a quantifier, or rebinds a data field is refused (OAK-M0301).
func TestE2EProtocolQuantifierPredicateShape(t *testing.T) {
	for name, guard := range map[string][2]string{
		"reads the payload":  {"count(data.peers, p, p.acked && u32(p.view) == u32(who)) >= u32(2)", "may read only p and data"},
		"nests a quantifier": {"any(data.peers, p, all(data.peers, q, q.acked))", "nests a quantifier form"},
		"rebinds a field":    {"count(data.peers, view, view.acked) >= u32(2)", "not a fresh name"},
	} {
		src := `import(std)
Peer: type = struct { acked: Bool, view: u8 }
Quorum: protocol = {
  data { peers: [3]Peer, view: u32 }
  init { peers: [3]Peer{ Peer { acked: false, view: u8(0) }, Peer { acked: false, view: u8(0) }, Peer { acked: false, view: u8(0) } }, view: u32(1) }
  initial Open
  commit(who: u8): Open -> Done when ` + guard[0] + `
}
main: (): i32 = 0
`
		_, err := New().WithSource("shape.oak", src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), guard[1]) {
			t.Fatalf("%s: %v", name, err)
		}
	}
}
