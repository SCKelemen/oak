package compiler

import (
	"strings"
	"testing"
)

// Refinement types as protocol payloads (docs/spec/112-protocols.md
// section 1): `Replica: type = u8 where value < u8(2)` names a step's
// payload or a record payload's field, and the predicate is the domain
// every gate reads — the Oak projection's type, the model-checker module's
// defined set, the prover's enumeration, and the typed-command derive.
const refinedProtocolSource = `
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
`

func TestE2EProtocolRefinedPayload(t *testing.T) {
	// The projection compiles, and so does the typed-command derive over
	// the step type: a refined field is drawn from its base and scanned to
	// an admitted value, packed as its base word, and decoded only when
	// the predicate admits the word (compiled with the testing host's
	// externs, which only `oak test` links).
	derived := refinedProtocolSource + `
import(testing)
step_generate: (choices: [*]TestChoices, data: []u8): ReplStep = derive.test_generate
step_encode: (v: ReplStep): TestCommand = derive.test_encode
step_decode: (command: TestCommand): Option[ReplStep] = derive.test_decode
main: (): i32 = 0
`
	if _, err := New().WithSource("repl_derive.oak", derived).EmitC().Get(); err != nil {
		t.Fatalf("typed commands over refined payloads: %v", err)
	}
	// The projection runs: a refined payload is constructed through its
	// refinement, and a step with an inadmissible value cannot be spelled.
	src := refinedProtocolSource + `
main: (): i32 {
  store: [1]ReplData
  data: [*]ReplData = span(&store)
  data[0] = repl_initial_data()
  s: ReplState = repl_initial()
  assert(repl_legal(s, data[0], .Request(Op(u8(1)))))
  s = repl_next(s, data, .Request(Op(u8(1))))
  assert(!repl_legal(s, data[0], .Commit(Count(u8(1)))))
  assert(repl_legal(s, data[0], .Prepare(Prepare { replica: Replica(u8(1)), op: Op(u8(0)) })))
  s = repl_next(s, data, .Prepare(Prepare { replica: Replica(u8(1)), op: Op(u8(0)) }))
  assert(repl_legal(s, data[0], .Commit(Count(u8(1)))))
  s = repl_next(s, data, .Commit(Count(u8(1))))
  data[0].commit[u32(0)] == u8(1) && data[0].logs[u32(1)].entries[u32(0)] == u8(1) ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "protocol_refined_payload", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	// The model-checker module defines each refined domain as the set its
	// predicate carves from the base range, and the configuration assigns
	// no constant for it.
	tree, err := New().WithSource("repl.oak", refinedProtocolSource+"main: (): i32 = 0\n").Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decl := Protocols(tree)[0]
	decls := ProtocolDeclarationsOf(tree.Root)
	module, err := ProtocolTLAWithDeclarations(decl, "repl.oak", decls)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"Op == {value \\in 0..255 : (value < 2)}",
		"PReplica == {value \\in 0..255 : (value < 2)}",
		"POp == {value \\in 0..255 : (value < 2)}",
		"P == [replica: PReplica, op: POp]",
		"N == {value \\in 0..255 : (value <= 2)}",
		"(\\E p \\in P : Prepare(p))",
	} {
		if !strings.Contains(module, want) {
			t.Fatalf("module lacks %q:\n%s", want, module)
		}
	}
	if strings.Contains(module, "CONSTANTS") {
		t.Fatalf("a refined payload needs no constant:\n%s", module)
	}
	if cfg := ProtocolTLCConfigWithDeclarations(decl, decls); strings.Contains(cfg, "CONSTANTS") {
		t.Fatalf("the configuration assigns nothing for refined domains:\n%s", cfg)
	}
	// Shape: a refinement of u32 is refused (the generator scans the base).
	wide := strings.Replace(refinedProtocolSource, "Count: type = u8 where value <= u8(2)", "Count: type = u32 where value <= u32(2)", 1)
	wide = strings.Replace(wide, "u8(n)", "u8_trunc_u32(u32(n))", -1)
	if _, err := New().WithSource("wide.oak", wide+"main: (): i32 = 0\n").EmitC().Get(); err == nil || !strings.Contains(err.Error(), "refinement of u8 or u16") {
		t.Fatalf("a u32 refinement must be refused as a payload, got %v", err)
	}
}
