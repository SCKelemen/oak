package compiler

import (
	"strings"
	"testing"
)

// The correctness-checklist pass over the protocol chapter
// (docs/notes/protocols-2026-09.md): the five readings of one declaration
// — the projection, the static projection, the model-checker module, the
// prover's theorems, the monitor — agree on binder names, index bounds,
// and reach.
const protocolPassProgram = `
import(std)
Cmd: type = struct { slot: u8, value: u8 }
Job: protocol = {
  data { code: u8 }
  init { code: u8(0) }
  initial Running
  finish(done: Bool): Running -> Stopped when done
  finish(done: Bool): Running -> Running when !done
  report(result: u8): Stopped -> Stopped then { data.code = result }
}
Gate: protocol = {
  initial Shut
  pass(done: Bool): Shut -> Open when done
  pass(done: Bool): Shut -> Shut when !done
}
Cells: protocol = {
  data { cells: [2]u8 }
  init { cells: [2]u8{ 0, 0 } }
  initial Open
  put(cmd: Cmd): Open -> Open then { data.cells[u32(cmd.slot)] = cmd.value }
}
is_stopped: (s: JobState): Bool = s ? | .Stopped => true | _ => false
is_open: (s: GateState): Bool = s ? | .Open => true | _ => false
main: (): i32 {
  ok: Bool = true
  // A payload named like a generated local (done, result) is the payload,
  // not the projection's own binder: the guard reads the argument.
  store: [1]JobData
  data: [*]JobData = span(&store)
  data[0] = job_initial_data()
  s: JobState = job_initial()
  ok = ok && job_legal(s, data[0], .Finish(true)) && job_legal(s, data[0], .Finish(false))
  s = job_next(s, data, .Finish(false))
  ok = ok && !is_stopped(s)
  s = job_next(s, data, .Finish(true))
  ok = ok && is_stopped(s)
  s = job_next(s, data, .Report(u8(9)))
  ok = ok && is_stopped(s) && data[0].code == u8(9)
  // The same for a machine without data, where the guarded step takes
  // the sequential shape with the done flag.
  g: GateState = gate_next(gate_initial(), .Pass(false))
  ok = ok && !is_open(g)
  g = gate_next(g, .Pass(true))
  ok = ok && is_open(g)
  // An index by the payload is bounded by its line: a slot out of range
  // is an illegal step in name_legal, a violation in the monitor, and
  // never a trap in name_next.
  cstore: [1]CellsData
  cdata: [*]CellsData = span(&cstore)
  cdata[0] = cells_initial_data()
  c: CellsState = cells_initial()
  ok = ok && cells_legal(c, cdata[0], .Put(Cmd { slot: u8(1), value: u8(7) }))
  ok = ok && !cells_legal(c, cdata[0], .Put(Cmd { slot: u8(2), value: u8(7) }))
  mstore: [1]CellsMonitor
  mon: [*]CellsMonitor = span(&mstore)
  mon[0] = cells_monitor()
  ok = ok && !cells_observe(mon, cdata, .Put(Cmd { slot: u8(2), value: u8(1) })) && mon[0].violations == u32(1)
  ok = ok && cells_observe(mon, cdata, .Put(Cmd { slot: u8(1), value: u8(7) })) && cdata[0].cells[u32(1)] == u8(7)
  // The static projection reads the same bound: the step is guarded, so
  // it returns an outcome, and the slot out of range is Refused.
  h: Cells[CellsOpen] = cells_handle()
  refused: Bool = cells_put(h, Cmd { slot: u8(2), value: u8(1) }) ? | .Refused(_) => true | .ToOpen(_) => false
  h2: Cells[CellsOpen] = cells_handle()
  moved: Bool = cells_put(h2, Cmd { slot: u8(0), value: u8(5) }) ? | .ToOpen(to) => to.data.cells[u32(0)] == u8(5) | .Refused(_) => false
  ok = ok && refused && moved
  ok ? 42 | 1
}
`

func TestE2EProtocolPassCompiled(t *testing.T) {
	code, abnormal := buildAndRun(t, "protocol_pass", protocolPassProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2EProtocolPassInterpreted(t *testing.T) {
	if got := interpretChecked(t, protocolPassProgram); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
}

// The shape errors the pass added (docs/spec/112-protocols.md section 1):
// reserved payload names, a guarded via line, an unreached state, two
// projections spelling one name, a constant index out of range.
func TestProtocolPassShapeDiagnostics(t *testing.T) {
	cases := map[string]struct{ src, want string }{
		"reserved payload":   {"P: protocol = { initial X\n a(state: u8): X -> Y\n b: Y -> X }\nmain: (): i32 = 0", "payload name state is reserved"},
		"oak_ payload":       {"P: protocol = { initial X\n a(oak_done: Bool): X -> Y\n b: Y -> X }\nmain: (): i32 = 0", "payload name oak_done is reserved"},
		"guarded via":        {"R: type = struct { x: u8 }\nP: protocol = { resource R\n initial X\n a: X -> Y when true via f\n b: Y -> X }\nf: (r: R): () = {}\nmain: (): i32 = 0", "a `via` line carries no `when` guard"},
		"unreached state":    {"P: protocol = { initial X\n a: X -> Y\n b: Z -> X }\nmain: (): i32 = 0", "no path of transitions leads from X to state Z"},
		"state named State":  {"P: protocol = { initial State\n a: State -> Done\n b: Done -> State }\nmain: (): i32 = 0", "projects PState twice"},
		"step named monitor": {"P: protocol = { initial X\n monitor: X -> Y\n b: Y -> X }\nmain: (): i32 = 0", "projects p_monitor twice"},
		"across protocols":   {"Foo: protocol = { initial Idle\n go: Idle -> BarState\n back: BarState -> Idle }\nFooBar: protocol = { initial Idle\n go: Idle -> Done\n back: Done -> Idle }\nmain: (): i32 = 0", "projects FooBarState, which protocol Foo already projects"},
		"literal index":      {"P: protocol = { data { c: [2]u8 }\n init { c: [2]u8{ 0, 0 } }\n initial X\n a: X -> X then { data.c[u32(2)] = u8(1) } }\nmain: (): i32 = 0", "index 2 is out of range for a field of 2 elements"},
	}
	for name, c := range cases {
		_, err := New().WithSource(name+".oak", c.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), CodeProtocolShape) || !strings.Contains(err.Error(), c.want) {
			t.Errorf("%s: expected %s mentioning %q, got %v", name, CodeProtocolShape, c.want, err)
		}
	}
}

// The model-checker module reads the same bound and states the fields'
// widths; the configuration's payload domain covers every literal the
// declaration mentions and one value past it.
func TestProtocolPassTLAModule(t *testing.T) {
	src := `
Cmd: type = struct { slot: u8, value: u8 }
Cells: protocol = {
  data { cells: [2]u8, count: u16 }
  init { cells: [2]u8{ 0, 0 }, count: u16(0) }
  initial Open
  put(cmd: Cmd): Open -> Open then { data.cells[u32(cmd.slot)] = cmd.value; data.count = data.count + u16(1) }
}
Dial: protocol = {
  initial Off
  turn(n: u8): Off -> On when n < u8(5)
  turn(n: u8): Off -> Off when n >= u8(5)
  reset: On -> Off
}
main: (): i32 = 0
`
	tree, err := New().WithSource("cells.oak", src).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decls := Protocols(tree)
	records := RecordDeclarations(tree.Root)
	module, err := ProtocolTLAWithRecords(decls[0], "cells.oak", records)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"Put(cmd) ==\n    state = \"Open\" /\\ (cmd.slot < 2) /\\ state' = \"Open\"",
		"/\\ cells \\in [0..1 -> 0..255]",
		"/\\ count \\in 0..65535",
	} {
		if !strings.Contains(module, want) {
			t.Errorf("module lacks %q:\n%s", want, module)
		}
	}
	if cfg := ProtocolTLCConfigWith(decls[0], records); !strings.Contains(cfg, "    CmdSlot = {0, 1, 2, 3}\n    CmdValue = {0, 1, 2, 3}\n") {
		t.Errorf("a declaration without literals keeps the four-value domain:\n%s", cfg)
	}
	if cfg := ProtocolTLCConfig(decls[1]); !strings.Contains(cfg, "    N = {0, 1, 2, 3, 4, 5, 6}\n") {
		t.Errorf("the domain reaches one past the largest literal (5):\n%s", cfg)
	}
	// The projection agrees with its own module under the added bound.
	self, err := ProtocolConformance(decls[0], module, records)
	if err != nil {
		t.Fatal(err)
	}
	if !self.Conforms {
		t.Fatalf("self-conformance with an index bound:\n%s", FormatTLAConformance(self))
	}
}
