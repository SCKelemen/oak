package compiler

import (
	"strings"
	"testing"
)

// A protocol with a data record: guards select between lines of one step,
// effects mutate the record through the transition function's span.
const schedProtocolSource = `
import(std)
Quantum: protocol = {
  data { budget: u32, pending: Bool }
  init { budget: u32(2), pending: false }
  initial Running
  tick: Running -> Running when data.budget > u32(1) then { data.budget = data.budget - u32(1) }
  tick: Running -> Yielded when data.budget <= u32(1) then { data.budget = u32(2) }
  resume: Yielded -> Running
  park: Running -> Parked when !data.pending
  signal(on: Bool): Parked -> Parked then { data.pending = on }
  signal(on: Bool): Running -> Running then { data.pending = on }
  wake: Parked -> Running when data.pending then { data.pending = false }
}
`

func TestE2EProtocolDataGuardsAndEffects(t *testing.T) {
	src := schedProtocolSource + `
is_running: (s: QuantumState): Bool = s ? | .Running => true | _ => false
is_yielded: (s: QuantumState): Bool = s ? | .Yielded => true | _ => false
is_parked: (s: QuantumState): Bool = s ? | .Parked => true | _ => false
main: (): i32 {
  store: [1]QuantumData
  data: [*]QuantumData = span(&store)
  data[0] = quantum_initial_data()
  s: QuantumState = quantum_initial()
  assert(quantum_legal(s, data[0], .Tick))
  s = quantum_next(s, data, .Tick)
  assert(is_running(s) && data[0].budget == u32(1))
  s = quantum_next(s, data, .Tick)
  assert(is_yielded(s) && data[0].budget == u32(2))
  assert(!quantum_legal(s, data[0], .Tick) && quantum_legal(s, data[0], .Resume))
  s = quantum_next(s, data, .Resume)
  assert(quantum_legal(s, data[0], .Park))
  s = quantum_next(s, data, .Park)
  assert(is_parked(s) && !quantum_legal(s, data[0], .Wake))
  s = quantum_next(s, data, .Signal(true))
  assert(is_parked(s) && data[0].pending && quantum_legal(s, data[0], .Wake))
  s = quantum_next(s, data, .Wake)
  assert(is_running(s) && !data[0].pending)
  s = quantum_next(s, data, .Signal(true))
  assert(!quantum_legal(s, data[0], .Park))
  42
}
`
	code, abnormal := buildAndRun(t, "protocol_data", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestProtocolDataShapeDiagnostics(t *testing.T) {
	cases := map[string]string{
		"init without data": "P: protocol = { init { x: u32(1) }\n initial X\n a: X -> Y }\nmain: (): i32 = 0",
		"init misses field": "P: protocol = { data { x: u32, y: u32 }\n init { x: u32(1) }\n initial X\n a: X -> Y }\nmain: (): i32 = 0",
		"init extra field":  "P: protocol = { data { x: u32 }\n init { x: u32(1), z: u32(2) }\n initial X\n a: X -> Y }\nmain: (): i32 = 0",
		"data w/o record":   "P: protocol = { initial X\n a: X -> Y when data.x > u32(0) }\nmain: (): i32 = 0",
		"unguarded twins":   "P: protocol = { data { x: u32 }\n init { x: u32(0) }\n initial X\n a: X -> Y when data.x > u32(0)\n a: X -> X }\nmain: (): i32 = 0",
		"reserved field":    "P: protocol = { data { state: u32 }\n init { state: u32(0) }\n initial X\n a: X -> Y }\nmain: (): i32 = 0",
	}
	for name, src := range cases {
		_, err := New().WithSource(name+".oak", "import(std)\n"+src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), CodeProtocolShape) {
			t.Errorf("%s: want %s, got %v", name, CodeProtocolShape, err)
		}
	}
}

func TestProtocolDataTLAModule(t *testing.T) {
	tree, err := New().WithSource("sched.oak", schedProtocolSource).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	module, err := ProtocolTLA(Protocols(tree)[0], "sched.oak")
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"CONSTANTS On",
		"VARIABLES state, budget, pending",
		"vars == <<state, budget, pending>>",
		"Init ==\n    state = \"Running\"\n    /\\ budget = 2\n    /\\ pending = FALSE",
		"Tick ==\n    \\/ state = \"Running\" /\\ (budget > 1) /\\ state' = \"Running\" /\\ budget' = (budget - 1) /\\ UNCHANGED <<pending>>\n    \\/ state = \"Running\" /\\ (budget <= 1) /\\ state' = \"Yielded\" /\\ budget' = 2 /\\ UNCHANGED <<pending>>",
		"Park ==\n    state = \"Running\" /\\ ~(pending) /\\ state' = \"Parked\" /\\ UNCHANGED <<budget, pending>>",
		"Signal(on) ==\n    \\/ state = \"Parked\" /\\ state' = \"Parked\" /\\ pending' = on /\\ UNCHANGED <<budget>>",
		"\\/ (\\E on \\in On : Signal(on))",
		"TypeOK ==\n    state \\in States\n    /\\ budget \\in Nat\n    /\\ pending \\in BOOLEAN",
	} {
		if !strings.Contains(module, want) {
			t.Errorf("module lacks %q:\n%s", want, module)
		}
	}
}
