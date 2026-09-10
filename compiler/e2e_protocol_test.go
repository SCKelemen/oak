package compiler

import (
	"strings"
	"testing"
)

const protocolSource = `
import(std)
VirtualIrq: protocol = {
  initial Idle
  inject: Idle -> Pending
  acknowledge: Pending -> Active
  eoi: Active -> Idle
  program(compare: u16): Idle -> Idle
  program(compare: u16): Pending -> Pending
}
`

func TestE2EProtocolProjectsStatesStepsAndTransitions(t *testing.T) {
	src := protocolSource + `
main: (): i32 {
  s: VirtualIrqState = virtual_irq_initial()
  ok: Bool = virtual_irq_legal(s, .Inject)
  bad: Bool = virtual_irq_legal(s, .Eoi)
  assert(ok && !bad)
  s = virtual_irq_next(s, .Inject)
  assert(virtual_irq_legal(s, .Program(u16(7))))
  s = virtual_irq_next(s, .Program(u16(7)))
  s = virtual_irq_next(s, .Acknowledge)
  assert(!virtual_irq_legal(s, .Program(u16(1))))
  s = virtual_irq_next(s, .Eoi)
  back: Bool = s ? | .Idle => true | _ => false
  assert(back)
  42
}
`
	code, abnormal := buildAndRun(t, "protocol_basic", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EProtocolNextTrapsOnIllegalStep(t *testing.T) {
	src := protocolSource + `
main: (): i32 {
  s: VirtualIrqState = virtual_irq_initial()
  s = virtual_irq_next(s, .Eoi)
  0
}
`
	_, abnormal := buildAndRun(t, "protocol_illegal", src)
	if !abnormal {
		t.Fatalf("an illegal transition must trap")
	}
}

func TestProtocolStepDerivesTypedCommands(t *testing.T) {
	src := protocolSource + `
import(testing)
step_generate: (choices: [*]TestChoices, data: []u8): VirtualIrqStep = derive.test_generate
step_encode: (v: VirtualIrqStep): TestCommand = derive.test_encode
step_decode: (command: TestCommand): Option[VirtualIrqStep] = derive.test_decode
`
	if _, err := New().WithSource("protocol_derive.oak", src).EmitC().Get(); err != nil {
		t.Fatalf("typed commands over a protocol step type: %v", err)
	}
}

func TestProtocolShapeDiagnostics(t *testing.T) {
	cases := map[string]string{
		"no initial":       "P: protocol = { a: X -> Y }\nmain: (): i32 = 0",
		"duplicate line":   "P: protocol = { initial X\n a: X -> Y\n a: X -> Y }\nmain: (): i32 = 0",
		"payload changes":  "P: protocol = { initial X\n a(n: u8): X -> Y\n a(n: u16): Y -> X }\nmain: (): i32 = 0",
		"bad payload type": "P: protocol = { initial X\n a(n: u64): X -> Y }\nmain: (): i32 = 0",
		"via w/o resource": "P: protocol = { initial X\n a: X -> Y via f }\nf: (): () = {}\nmain: (): i32 = 0",
		"dead initial":     "P: protocol = { initial Z\n a: X -> Y }\nmain: (): i32 = 0",
		"name collision":   "P: protocol = { initial X\n a: X -> Y }\np_legal: (): i32 = 0\nmain: (): i32 = 0",
	}
	for name, src := range cases {
		_, err := New().WithSource(name+".oak", src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), CodeProtocolShape) {
			t.Errorf("%s: want %s, got %v", name, CodeProtocolShape, err)
		}
	}
}

func TestProtocolTLAModule(t *testing.T) {
	tree, err := New().WithSource("irq.oak", protocolSource).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decls := Protocols(tree)
	if len(decls) != 1 {
		t.Fatalf("declarations = %d", len(decls))
	}
	module, err := ProtocolTLA(decls[0], "irq.oak")
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"MODULE VirtualIrq",
		"CONSTANTS Compare",
		`States == {"Idle", "Pending", "Active"}`,
		`Init == state = "Idle"`,
		"Inject ==\n    state = \"Idle\" /\\ state' = \"Pending\"",
		"Program(compare) ==\n    \\/ state = \"Idle\" /\\ state' = \"Idle\"\n    \\/ state = \"Pending\" /\\ state' = \"Pending\"",
		"Next ==\n    Inject\n    \\/ Acknowledge\n    \\/ Eoi\n    \\/ (\\E compare \\in Compare : Program(compare))",
		"TypeOK == state \\in States",
		"Spec == Init /\\ [][Next]_state",
	} {
		if !strings.Contains(module, want) {
			t.Errorf("module lacks %q:\n%s", want, module)
		}
	}
}
