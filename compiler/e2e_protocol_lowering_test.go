package compiler

import (
	"fmt"
	"regexp"
	"strings"
	"testing"
)

// Protocol lowering (docs/spec/112-protocols.md section 2a, 90-backend.md
// section 14): a machine without a data record lowers to a compile-time
// transition table — a shift DFA when states plus the sink number at most
// ten, a dense u8 table otherwise — and a byte-driven machine also gets
// `name_run`. The Oak bodies stay the meaning: these tests run the same
// programs through the interpreter (which executes the Oak bodies) and the
// C backend (which executes the tables) and require the same answers.

// A guarded byte machine: the shape whose guards the projection used to
// drop. Three states plus the sink is four fields: shift form.
const byteMachine = `
Bytes: protocol = {
  initial Start
  byte(b: u8): Start -> Small when b < u8(128)
  byte(b: u8): Start -> Big when b >= u8(128) && b != u8(255)
  byte(b: u8): Small -> Small when b % u8(2) == u8(0)
  byte(b: u8): Small -> Big when b % u8(2) == u8(1)
  byte(b: u8): Big -> Big
}
`

// The UTF-8 validity DFA as a protocol: Accept plus seven continuation
// classes make eight states, nine with the sink — within the shift limit,
// so one u64 row per byte value.
const utf8Machine = `
Utf8: protocol = {
  initial Accept
  byte(b: u8): Accept -> Accept when b < u8(128)
  byte(b: u8): Accept -> Two when b >= u8(194) && b <= u8(223)
  byte(b: u8): Accept -> ThreeE0 when b == u8(224)
  byte(b: u8): Accept -> Three when (b >= u8(225) && b <= u8(236)) || b == u8(238) || b == u8(239)
  byte(b: u8): Accept -> ThreeED when b == u8(237)
  byte(b: u8): Accept -> FourF0 when b == u8(240)
  byte(b: u8): Accept -> Four when b >= u8(241) && b <= u8(243)
  byte(b: u8): Accept -> FourF4 when b == u8(244)
  byte(b: u8): Two -> Accept when b >= u8(128) && b <= u8(191)
  byte(b: u8): ThreeE0 -> Two when b >= u8(160) && b <= u8(191)
  byte(b: u8): Three -> Two when b >= u8(128) && b <= u8(191)
  byte(b: u8): ThreeED -> Two when b >= u8(128) && b <= u8(159)
  byte(b: u8): FourF0 -> Three when b >= u8(144) && b <= u8(191)
  byte(b: u8): Four -> Three when b >= u8(128) && b <= u8(191)
  byte(b: u8): FourF4 -> Three when b >= u8(128) && b <= u8(143)
}
`

func TestProtocolPayloadGuardsAreHonored(t *testing.T) {
	src := byteMachine + `
main: (): u32 {
  s: BytesState = bytes_initial()
  s = bytes_next(s, .Byte(u8(200)))
  s ? | .Big => u32(1) | .Small => u32(2) | .Start => u32(3)
}
`
	if got := interpretChecked(t, src); got != 1 {
		t.Fatalf("interpreter: guard on the payload not honored, got %d", got)
	}
	exit, abnormal := buildAndRun(t, "payload_guard", src)
	if abnormal || exit != 1 {
		t.Fatalf("compiled: exit %d abnormal %v", exit, abnormal)
	}
}

// foldProgram returns a program whose main folds, over every symbol of the
// machine from one fixed state, the code `next index + 1` (0 when the step
// is illegal) into an 8-bit checksum — one exit code per state, compared
// between the interpreter (Oak bodies) and the backend (tables).
func foldProgram(machine, name, snake, state string, states, symbols []string, byteStep bool) string {
	var b strings.Builder
	b.WriteString(machine)
	b.WriteString(fmt.Sprintf("code: (s: %sState): u32 = s ?", name))
	for i, st := range states {
		b.WriteString(fmt.Sprintf(" | .%s => u32(%d)", st, i+1))
	}
	b.WriteString("\n")
	b.WriteString("main: (): u32 {\n  acc: u32 = 7\n")
	if byteStep {
		b.WriteString(fmt.Sprintf("  i: u32 = 0\n  while i < u32(256) {\n    sym: u8 = u8_trunc_u32(i)\n    step: %sStep = .%s(sym)\n    source: %sState = .%s\n", name, symbols[0], name, state))
		b.WriteString(fmt.Sprintf("    c: u32 = %s_legal(source, step) ? code(%s_next(source, step)) | u32(0)\n", snake, snake))
		b.WriteString("    acc = (acc * u32(31) + c) % u32(251)\n    i = i + u32(1)\n  }\n")
	} else {
		for _, sym := range symbols {
			b.WriteString(fmt.Sprintf("  {\n    step: %sStep = .%s\n    source: %sState = .%s\n", name, sym, name, state))
			b.WriteString(fmt.Sprintf("    c: u32 = %s_legal(source, step) ? code(%s_next(source, step)) | u32(0)\n", snake, snake))
			b.WriteString("    acc = (acc * u32(31) + c) % u32(251)\n  }\n")
		}
	}
	b.WriteString("  acc\n}\n")
	return b.String()
}

func TestProtocolLoweringMatchesInterpreterByteMachines(t *testing.T) {
	cases := []struct {
		name, snake, machine string
		states               []string
	}{
		{"Bytes", "bytes", byteMachine, []string{"Start", "Small", "Big"}},
		{"Utf8", "utf8", utf8Machine, []string{"Accept", "Two", "ThreeE0", "Three", "ThreeED", "FourF0", "Four", "FourF4"}},
	}
	for _, c := range cases {
		for _, state := range c.states {
			src := foldProgram(c.machine, c.name, c.snake, state, c.states, []string{"Byte"}, true)
			want := interpretChecked(t, src)
			exit, abnormal := buildAndRun(t, "fold_"+c.snake+"_"+state, src)
			if abnormal || int64(exit) != want {
				t.Fatalf("%s from %s: interpreter %d, compiled exit %d abnormal %v", c.name, state, want, exit, abnormal)
			}
		}
	}
}

func TestProtocolLoweringMatchesInterpreterStepMachines(t *testing.T) {
	// VirtualIrq: three states, shift form; its program step carries a
	// payload no guard reads, so the step is one symbol. Ten states: dense.
	ten := "Ten: protocol = {\n  initial S0\n"
	var tenStates []string
	for i := 0; i < 10; i++ {
		tenStates = append(tenStates, fmt.Sprintf("S%d", i))
	}
	for i := 0; i < 10; i++ {
		ten += fmt.Sprintf("  go: S%d -> S%d\n", i, (i+1)%10)
		if i%2 == 0 {
			ten += fmt.Sprintf("  skip: S%d -> S%d\n", i, (i+3)%10)
		}
	}
	ten += "}\n"
	cases := []struct {
		name, snake, machine string
		states, steps        []string
	}{
		{"VirtualIrq", "virtual_irq", protocolSource, []string{"Idle", "Pending", "Active"}, []string{"Inject", "Acknowledge", "Eoi", "Program(u16(7))"}},
		{"Ten", "ten", ten, tenStates, []string{"Go", "Skip"}},
	}
	for _, c := range cases {
		for _, state := range c.states {
			src := foldProgram(c.machine, c.name, c.snake, state, c.states, c.steps, false)
			want := interpretChecked(t, src)
			exit, abnormal := buildAndRun(t, "fold_"+c.snake+"_"+state, src)
			if abnormal || int64(exit) != want {
				t.Fatalf("%s from %s: interpreter %d, compiled exit %d abnormal %v", c.name, state, want, exit, abnormal)
			}
		}
	}
}

func TestProtocolLoweringEmitsTablesAndOffsets(t *testing.T) {
	c, err := New().WithSource("lower.oak", protocolSource+utf8Machine+"main: (): u32 = u32(0)\n").EmitC().Get()
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	for _, want := range []string{
		`static const u64 oak_virtual_irq_transitions\[4\]`, // shift rows, one per step
		`oak_VirtualIrqState_tag_Pending\s*=\s*6`,           // offsets as tags
		`oak_VirtualIrqState_tag_Active\s*=\s*12`,
		`static const u64 oak_utf8_transitions\[256\]`, // shift rows, one per byte value
		`oak_Utf8State_tag_Two\s*=\s*6`,
		`oak_Utf8State oak_utf8_run\( oak_Utf8State state, oak_view_u8 bytes \)`,
	} {
		if !regexp.MustCompile(want).MatchString(c) {
			t.Errorf("generated C lacks %q", want)
		}
	}
}

func TestProtocolRunStepsAByteView(t *testing.T) {
	// A valid UTF-8 text ends in Accept; a truncated sequence traps once
	// at the end of the batch (Oak.Protocol.runSink_correct).
	valid := utf8Machine + `
main: (): u32 {
  text: [8]u8 = [u8(104), u8(105), u8(195), u8(169), u8(226), u8(130), u8(172), u8(33)]
  s: Utf8State = utf8_run(utf8_initial(), view(&text))
  s ? | .Accept => u32(42) | _ => u32(1)
}
`
	exit, abnormal := buildAndRun(t, "utf8_run_valid", valid)
	if abnormal || exit != 42 {
		t.Fatalf("valid text: exit %d abnormal %v", exit, abnormal)
	}
	if got := interpretChecked(t, valid); got != 42 {
		t.Fatalf("interpreter disagrees on the valid text: %d", got)
	}
	invalid := utf8Machine + `
main: (): u32 {
  text: [3]u8 = [u8(195), u8(65), u8(66)]
  s: Utf8State = utf8_run(utf8_initial(), view(&text))
  s ? | .Accept => u32(42) | _ => u32(1)
}
`
	_, abnormal = buildAndRun(t, "utf8_run_invalid", invalid)
	if !abnormal {
		t.Fatalf("an illegal byte in the batch must trap")
	}
}
