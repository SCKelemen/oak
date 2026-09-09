package testrunner

import (
	"reflect"
	"strings"
	"testing"
)

const typedFixture = `import(std)
import(testing)

SleepArg: type = struct { task: u8, ticks: u8 }
Cmd: type = Admit: u8 | Sleep: SleepArg | Tick | Flag: Bool

cmd_generate: (choices: [*]TestChoices, data: []u8): Cmd = derive.test_generate
cmd_encode: (v: Cmd): TestCommand = derive.test_encode
cmd_decode: (command: TestCommand): Option[Cmd] = derive.test_decode

sleep_ticks: (v: Cmd): u8 = v ? | .Sleep(s) => s.ticks | .Admit(t) => u8(0) | .Tick => u8(0) | .Flag(f) => u8(0)

GeneratePropertyTyped: (data: []u8): () {
  tape: [1]TestChoices
  choices: [*]TestChoices = span(&tape)
  i: u32 = u32(0)
  while i < u32(6) {
    testing_command(cmd_encode(cmd_generate(choices, data)))
    i = i + u32(1)
  }
}

PropertyTyped: (data: []u8): () {
  count: u32 = test_command_count(data)
  i: u32 = u32(0)
  while i < count {
    raw: TestCommand = test_command_at(data, i)
    decoded: Option[Cmd] = cmd_decode(raw)
    present: Bool = decoded ? | .Some(v) => true | .None => false
    test_assume(present)
    value: Cmd = decoded ? | .Some(v) => v | .None => Cmd.Tick
    back: TestCommand = cmd_encode(value)
    test_check(back.kind == raw.kind && back.target == raw.target && back.value == raw.value, u32(9001))
    test_check(sleep_ticks(value) < u8(3), u32(9002))
    i = i + u32(1)
  }
}
`

// Typed commands round-trip through the carrier, the generator drives them,
// and a failing history shrinks to the single smallest decodable command.
func TestDerivedTypedCommands(t *testing.T) {
	dir := fixture(t, map[string]string{"a_test.oak": typedFixture})
	code, results, stderr := runCLI(t, "-runs", "200", "-seed", "3", "-timeout", "10s", dir)
	if code != 1 || len(results) != 1 || results[0].Failure != "invariant:9002" {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	want := []Command{{Kind: 1, Target: 0, Value: 3}}
	if !reflect.DeepEqual(results[0].Commands, want) {
		t.Fatalf("minimized typed history: %+v", results[0].Commands)
	}
	code, replay, _ := runCLI(t, "-replay", results[0].Artifact, dir)
	if code != 1 || replay[0].Failure != "reproduced invariant:9002" {
		t.Fatalf("replay: %d %+v", code, replay)
	}
}

func TestDerivedTypedCommandsRejectBadShapes(t *testing.T) {
	for _, bad := range []struct{ source, code string }{
		{"import(std)\nimport(testing)\nCmd: type = Tick | Go: u32\nbad: (v: Cmd): u32 = derive.test_encode\nTestX: (): () {}\n", "OAK-M0202"},
		{"import(std)\nimport(testing)\nCmd: type = Tick | Go: u64\ngen: (choices: [*]TestChoices, data: []u8): Cmd = derive.test_generate\nTestX: (): () {}\n", "OAK-M0203"},
		{"import(std)\nimport(testing)\nBig: type = struct { a: u32, b: u32, c: u32 }\nCmd: type = Tick | Go: Big\ngen: (choices: [*]TestChoices, data: []u8): Cmd = derive.test_generate\nTestX: (): () {}\n", "OAK-M0203"},
		{"import(std)\nimport(testing)\nP: type = struct { a: u32 }\ngen: (choices: [*]TestChoices, data: []u8): P = derive.test_generate\nTestX: (): () {}\n", "OAK-M0203"},
	} {
		dir := fixture(t, map[string]string{"a_test.oak": bad.source})
		code, results, stderr := runCLI(t, dir)
		text := stderr
		for _, r := range results {
			text += r.Failure
		}
		if code == 0 || !strings.Contains(text, bad.code) {
			t.Fatalf("accepted or misreported %q: %d %+v %s", bad.source, code, results, stderr)
		}
	}
}
