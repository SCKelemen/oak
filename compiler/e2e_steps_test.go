package compiler

import (
	"strings"
	"testing"
)

// Steps as values (docs/spec/60-effects-allocation.md section 2b; the ml
// pilot's F4 / 5.19): the device's two effects, Device.Launch and
// Device.Readback, declared on the runtime's externs; a Step is a record
// whose run field carries the row { Device.Launch }, so a body that reads
// back is refused where the step is built, and a replay loop that forbids
// Device.Readback launches through the field without knowing the body.
const stepsProgram = `package main

launch: (kernel: c.UInt32): () effects { Device.Launch } = c.extern("ml_launch")
readback: (slot: c.UInt32): c.UInt32 effects { Device.Readback } = c.extern("ml_readback")

Step: type = struct { run: (u32) -> () effects { Device.Launch } }

decode_token: (t: u32): () = {
  launch(c.UInt32(t))
  launch(c.UInt32(t + 1))
}

replay: (s: Step, n: u32): () forbids { Device.Readback } = {
  run: (u32) -> () effects { Device.Launch } = s.run
  i: u32 = 0
  while i < n {
    run(i)
    i = i + 1
  }
}

main: (): i32 = {
  s: Step = Step { run: decode_token }
  replay(s, 3)
  0
}
`

func TestE2EStepsAsValues(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": stepsProgram})
	if _, err := New().WithPackageDir(root).SemanticModel().Get(); err != nil {
		t.Fatalf("a launching step is a Step: %v", err)
	}
	// A body that reads back is refused where the step is built, naming
	// the reader.
	reading := strings.Replace(stepsProgram, "  launch(c.UInt32(t + 1))\n", "  launch(c.UInt32(t + 1))\n  _ = readback(c.UInt32(t))\n", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": reading})
	_, err := New().WithPackageDir(root).SemanticModel().Get()
	if err == nil || !strings.Contains(err.Error(), "Device.Readback") || !strings.Contains(err.Error(), "readback") {
		t.Fatalf("a step that reads back must be refused by name: %v", err)
	}
	// A step stored and replayed later: the field's row is what the replay
	// sees, so forbids holds through the value.
	stored := strings.Replace(stepsProgram, "  replay(s, 3)\n", "  steps: [2]Step = [s, s]\n  replay(steps[1], 3)\n", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": stored})
	if _, err := New().WithPackageDir(root).SemanticModel().Get(); err != nil {
		t.Fatalf("a stored step replays: %v", err)
	}
}
