package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Methods on ADT receivers lower to C (docs/spec/90-backend.md): a direct
// call to the method's function with the receiver first, under a mangled
// name no function or other method can share. Verified in running machine
// code, including a resource receiver contract declared in source.

const adtMethodsSource = `
Handle: type = Live: u32 | Dead
Other: type = On | Off

fn (h: Handle) peek(): u32 = h ? | .Live(id) => id | .Dead => u32(0)
fn (h: Handle) merge(other: Handle): u32 = h.peek() + other.peek()
fn (o: Other) peek(): u32 = o ? | .On => u32(100) | .Off => u32(200)

Handle_peek: (h: Handle): u32 = u32(7)
`

func TestE2EADTMethodsLowerToC(t *testing.T) {
	stdout, exit, abnormal := buildAndRunOutput(t, "adt_methods", adtMethodsSource+`
main: (): u32 {
  h: Handle = Handle.Live(u32(5))
  g: Handle = Handle.Live(u32(30))
  o: Other = Other.Off
  h.peek() + h.merge(g) + o.peek() - Handle_peek(h) - u32(200)
}
`)
	// 5 + (5 + 30) + 200 - 7 - 200 = 33
	if abnormal || exit != 33 {
		t.Fatalf("ADT methods: exit %d abnormal %v\n%s", exit, abnormal, stdout)
	}
	// The generated C names each method by its receiver type and never by
	// the bare method name, so `Handle_peek` and `Handle::peek` differ.
	c, err := New().WithSource("adt_methods_names.oak", adtMethodsSource+"\nmain: (): u32 = u32(0)\n").EmitC().Get()
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	for _, want := range []string{"oak_6Handle_peek(", "oak_6Handle_merge(", "oak_5Other_peek(", "oak_Handle_peek("} {
		if !strings.Contains(c, want) {
			t.Errorf("generated C lacks %s", want)
		}
	}
	if strings.Contains(c, ".peek(") || strings.Contains(c, ".merge(") {
		t.Errorf("a method call leaked as a struct-field call:\n%s", c)
	}
}

func TestE2EResourceReceiverContractsExecute(t *testing.T) {
	// The receiver contract typechecks from source (docs/spec/112-protocols.md
	// section 5.1) and the program compiles and runs.
	source := `
Handle: type = Live: u32 | Dead
fn (h: Handle) peek(): u32 = h ? | .Live(id) => id | .Dead => u32(0)
fn (h: Handle) close(): () = {}

Lifecycle: protocol = {
  resource Handle
  initial Open
  look: Open -> Open via Handle.peek(borrowed receiver)
  shut: Open -> Closed via Handle.close(consumed receiver)
}
`
	// A parameter is a tracked authority; a variant literal is not (it is
	// not a fresh-return operation), so the body runs on a parameter.
	exit, abnormal := buildAndRun(t, "receiver_contracts", source+`
run: (h: Handle): u32 {
  n: u32 = h.peek()
  h.close()
  n
}
main: (): u32 = run(Handle.Live(u32(42)))
`)
	if abnormal || exit != 42 {
		t.Fatalf("receiver contracts: exit %d abnormal %v", exit, abnormal)
	}
	_, err := New().WithSource("receiver_after_close.oak", source+`
run: (h: Handle): u32 {
  h.close()
  h.peek()
}
main: (): u32 = run(Handle.Live(u32(42)))
`).Check().Get()
	expectCode(t, "receiver-after-close", err, typechecker.CodeResourceUsedAfterConsume)
}
