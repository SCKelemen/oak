package compiler

import (
	"strings"
	"testing"
)

// The static projection (docs/spec/112-protocols.md section 2b): a protocol
// without a resource clause projects its machine into a handle's type —
// `Door[DoorClosed]`, one marker per state, `door_handle()` at the initial
// state, and one function per line that consumes the handle and returns
// it in its target state (a `DoorOpenOutcome`, `Open` or `Refused`, when the line is guarded). The same
// lines build the dynamic projection, and the two agree.
const staticProtocolProgram = `
Door: protocol = {
  data { locked: Bool, uses: u8 }
  init { locked: false, uses: u8(0) }
  initial Closed
  open: Closed -> Open when !data.locked then { data.uses = data.uses + u8(1) }
  close: Open -> Closed
  lock: Closed -> Closed then { data.locked = true }
}

main: (): i32 {
  shut: Door[DoorClosed] = door_handle()
  opened: DoorOpenOutcome = door_open(shut)
  opened ?
  | .Refused(_) => { 1 }
  | .Open(ajar) => {
    back: Door[DoorClosed] = door_close(ajar)
    locked: Door[DoorClosed] = door_lock(back)
    refused: DoorOpenOutcome = door_open(locked)
    refused ?
    | .Open(_) => { 2 }
    | .Refused(still) => {
      // The dynamic projection over the same steps reads the same data.
      store: [1]DoorData = [door_initial_data()]
      state: DoorState = door_initial()
      state = door_next(state, span(&store), .Open)
      state = door_next(state, span(&store), .Close)
      state = door_next(state, span(&store), .Lock)
      legal: Bool = door_legal(state, store[0], .Open)
      still.data.uses == u8(1) && still.data.locked && store[0].uses == u8(1) && store[0].locked && !legal ? { 42 } | { 3 }
    }
  }
}
`

func TestE2EProtocolStaticCompiled(t *testing.T) {
	code, abnormal := buildAndRun(t, "protocol_static", staticProtocolProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2EProtocolStaticInterpreted(t *testing.T) {
	if got := interpretChecked(t, staticProtocolProgram); got != 42 {
		t.Fatalf("interpreter returned %d, want 42", got)
	}
}

// A consumed handle is dead, a handle at a non-initial state cannot be
// written down, and a step from the wrong state is a type error.
func TestProtocolStaticRejections(t *testing.T) {
	for _, tc := range []struct{ name, body, want string }{
		{"reuse", `
main: (): i32 {
  shut: Door[DoorClosed] = door_handle()
  again: Door[DoorClosed] = door_lock(shut)
  twice: Door[DoorClosed] = door_lock(shut)
  0
}
`, "OAK-B0111"},
		{"construct", `
main: (): i32 {
  ajar: Door[DoorOpen] = Door { data: door_initial_data() }
  0
}
`, "OAK-B0121"},
		{"wrong-state", `
main: (): i32 {
  shut: Door[DoorClosed] = door_handle()
  closed: Door[DoorClosed] = door_close(shut)
  0
}
`, "type"},
	} {
		program := staticProtocolProgram[:strings.Index(staticProtocolProgram, "main: (): i32 {")] + tc.body
		_, err := New().WithSource(tc.name+".oak", program).Check().Get()
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Fatalf("%s: err = %v, want %s", tc.name, err, tc.want)
		}
	}
}
