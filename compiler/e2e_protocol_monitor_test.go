package compiler

import "testing"

// The derived conformance monitor (docs/spec/112-protocols.md section 2c):
// the declaration's machine runs beside an implementation, admits every
// declared transition, and counts the ones the declaration does not
// admit, leaving its state where the last legal step put it. The same
// declaration drives it that drives the projection, the model checker,
// the prover, and the typed-command derive.
const monitorProgram = `
import(std)
Cmd: type = struct { slot: u8, value: u8 }
Log: protocol = {
  data { cells: [2]u8, writes: u32 }
  init { cells: [2]u8{ 0, 0 }, writes: u32(0) }
  initial Open
  write(cmd: Cmd): Open -> Open when u32(cmd.slot) < u32(2) && data.writes < u32(3) then { data.cells[u32(cmd.slot)] = cmd.value; data.writes = data.writes + u32(1) }
  seal: Open -> Sealed when data.writes > u32(0)
}
Door: protocol = {
  initial Shut
  open: Shut -> Ajar
  close: Ajar -> Shut
  lock: Shut -> Locked
  unlock: Locked -> Shut
}
main: (): i32 {
  // A conforming implementation run: two writes, then seal.
  store: [1]LogData
  data: [*]LogData = span(&store)
  data[0] = log_initial_data()
  mon_store: [1]LogMonitor
  mon: [*]LogMonitor = span(&mon_store)
  mon[0] = log_monitor()
  ok: Bool = log_observe(mon, data, .Write(Cmd { slot: u8(1), value: u8(7) }))
  ok = ok && log_observe(mon, data, .Write(Cmd { slot: u8(0), value: u8(3) }))
  ok = ok && log_observe(mon, data, .Seal)
  ok = ok && log_conforms(mon) && data[0].writes == u32(2) && data[0].cells[u32(1)] == u8(7)
  // A write after sealing is not a declared transition: counted, state kept.
  ok = ok && !log_observe(mon, data, .Write(Cmd { slot: u8(0), value: u8(9) }))
  ok = ok && !log_conforms(mon) && mon[0].violations == u32(1) && data[0].cells[u32(0)] == u8(3)
  // A guard the declaration refuses counts too: slot 2 is out of range.
  mon[0] = log_monitor()
  data[0] = log_initial_data()
  ok = ok && !log_observe(mon, data, .Write(Cmd { slot: u8(2), value: u8(1) })) && mon[0].violations == u32(1)
  // The data-free machine: a legal walk, then a step from the wrong state.
  door_store: [1]DoorMonitor
  door: [*]DoorMonitor = span(&door_store)
  door[0] = door_monitor()
  ok = ok && door_observe(door, .Open) && door_observe(door, .Close) && door_observe(door, .Lock)
  ok = ok && door_conforms(door)
  ok = ok && !door_observe(door, .Open) && !door_conforms(door) && door[0].violations == u32(1)
  ok = ok && door_observe(door, .Unlock) && door[0].violations == u32(1)
  ok ? 42 | 1
}
`

func TestE2EProtocolMonitorCompiled(t *testing.T) {
	code, abnormal := buildAndRun(t, "protocol_monitor", monitorProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2EProtocolMonitorInterpreted(t *testing.T) {
	if got := interpretChecked(t, monitorProgram); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
}
