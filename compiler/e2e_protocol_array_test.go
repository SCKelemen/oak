package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// Array-valued data: per-slot state indexed by the payload, with bounds
// guards, element effects, and the TLA+ function encoding. The wake counter
// is bounded by its guard so the model-checked state space is finite.
const slotsProtocolSource = `
import(std)
Slots: protocol = {
  data { parked: [2]Bool, woken: [2]u32, last: u32 }
  init { parked: [2]Bool{ false, false }, woken: [2]u32{ 0, 0 }, last: u32(9) }
  initial Running
  park(who: u8): Running -> Running when u32(who) < u32(2) && !data.parked[u32(who)] then { data.parked[u32(who)] = true }
  wake(who: u8): Running -> Running when u32(who) < u32(2) && data.parked[u32(who)] && data.woken[u32(who)] < u32(2) then { data.parked[u32(who)] = false; data.woken[u32(who)] = data.woken[u32(who)] + u32(1); data.last = u32(who) }
  halt: Running -> Halted when data.parked[u32(0)] && data.parked[u32(1)]
}
`

func TestE2EProtocolArrayData(t *testing.T) {
	src := slotsProtocolSource + `
main: (): i32 {
  store: [1]SlotsData
  data: [*]SlotsData = span(&store)
  data[0] = slots_initial_data()
  s: SlotsState = slots_initial()
  assert(!slots_legal(s, data[0], .Wake(u8(0))) && !slots_legal(s, data[0], .Park(u8(2))))
  s = slots_next(s, data, .Park(u8(0)))
  assert(data[0].parked[u32(0)] && !data[0].parked[u32(1)])
  assert(!slots_legal(s, data[0], .Halt))
  s = slots_next(s, data, .Wake(u8(0)))
  assert(!data[0].parked[u32(0)] && data[0].woken[u32(0)] == u32(1) && data[0].last == u32(0))
  s = slots_next(s, data, .Park(u8(1)))
  s = slots_next(s, data, .Park(u8(0)))
  assert(slots_legal(s, data[0], .Halt))
  s = slots_next(s, data, .Halt)
  halted: Bool = s ? | .Halted => true | _ => false
  halted ? { 42 } | { 0 }
}
`
	code, abnormal := buildAndRun(t, "protocol_arrays", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestProtocolArrayTLAModule(t *testing.T) {
	tree, err := New().WithSource("slots.oak", slotsProtocolSource).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	module, err := ProtocolTLA(Protocols(tree)[0], "slots.oak")
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"CONSTANTS Who",
		"VARIABLES state, parked, woken, last",
		"/\\ parked = [k \\in 0..1 |-> FALSE]",
		"/\\ woken = [k \\in 0..1 |-> 0]",
		"/\\ last = 9",
		"Park(who) ==\n    state = \"Running\" /\\ ((who < 2) /\\ ~(parked[who])) /\\ state' = \"Running\" /\\ parked' = [parked EXCEPT ![who] = TRUE] /\\ UNCHANGED <<woken, last>>",
		"woken' = [woken EXCEPT ![who] = (woken[who] + 1)]",
		"last' = who",
		"Halt ==\n    state = \"Running\" /\\ (parked[0] /\\ parked[1]) /\\ state' = \"Halted\" /\\ UNCHANGED <<parked, woken, last>>",
		"/\\ parked \\in [0..1 -> BOOLEAN]",
		"/\\ woken \\in [0..1 -> Nat]",
	} {
		if !strings.Contains(module, want) {
			t.Errorf("module lacks %q:\n%s", want, module)
		}
	}
	// With TLC available, the generated module model-checks as is.
	jar := os.Getenv("OAK_TLA2TOOLS_JAR")
	java := "java"
	if _, err := exec.LookPath(java); err != nil || jar == "" {
		t.Skip("set OAK_TLA2TOOLS_JAR (and have java) to model-check the generated module")
	}
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "Slots.tla"), []byte(module), 0o644); err != nil {
		t.Fatal(err)
	}
	cfg := "SPECIFICATION Spec\nINVARIANTS TypeOK\nCONSTANTS\n    Who = {0, 1}\n"
	if err := os.WriteFile(filepath.Join(dir, "Slots.cfg"), []byte(cfg), 0o644); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, java, "-cp", jar, "tlc2.TLC", "-deadlock", "Slots.tla")
	cmd.Dir = dir
	out, err := cmd.CombinedOutput()
	if err != nil || !strings.Contains(string(out), "No error has been found") {
		t.Fatalf("TLC: %v\n%s", err, out)
	}
}
