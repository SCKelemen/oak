package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// Interval readings under an attested bound (stdlib/time.oak,
// docs/spec/110-testing.md "Simulated time"): the reading exists only
// while attested, spans wall ± bound, orders only definitely, and the
// simulation can break the bound or withdraw the attestation as faults
// that a scenario observes through timesim_interval_honest.
const timeIntervalProgram = `package main
import(std)
import("time")

interval_or_trap: (source: [*]time.TimeSource): time.TimeInterval {
  r: Result[time.TimeInterval, time.TimeError] = time.time_interval(source)
  r ? | .Ok(i) => i | .Err(e) => { assert(false)
    time.TimeInterval { earliest: time.instant_nanos(i64(0)), latest: time.instant_nanos(i64(0)) } }
}

refused: (source: [*]time.TimeSource): Bool {
  r: Result[time.TimeInterval, time.TimeError] = time.time_interval(source)
  r ? | .Ok(i) => false | .Err(e) => { e ? | .Unattested => true | _ => false }
}

overflowed_reading: (source: [*]time.TimeSource): Bool {
  r: Result[time.TimeInterval, time.TimeError] = time.time_interval(source)
  r ? | .Ok(i) => false | .Err(e) => { e ? | .Overflowed => true | _ => false }
}

main: (): i32 {
  store: [1]time.TimeSource
  source: [*]time.TimeSource = span(&store)
  source[0] = time.time_source_fixed(time.instant_nanos(i64(1000)))
  // Nobody vouched: the clock-ordered reading refuses.
  assert(refused(source))
  assert(!time.time_source_attest(source, time.duration_nanos(i64(0) - i64(1))))
  assert(refused(source))
  assert(time.time_source_attest(source, time.duration_nanos(i64(100))))
  a: time.TimeInterval = interval_or_trap(source)
  assert(a.earliest.nanos == i64(900) && a.latest.nanos == i64(1100))
  assert(time.time_interval_contains(a, time.instant_nanos(i64(1000))))
  assert(!time.time_interval_contains(a, time.instant_nanos(i64(1101))))
  assert(time.time_source_set(source, time.instant_nanos(i64(1300))))
  b: time.TimeInterval = interval_or_trap(source)
  assert(time.time_interval_before(a, b) && !time.time_interval_before(b, a))
  assert(time.time_source_set(source, time.instant_nanos(i64(1150))))
  c: time.TimeInterval = interval_or_trap(source)
  // Overlapping intervals are unordered either way.
  assert(!time.time_interval_before(a, c) && !time.time_interval_before(c, a))
  time.time_source_unattest(source)
  assert(refused(source))
  // A bound at the range end overflows the reading rather than wrapping.
  assert(time.time_source_attest(source, time.duration_nanos(i64(9223372036854775807))))
  assert(overflowed_reading(source))
  42
}
`

// The simulation side imports testing (the tape), so it runs in the
// interpreter and under the runner, never as a linked native program.
const timeIntervalSimProgram = `package main
import(std)
import("time")
import("timesim")
import(testing)

interval_or_trap: (source: [*]time.TimeSource): time.TimeInterval {
  r: Result[time.TimeInterval, time.TimeError] = time.time_interval(source)
  r ? | .Ok(i) => i | .Err(e) => { assert(false)
    time.TimeInterval { earliest: time.instant_nanos(i64(0)), latest: time.instant_nanos(i64(0)) } }
}

refused: (source: [*]time.TimeSource): Bool {
  r: Result[time.TimeInterval, time.TimeError] = time.time_interval(source)
  r ? | .Ok(i) => false | .Err(e) => { e ? | .Unattested => true | _ => false }
}

main: (): i32 {
  store: [1]time.TimeSource
  source: [*]time.TimeSource = span(&store)
  sim_store: [1]timesim.TimeSim
  sim: [*]timesim.TimeSim = span(&sim_store)
  tape_store: [1]TestChoices
  choices: [*]TestChoices = span(&tape_store)
  sevens: [64]u8
  i: u32 = u32(0)
  while i < u32(64) {
    sevens[i] = u8(7)
    i = i + u32(1)
  }
  data: []u8 = view(&sevens)

  // With no faults every reading is honest.
  source[0] = time.time_source_sim(time.instant_nanos(i64(0)))
  assert(time.time_source_attest(source, time.duration_nanos(i64(1000000))))
  timesim.timesim_init(sim, u32(0), i64(1000000))
  i = u32(0)
  while i < u32(20) {
    assert(timesim.timesim_advance(sim, source, time.duration_nanos(i64(1000000)), choices, data))
    assert(timesim.timesim_interval_honest(sim, source, interval_or_trap(source)))
    i = i + u32(1)
  }

  // A bound break: the attestation stands, the reading lies, and the
  // environment's check catches it.
  choices[0].offset = u32(0)
  source[0] = time.time_source_sim(time.instant_nanos(i64(0)))
  assert(time.time_source_attest(source, time.duration_nanos(i64(1000000))))
  timesim.timesim_init(sim, timesim.TIME_FAULT_BOUND_BREAK, i64(1000000))
  dishonest: u32 = u32(0)
  i = u32(0)
  while i < u32(8) {
    assert(timesim.timesim_advance(sim, source, time.duration_nanos(i64(1000000)), choices, data))
    assert(time.time_source_attested(source))
    !timesim.timesim_interval_honest(sim, source, interval_or_trap(source)) ? { dishonest = dishonest + u32(1) } | { }
    i = i + u32(1)
  }
  assert(sim[0].bound_breaks > u32(0) && dishonest > u32(0))

  // Withdrawn attestation: the reading refuses, the ledger counts it.
  choices[0].offset = u32(0)
  source[0] = time.time_source_sim(time.instant_nanos(i64(0)))
  assert(time.time_source_attest(source, time.duration_nanos(i64(1000000))))
  timesim.timesim_init(sim, timesim.TIME_FAULT_UNATTEST, i64(1000000))
  assert(timesim.timesim_advance(sim, source, time.duration_nanos(i64(1000000)), choices, data))
  assert(sim[0].unattested == u32(1) && refused(source))
  42
}
`

func timeIntervalModule(t *testing.T, program string) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"oak.mod":  "module example.com/time_interval_check\noak 0.1.0\n",
		"main.oak": program,
	})
}

func interpretModule(t *testing.T, root string) int64 {
	t.Helper()
	model, err := New().WithPackageDir(root).Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if e, isErr := evaluator.Eval(model.Tree.Root, env).(*object.Error); isErr {
		t.Fatalf("interpreter error evaluating program: %s", e.Message)
	}
	result := evaluator.Eval(parser.New(layout.New(scanner.New("main()"))).ParseProgram(), env)
	if e, isErr := result.(*object.Error); isErr {
		t.Fatalf("interpreter error in main(): %s", e.Message)
	}
	integer, ok := result.(*object.Integer)
	if !ok {
		t.Fatalf("main() returned %s", result.Inspect())
	}
	return integer.Value
}

func TestE2ETimeIntervalInterpreted(t *testing.T) {
	if got := interpretModule(t, timeIntervalModule(t, timeIntervalProgram)); got != 42 {
		t.Fatalf("main() returned %d, want 42", got)
	}
}

func TestE2ETimeIntervalCompiled(t *testing.T) {
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(timeIntervalModule(t, timeIntervalProgram)))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ETimeIntervalFaults(t *testing.T) {
	if got := interpretModule(t, timeIntervalModule(t, timeIntervalSimProgram)); got != 42 {
		t.Fatalf("main() returned %d, want 42", got)
	}
}
