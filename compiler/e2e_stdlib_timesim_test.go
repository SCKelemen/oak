package compiler

import (
	"fmt"
	"strings"
	"testing"
	"time"
)

// TimeSource (stdlib/time.oak, "Time sources"): a fixed source never moves
// on its own, a simulated source advances both clocks together and a wall
// step leaves the monotonic clock alone, a native source traps until it is
// refreshed and never lets the monotonic clock regress. Compiled through
// the module loader so the qualified names are the ones consumers write.
func TestE2EStdlibTimeSource(t *testing.T) {
	src := `package main
import(std)
import("time")

main: (): i32 {
  store: [1]time.TimeSource
  source: [*]time.TimeSource = span(&store)
  source[0] = time.time_source_fixed(time.instant_nanos(i64(5000)))
  assert(time.time_now(source).nanos == i64(5000) && time.time_monotonic(source).nanos == i64(0))
  assert(!time.time_source_advance(source, time.duration_nanos(i64(7))))
  assert(time.time_source_set(source, time.instant_nanos(i64(9000))))
  assert(time.time_now(source).nanos == i64(9000) && time.time_monotonic(source).nanos == i64(0))
  assert(!time.time_source_refresh(source, i64(1), i64(2)))

  source[0] = time.time_source_sim(time.instant_nanos(i64(100)))
  assert(time.time_source_advance(source, time.duration_nanos(i64(250))))
  assert(time.time_now(source).nanos == i64(350) && time.time_monotonic(source).nanos == i64(250))
  assert(!time.time_source_advance(source, time.duration_nanos(i64(0) - i64(1))))
  assert(time.time_source_shift_wall(source, i64(0) - i64(1000)))
  assert(time.time_now(source).nanos == i64(0) - i64(650) && time.time_monotonic(source).nanos == i64(250))
  deadline: Result[time.Duration, time.TimeError] = time.time_deadline(source, time.duration_nanos(i64(100)))
  at: i64 = deadline ? | .Ok(d) => d.nanos | .Err(e) => i64(0)
  assert(at == i64(350))
  assert(!time.time_expired(source, time.duration_nanos(at)))
  assert(time.time_remaining(source, time.duration_nanos(at)).nanos == i64(100))
  assert(time.time_source_advance(source, time.duration_nanos(i64(100))))
  assert(time.time_expired(source, time.duration_nanos(at)))
  assert(time.time_remaining(source, time.duration_nanos(at)).nanos == i64(0))
  assert(time.time_elapsed(source, time.duration_nanos(i64(250))).nanos == i64(100))
  // Advancing past the range is refused and changes nothing.
  assert(!time.time_source_advance(source, time.duration_nanos(i64(9223372036854775807))))
  assert(time.time_monotonic(source).nanos == i64(350))

  source[0] = time.time_source_native()
  assert(!time.time_source_advance(source, time.duration_nanos(i64(1))))
  assert(!time.time_source_set(source, time.instant_nanos(i64(1))))
  assert(time.time_source_refresh(source, i64(1700000000000000000), i64(500)))
  assert(time.time_now(source).nanos == i64(1700000000000000000) && time.time_monotonic(source).nanos == i64(0))
  assert(time.time_source_refresh(source, i64(1700000000000000010), i64(800)))
  assert(time.time_monotonic(source).nanos == i64(300))
  // A host whose monotonic reading went backwards is clamped, not believed.
  assert(time.time_source_refresh(source, i64(1600000000000000000), i64(700)))
  assert(time.time_monotonic(source).nanos == i64(300) && time.time_now(source).nanos == i64(1600000000000000000))
  assert(time.time_source_refresh(source, i64(1600000000000000000), i64(900)))
  assert(time.time_monotonic(source).nanos == i64(400))
  42
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/timesource\noak 0.1.0\n",
		"main.oak": src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Reading a native source before any refresh traps: forgetting the platform
// refresh fails closed instead of reporting the epoch.
func TestE2EStdlibTimeSourceUnrefreshedTraps(t *testing.T) {
	src := `package main
import(std)
import("time")

main: (): i32 {
  store: [1]time.TimeSource
  source: [*]time.TimeSource = span(&store)
  source[0] = time.time_source_native()
  now: time.Instant = time.time_now(source)
  now.nanos == i64(0) ? { 1 } | { 2 }
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/timesource_trap\noak 0.1.0\n",
		"main.oak": src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if !abnormal && code == 0 {
		t.Fatalf("expected a trap, got exit=(%d,%v)", code, abnormal)
	}
}

// The native realization (stdlib/timenative.oak) in pure Oak — the clock
// ids as target constants, clock_gettime as an extern, the timespec through
// c.out, nothing linked but the C library: the wall clock is after 2020 and
// before 2100 and within a minute of Go's own reading, the monotonic clock
// starts at zero and never decreases across refreshes.
func TestE2EStdlibTimeNative(t *testing.T) {
	skipWithoutPosixSpawn(t)
	nowNanos := time.Now().UnixNano()
	src := `package main
import(std)
import("time")
import("timenative")

main: (): i32 {
  store: [1]time.TimeSource
  source: [*]time.TimeSource = span(&store)
  timenative.timenative_source(source)
  first: time.Instant = time.time_now(source)
  assert(first.nanos > i64(1577836800000000000) && first.nanos < i64(4102444800000000000))
  assert(first.nanos > i64(WALL_LOW) && first.nanos < i64(WALL_HIGH))
  assert(time.time_monotonic(source).nanos == i64(0))
  i: u32 = u32(0)
  last: i64 = i64(0)
  while i < u32(1000) {
    assert(timenative.timenative_refresh(source))
    mono: i64 = time.time_monotonic(source).nanos
    assert(mono >= last)
    last = mono
    i = i + u32(1)
  }
  // A fixed source handed to the platform layer is refused, not overwritten.
  source[0] = time.time_source_fixed(time.instant_nanos(i64(7)))
  assert(!timenative.timenative_refresh(source))
  assert(time.time_now(source).nanos == i64(7))
  42
}
`
	// Within a minute of Go's wall clock, either way.
	src = strings.NewReplacer(
		"WALL_LOW", fmt.Sprintf("%d", nowNanos-60*time.Second.Nanoseconds()),
		"WALL_HIGH", fmt.Sprintf("%d", nowNanos+60*time.Second.Nanoseconds()),
	).Replace(src)
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/timenative_check\noak 0.1.0\n",
		"main.oak": src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
