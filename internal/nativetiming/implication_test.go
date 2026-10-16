package nativetiming

import (
	"errors"
	"io"
	"reflect"
	"sync"
	"testing"
	"time"
)

// These controls describe one process-current wall state. They intentionally
// make no inference about active goroutine depth or inclusive/CPU duration.
func requireImplicationSnapshot(t *testing.T, h *harness, phase string, started, finished uint64) record {
	t.Helper()
	a, b := h.s.snapshot("test"), h.s.snapshot("test")
	if !reflect.DeepEqual(a, b) {
		t.Fatal("repeated snapshot charged time twice")
	}
	if a.Phase != phase || a.Totals.ImplicationsStarted != started || a.Totals.ImplicationsFinished != finished {
		t.Fatalf("phase/counts = %q/%d/%d; want %q/%d/%d", a.Phase, a.Totals.ImplicationsStarted, a.Totals.ImplicationsFinished, phase, started, finished)
	}
	return a
}

func TestImplicationExclusiveNestedScopes(t *testing.T) {
	h := newHarness(t, maxRecords, maxBytes)
	loops := BeginLoops(2, 3, 4, false)
	Coupling(5, 6, 7)
	h.clock.advance(time.Second)
	outer := BeginImplication()
	h.clock.advance(2 * time.Second)
	inner := BeginImplication()
	h.clock.advance(3 * time.Second)
	valuationDone := BeginValuation(8, 9, 10, 11, 12)
	h.clock.advance(5 * time.Second)
	requireImplicationSnapshot(t, h, "valuation", 2, 0)
	valuationDone(13)
	valuationDone(99)
	if r := requireImplicationSnapshot(t, h, "implication", 2, 0); r.Current.Nodes != 0 || r.Current.CheckedWitnesses != 5 {
		t.Fatal("valuation context leaked into restored implication")
	}
	h.clock.advance(7 * time.Second)
	inner()
	inner()
	requireImplicationSnapshot(t, h, "implication", 2, 1)
	h.clock.advance(11 * time.Second)
	outer()
	outer()
	requireImplicationSnapshot(t, h, "coupling", 2, 2)
	h.clock.advance(13 * time.Second)
	loops()
	r := requireImplicationSnapshot(t, h, "idle", 2, 2)
	want := phaseCosts{Coupling: uint64(14 * time.Second), Implication: uint64(23 * time.Second), Valuation: uint64(5 * time.Second)}
	if r.Totals.PhaseNS != want || r.ElapsedNS != uint64(42*time.Second) || r.Totals.LoopNS != uint64(42*time.Second) {
		t.Fatalf("exclusive partition: elapsed=%d totals=%+v; want %+v", r.ElapsedNS, r.Totals, want)
	}
	if len(decode(t, h.out.data())) != 1 {
		t.Fatal("implication hooks emitted per-call records")
	}
}

func TestImplicationOutOfOrderConcurrentScopes(t *testing.T) {
	for _, mixed := range []bool{false, true} {
		name := "same_phase"
		if mixed {
			name = "valuation_child"
		}
		t.Run(name, func(t *testing.T) {
			h := newHarness(t, maxRecords, maxBytes)
			loops := BeginLoops(1, 1, 1, false)
			Coupling(1, 1, 1)
			// A and B enter on different goroutines and their scopes overlap.
			// Barrier receipt, not scheduling speed, determines the clock order.
			enter := func() func() {
				c := make(chan func(), 1)
				go func() { c <- BeginImplication() }()
				select {
				case finish := <-c:
					return finish
				case <-time.After(5 * time.Second):
					t.Fatal("entry did not make progress")
					return nil
				}
			}
			finish := func(done func()) {
				c := make(chan struct{})
				go func() { done(); done(); close(c) }()
				await(t, c)
			}
			h.clock.advance(time.Second)
			a := enter()
			h.clock.advance(2 * time.Second)
			b := enter()
			h.clock.advance(3 * time.Second)
			var valuationDone func(uint32)
			if mixed {
				valuationDone = BeginValuation(1, 1, 1, 1, 1)
				h.clock.advance(5 * time.Second)
			}
			finish(a) // A must not displace B or its valuation child.
			current := "implication"
			if mixed {
				current = "valuation"
			}
			requireImplicationSnapshot(t, h, current, 2, 1)
			if mixed {
				valuationDone(1)
				requireImplicationSnapshot(t, h, "implication", 2, 1)
			}
			h.clock.advance(7 * time.Second)
			finish(b) // B skips ended A and restores the coupling scope.
			requireImplicationSnapshot(t, h, "coupling", 2, 2)
			h.clock.advance(11 * time.Second)
			loops()
			r := requireImplicationSnapshot(t, h, "idle", 2, 2)
			want := phaseCosts{Coupling: uint64(12 * time.Second), Implication: uint64(12 * time.Second)}
			if mixed {
				want.Valuation = uint64(5 * time.Second)
			}
			if r.Totals.PhaseNS != want || r.ElapsedNS != want.Coupling+want.Implication+want.Valuation {
				t.Fatalf("process-current partition: %+v; want %+v", r, want)
			}
		})
	}
}

func TestImplicationSupersededSameSessionFinish(t *testing.T) {
	h := newHarness(t, maxRecords, maxBytes)
	oldSearch := BeginSearch("old")
	h.clock.advance(time.Second)
	old := BeginImplication()
	h.clock.advance(2 * time.Second)
	newSearch := BeginSearch("new")
	h.clock.advance(3 * time.Second)
	fresh := BeginImplication()
	h.clock.advance(5 * time.Second)
	old()
	old()
	oldSearch(0, 0, 0, false)
	r := requireImplicationSnapshot(t, h, "implication", 2, 1)
	if r.Current.Function != "new" || r.Current.FunctionOrdinal != 2 {
		t.Fatal("superseded callback restored old search/context")
	}
	fresh()
	newSearch(0, 0, 0, false)
	r = requireImplicationSnapshot(t, h, "idle", 2, 2)
	if r.Totals.SearchesCompleted != 2 || r.Totals.PhaseNS.Search != uint64(4*time.Second) || r.Totals.PhaseNS.Implication != uint64(7*time.Second) {
		t.Fatalf("same-session superseded finish/partition changed: %+v", r.Totals)
	}
}

func TestImplicationCloseFreezesOpenScope(t *testing.T) {
	if Enabled() {
		t.Fatal("unexpected active observer")
	}
	BeginImplication()()
	h := newHarness(t, maxRecords, maxBytes)
	late := BeginImplication()
	h.clock.advance(7 * time.Second)
	if err := h.s.Close(); err != nil {
		t.Fatal(err)
	}
	frozen := requireImplicationSnapshot(t, h, "implication", 1, 0)
	if frozen.Totals.PhaseNS.Implication != uint64(7*time.Second) {
		t.Fatalf("Close did not freeze implication time: %+v", frozen)
	}
	h.clock.advance(11 * time.Second)
	late()
	late()
	BeginImplication()()
	if after := h.s.snapshot("test"); !reflect.DeepEqual(after, frozen) {
		t.Fatal("post-Close callback/snapshot changed frozen state")
	}
	h2 := newHarness(t, maxRecords, maxBytes)
	fresh := BeginImplication()
	late()
	if err := h.s.Close(); err != nil {
		t.Fatal(err)
	}
	requireImplicationSnapshot(t, h2, "implication", 1, 0)
	fresh()
	requireImplicationSnapshot(t, h2, "idle", 1, 1)
}

func TestImplicationWriterFailureFreezesCounts(t *testing.T) {
	for _, event := range []string{"status", "close"} {
		for _, failure := range []string{"error", "short"} {
			t.Run(event+"_"+failure, func(t *testing.T) {
				h := newHarness(t, maxRecords, maxBytes)
				late := BeginImplication()
				want := errors.New("writer failed")
				if failure == "short" {
					want = io.ErrShortWrite
				}
				h.s.writer = writeFunc(func(p []byte) (int, error) {
					if failure == "short" {
						return len(p) - 1, nil
					}
					return 0, want
				})
				h.clock.advance(interval)
				if event == "status" {
					h.ticker.ticks <- h.clock.now()
					await(t, h.s.done)
				}
				if err := h.s.Close(); !errors.Is(err, want) {
					t.Fatalf("Close = %v, want %v", err, want)
				}
				late()
				r := requireImplicationSnapshot(t, h, "implication", 1, 0)
				if r.Totals.PhaseNS.Implication != uint64(interval) || Enabled() || !h.ticker.stopped.Load() {
					t.Fatal("write failure/Close did not freeze and join")
				}
			})
		}
	}
}

func TestImplicationBlockedWriterAndConcurrentClose(t *testing.T) {
	h := newHarness(t, maxRecords, maxBytes)
	entered, release := make(chan struct{}), make(chan struct{})
	var blocked, released sync.Once
	releaseWriter := func() { released.Do(func() { close(release) }) }
	// Release precedes the harness cleanup even if an assertion fails.
	t.Cleanup(releaseWriter)
	h.s.writer = writeFunc(func(p []byte) (int, error) {
		blocked.Do(func() { close(entered); <-release })
		return h.out.Write(p)
	})
	late := BeginImplication()
	h.clock.advance(interval)
	h.ticker.ticks <- h.clock.now()
	await(t, entered)
	hooksDone := make(chan struct{})
	go func() { BeginImplication()(); close(hooksDone) }()
	await(t, hooksDone)
	requireImplicationSnapshot(t, h, "implication", 2, 1)
	closing, closed := make(chan struct{}), make(chan struct{})
	go func() { close(closing); _ = h.s.Close(); close(closed) }()
	await(t, closing)
	select {
	case <-closed:
		t.Fatal("Close returned while controlled writer was blocked")
	default:
	}
	releaseWriter()
	await(t, closed)
	late()
	requireImplicationSnapshot(t, h, "implication", 2, 1)
	if Enabled() || !h.ticker.stopped.Load() {
		t.Fatal("Close did not join writer/logger")
	}
}

func TestImplicationDisabledNoAllocations(t *testing.T) {
	if Enabled() {
		t.Fatal("unexpected active observer")
	}
	if got := testing.AllocsPerRun(100, func() { BeginImplication()() }); got != 0 {
		t.Fatalf("disabled pair allocs = %v, want zero", got)
	}
}

func BenchmarkImplicationObserver(b *testing.B) {
	for _, name := range []string{"disabled_pair", "enabled_pair", "enabled_nested_valuation"} {
		b.Run(name, func(b *testing.B) {
			if Enabled() {
				b.Fatal("unexpected active observer")
			}
			if name != "disabled_pair" {
				// The real production clock and an untriggered ticker retain clock
				// costs without per-iteration logger I/O.
				// Session setup and the single start/close records are unmeasured.
				tick := &testTicker{ticks: make(chan time.Time), ready: make(chan struct{}, 1)}
				s, err := start(io.Discard, config{now: time.Now, newTicker: func(time.Duration) ticker { return tick }, recordCap: maxRecords, byteCap: maxBytes})
				if err != nil {
					b.Fatal(err)
				}
				b.Cleanup(func() { _ = s.Close() })
			}
			b.ReportAllocs()
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				done := BeginImplication()
				if name == "enabled_nested_valuation" {
					nested := BeginImplication()
					BeginValuation(1, 1, 1, 1, 1)(1)
					nested()
				}
				done()
			}
			b.StopTimer()
		})
	}
}
