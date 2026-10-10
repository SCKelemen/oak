package nativetiming

import (
	"bytes"
	"encoding/json"
	"errors"
	"io"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
	"unicode/utf8"
)

type testClock struct{ ns atomic.Int64 }

func (c *testClock) now() time.Time          { return time.Unix(0, c.ns.Load()) }
func (c *testClock) advance(d time.Duration) { c.ns.Add(int64(d)) }

type testTicker struct {
	ticks   chan time.Time
	ready   chan struct{}
	stopped atomic.Bool
}

func (t *testTicker) channel() <-chan time.Time {
	select {
	case t.ready <- struct{}{}:
	default:
	}
	return t.ticks
}

func (t *testTicker) stop() { t.stopped.Store(true) }

type lockedBuffer struct {
	mu sync.Mutex
	b  bytes.Buffer
}

func (b *lockedBuffer) Write(p []byte) (int, error) {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.b.Write(p)
}

func (b *lockedBuffer) data() []byte {
	b.mu.Lock()
	defer b.mu.Unlock()
	return bytes.Clone(b.b.Bytes())
}

type harness struct {
	s      *Session
	clock  *testClock
	ticker *testTicker
	out    *lockedBuffer
}

func newHarness(t *testing.T, records, bytes int) *harness {
	t.Helper()
	c := &testClock{}
	tick := &testTicker{ticks: make(chan time.Time), ready: make(chan struct{}, 1)}
	out := &lockedBuffer{}
	s, err := start(out, config{
		now: c.now,
		newTicker: func(d time.Duration) ticker {
			if d != interval {
				t.Errorf("ticker interval = %s, want %s", d, interval)
			}
			return tick
		},
		recordCap: records,
		byteCap:   bytes,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = s.Close() })
	await(t, tick.ready)
	return &harness{s: s, clock: c, ticker: tick, out: out}
}

func await(t *testing.T, ch <-chan struct{}) {
	t.Helper()
	select {
	case <-ch:
	case <-time.After(5 * time.Second):
		t.Fatal("logger did not make progress")
	}
}

// channel() signals that the prior tick is fully processed, including its write.
// Tests can therefore inspect output without scheduler sleeps or polling.
func (h *harness) tick(t *testing.T, d time.Duration) {
	t.Helper()
	h.clock.advance(d)
	select {
	case h.ticker.ticks <- h.clock.now():
	case <-time.After(5 * time.Second):
		t.Fatal("logger did not receive tick")
	}
	await(t, h.ticker.ready)
}

func decode(t *testing.T, data []byte) []record {
	t.Helper()
	var records []record
	d := json.NewDecoder(bytes.NewReader(data))
	for {
		var r record
		if err := d.Decode(&r); err == io.EOF {
			break
		} else if err != nil {
			t.Fatal(err)
		}
		records = append(records, r)
	}
	return records
}

func TestDisabledCleanupAndReenable(t *testing.T) {
	if Enabled() {
		t.Fatal("unexpected session")
	}
	BeginSearch("disabled")(1, 2, 3, true)
	BeginValidation("disabled")(9, true)
	BeginLoops(1, 2, 3, true)()
	Coupling(1, 2, 3)
	BeginValuation(1, 2, 3, 4, 5)(6)
	if _, err := Start(nil); err == nil {
		t.Fatal("accepted nil writer")
	}
	h := newHarness(t, maxRecords, maxBytes)
	if !Enabled() {
		t.Fatal("session not enabled")
	}
	if _, err := Start(io.Discard); err == nil {
		t.Fatal("accepted overlapping session")
	}
	stale := BeginSearch("old")
	if err := h.s.Close(); err != nil {
		t.Fatal(err)
	}
	if Enabled() || !h.ticker.stopped.Load() {
		t.Fatal("Close did not disable and join logger")
	}
	h2 := newHarness(t, maxRecords, maxBytes)
	fresh := BeginSearch("new")
	stale(100, 100, 100, true)
	if got := h2.s.snapshot("test"); got.Current.Function != "new" || got.Totals.SearchesCompleted != 0 {
		t.Fatalf("stale closure affected new session: %+v", got)
	}
	fresh(1, 2, 3, false)
	if err := h.s.Close(); err != nil {
		t.Fatal(err)
	}
	if !Enabled() {
		t.Fatal("old Close cleared new session")
	}
	if err := h2.s.Close(); err != nil {
		t.Fatal(err)
	}
	for _, h := range []*harness{h, h2} {
		r := decode(t, h.out.data())
		if len(r) != 2 || r[0].Event != "start" || r[1].Event != "close" {
			t.Fatalf("lifecycle records: %+v", r)
		}
	}
}

func TestNestedPhasesRestoreAndAccount(t *testing.T) {
	h := newHarness(t, maxRecords, maxBytes)
	searchDone := BeginSearch("function")
	h.clock.advance(time.Second)
	validationDone := BeginValidation("candidate")
	h.clock.advance(2 * time.Second)
	loopsDone := BeginLoops(2, 3, 4, true)
	h.clock.advance(3 * time.Second)
	Coupling(5, 6, 7)
	h.clock.advance(4 * time.Second)
	valuationDone := BeginValuation(8, 9, 10, 11, 12)
	h.clock.advance(5 * time.Second)
	r := h.s.snapshot("test")
	if r.Phase != "valuation" || r.PhaseAgeNS != uint64(5*time.Second) || r.FunctionAgeNS != uint64(15*time.Second) || r.CandidateAgeNS != uint64(14*time.Second) || r.Current.Nodes != 8 || r.Current.CandidateOrdinal != 1 {
		t.Fatalf("valuation state: %+v", r)
	}
	valuationDone(13)
	valuationDone(1000) // Scope completion is idempotent.
	r = h.s.snapshot("test")
	if r.Phase != "coupling" || r.PhaseAgeNS != uint64(9*time.Second) || r.Current.Nodes != 0 || r.Current.CheckedWitnesses != 5 {
		t.Fatalf("coupling restoration: %+v", r)
	}
	h.clock.advance(6 * time.Second)
	loopsDone()
	r = h.s.snapshot("test")
	if r.Phase != "validation" || r.Current.ASMLoops != 0 || r.Current.Candidate != "candidate" {
		t.Fatalf("validation restoration: %+v", r)
	}
	h.clock.advance(7 * time.Second)
	validationDone(3, true)
	r = h.s.snapshot("test")
	if r.Phase != "search" || r.Current.Candidate != "" {
		t.Fatalf("search restoration: %+v", r)
	}
	h.clock.advance(8 * time.Second)
	searchDone(14, 15, 16, true)
	r = h.s.snapshot("test")
	want := totals{
		SearchesStarted: 1, SearchesCompleted: 1, SearchesFailed: 1, SearchNS: uint64(36 * time.Second),
		Considered: 14, Materialized: 15, SearchValidations: 16,
		ValidationsStarted: 1, ValidationsCompleted: 1, ValidationNS: uint64(27 * time.Second), Cached: 1, LastOutcome: 3,
		LoopsStarted: 1, LoopsCompleted: 1, LoopNS: uint64(18 * time.Second),
		Couplings: 1, CheckedWitnesses: 5, WitnessWork: 6, Slots: 7,
		ValuationsStarted: 1, ValuationsCompleted: 1, ValuationNS: uint64(5 * time.Second), Evaluations: 13,
		PhaseNS: phaseCosts{Search: uint64(9 * time.Second), Validation: uint64(9 * time.Second), Witnesses: uint64(3 * time.Second), Coupling: uint64(10 * time.Second), Valuation: uint64(5 * time.Second)},
	}
	if r.Phase != "idle" || r.Totals != want {
		t.Fatalf("accounting = %+v; want %+v", r, want)
	}
	if r.LastSearch.Function != "function" || r.LastSearch.NS != uint64(36*time.Second) || !r.LastSearch.Failed {
		t.Fatalf("last completed search: %+v", r.LastSearch)
	}
}

func TestOutOfOrderAndSupersededScopes(t *testing.T) {
	h := newHarness(t, maxRecords, maxBytes)
	oldSearch := BeginSearch("old")
	oldValidation := BeginValidation("old candidate")
	oldLoops := BeginLoops(1, 1, 1, false)
	oldValidation(1, false)
	if got := h.s.snapshot("test").Phase; got != "witnesses" {
		t.Fatalf("outer completion displaced child: %s", got)
	}
	oldLoops()
	if got := h.s.snapshot("test").Phase; got != "search" {
		t.Fatalf("restored ended validation: %s", got)
	}
	oldValidation2 := BeginValidation("old candidate 2")
	newSearch := BeginSearch("new")
	newValidation := BeginValidation("new candidate")
	oldSearch(1, 1, 1, false)
	oldValidation2(1, false)
	r := h.s.snapshot("test")
	if r.Current.Function != "new" || r.Current.FunctionOrdinal != 2 || r.Current.CandidateOrdinal != 1 || r.Phase != "validation" {
		t.Fatalf("stale completion restored obsolete scope: %+v", r)
	}
	newValidation(2, false)
	newSearch(1, 1, 1, false)
	r = h.s.snapshot("test")
	if r.Phase != "idle" || r.Totals.SearchesCompleted != 2 || r.Totals.ValidationsCompleted != 3 {
		t.Fatalf("completion totals: %+v", r)
	}
}

func TestSamplingRateAndRecordCap(t *testing.T) {
	h := newHarness(t, 4, maxBytes)
	done := BeginSearch("fast")
	for i := 0; i < 20; i++ {
		BeginValidation("candidate")(i, false)
	}
	done(20, 20, 20, false)
	if got := len(decode(t, h.out.data())); got != 1 {
		t.Fatalf("hooks wrote %d records", got)
	}
	h.tick(t, interval-time.Nanosecond)
	if got := len(decode(t, h.out.data())); got != 1 {
		t.Fatal("status emitted before five seconds")
	}
	h.tick(t, time.Nanosecond)
	h.tick(t, 0)
	h.tick(t, interval)
	h.tick(t, interval)
	h.tick(t, interval)
	if err := h.s.Close(); err != nil {
		t.Fatal(err)
	}
	r := decode(t, h.out.data())
	if len(r) != 4 || r[3].Event != "close" || !r[3].OutputLimited {
		t.Fatalf("record cap: %+v", r)
	}
	for i, event := range r {
		if event.Sequence != i+1 {
			t.Fatalf("sequence = %d at %d", event.Sequence, i)
		}
	}
	if r[1].ElapsedNS != uint64(interval) || r[2].ElapsedNS != uint64(2*interval) || r[3].Totals.ValidationsCompleted != 20 {
		t.Fatalf("rate or coalesced totals incorrect: %+v", r)
	}
}

func TestByteCapReservesClose(t *testing.T) {
	const cap = 2 * maxRecordBytes
	h := newHarness(t, maxRecords, cap)
	BeginSearch(strings.Repeat("\\\"", 1000))
	BeginValidation(strings.Repeat("\n", 1000))
	for i := 0; i < 30; i++ {
		h.tick(t, interval)
	}
	if err := h.s.Close(); err != nil {
		t.Fatal(err)
	}
	data := h.out.data()
	r := decode(t, data)
	if len(data) > cap || !r[len(r)-1].OutputLimited || r[len(r)-1].Event != "close" {
		t.Fatalf("byte cap failed: bytes=%d final=%+v", len(data), r[len(r)-1])
	}
}

func TestIdentifiersAndNumericJSONAreBounded(t *testing.T) {
	input := strings.Repeat("界", 100)
	a, b := identifier(input), identifier(input+"x")
	if len(a) > maxIdentifier || !utf8.ValidString(a) || a != identifier(input) || a == b {
		t.Fatalf("identifier bounds or hash: %q %q", a, b)
	}
	if identifier("short") != "short" {
		t.Fatal("changed short identifier")
	}
	r := record{Event: "status", Phase: "valuation"}
	minInt := -int64(1) << (strconv.IntSize - 1)
	// Maximize all numbers and escaping to check the reserved record size.
	var fill func(reflect.Value)
	fill = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				fill(v.Field(i))
			}
		case reflect.Uint64:
			v.SetUint(^uint64(0))
		case reflect.Int:
			v.SetInt(minInt)
		case reflect.String:
			v.SetString(strings.Repeat("\x00", maxIdentifier))
		}
	}
	fill(reflect.ValueOf(&r).Elem())
	aJSON, err := json.Marshal(r)
	if err != nil {
		t.Fatal(err)
	}
	bJSON, err := json.Marshal(r)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(aJSON, bJSON) || len(aJSON)+1 > maxRecordBytes {
		t.Fatalf("unstable or oversized record: %d", len(aJSON))
	}
	// The worst-case width must still cover 45 minutes of five-second samples,
	// plus start/close, even after reserving the close record's maximum budget.
	if (len(aJSON)+1)*542+maxRecordBytes > maxBytes {
		t.Fatalf("45-minute record budget is too small: record=%d", len(aJSON)+1)
	}
	if !bytes.Contains(aJSON, []byte(`"evaluations":18446744073709551615`)) || !bytes.Contains(aJSON, []byte(`"last_outcome":`+strconv.FormatInt(minInt, 10))) {
		t.Fatal("numeric fields lost exact integer representation")
	}
}

func TestFullPublicRecordLimit(t *testing.T) {
	h := newHarness(t, maxRecords, maxBytes)
	BeginSearch("long running")
	for i := 0; i < maxRecords+1; i++ {
		h.tick(t, interval)
	}
	if err := h.s.Close(); err != nil {
		t.Fatal(err)
	}
	r := decode(t, h.out.data())
	if len(r) != maxRecords || len(h.out.data()) > maxBytes || !r[len(r)-1].OutputLimited {
		t.Fatalf("public limits: records=%d bytes=%d", len(r), len(h.out.data()))
	}
	for _, event := range r {
		if event.Schema != "oak.native.timing.v1" {
			t.Fatalf("schema = %q", event.Schema)
		}
	}
}

type writeFunc func([]byte) (int, error)

func (f writeFunc) Write(p []byte) (int, error) { return f(p) }

func TestWriteErrorsAndShortWrites(t *testing.T) {
	want := errors.New("writer failed")
	for _, tc := range []struct {
		name   string
		writer io.Writer
		want   error
	}{
		{"error", writeFunc(func([]byte) (int, error) { return 0, want }), want},
		{"short", writeFunc(func(p []byte) (int, error) { return len(p) - 1, nil }), io.ErrShortWrite},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if s, err := Start(tc.writer); s != nil || !errors.Is(err, tc.want) {
				t.Fatalf("Start = %v, %v", s, err)
			}
			if Enabled() {
				t.Fatal("failed Start left session active")
			}
		})
	}
	for _, failOn := range []int{2, 3} {
		t.Run(string(rune('0'+failOn)), func(t *testing.T) {
			h := newHarness(t, maxRecords, maxBytes)
			// Start has returned and the logger is waiting for a tick.
			writes := 1
			h.s.writer = writeFunc(func(p []byte) (int, error) {
				writes++
				if writes == failOn {
					return 0, want
				}
				return h.out.Write(p)
			})
			if failOn == 2 {
				h.clock.advance(interval)
				h.ticker.ticks <- h.clock.now()
				await(t, h.s.done)
			} else {
				h.tick(t, interval)
			}
			if err := h.s.Close(); !errors.Is(err, want) {
				t.Fatalf("Close = %v", err)
			}
			if Enabled() || !h.ticker.stopped.Load() {
				t.Fatal("write error cleanup incomplete")
			}
		})
	}
}

func TestBlockedWriterDoesNotHoldStateLockAndCloseJoins(t *testing.T) {
	h := newHarness(t, maxRecords, maxBytes)
	entered, release := make(chan struct{}), make(chan struct{})
	var once sync.Once
	h.s.writer = writeFunc(func(p []byte) (int, error) {
		once.Do(func() { close(entered); <-release })
		return h.out.Write(p)
	})
	h.clock.advance(interval)
	h.ticker.ticks <- h.clock.now()
	await(t, entered)
	hooksDone := make(chan struct{})
	go func() { BeginSearch("while writing")(1, 1, 1, false); close(hooksDone) }()
	await(t, hooksDone)
	closing, closed := make(chan struct{}), make(chan struct{})
	go func() { close(closing); _ = h.s.Close(); close(closed) }()
	await(t, closing)
	select {
	case <-closed:
		t.Fatal("Close returned before writer finished")
	default:
	}
	close(release)
	await(t, closed)
	if Enabled() || !h.ticker.stopped.Load() {
		t.Fatal("logger not joined")
	}
}

func TestConcurrentHooksAndClose(t *testing.T) {
	h := newHarness(t, maxRecords, maxBytes)
	const workers, iterations = 8, 40
	var wg sync.WaitGroup
	for worker := 0; worker < workers; worker++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := 0; i < iterations; i++ {
				s := BeginSearch("concurrent")
				v := BeginValidation("candidate")
				l := BeginLoops(1, 1, 1, false)
				Coupling(1, 1, 1)
				x := BeginValuation(1, 1, 1, 1, 1)
				x(1)
				l()
				v(1, false)
				s(1, 1, 1, false)
			}
		}()
	}
	wg.Wait()
	r := h.s.snapshot("test")
	if r.Totals.SearchesCompleted != workers*iterations || r.Totals.ValidationsCompleted != workers*iterations || r.Totals.ValuationsCompleted != workers*iterations {
		t.Fatalf("concurrent totals: %+v", r.Totals)
	}
	for i := 0; i < workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < iterations; j++ {
				BeginSearch("closing")(1, 1, 1, false)
			}
			_ = h.s.Close()
		}()
	}
	wg.Wait()
	if Enabled() {
		t.Fatal("concurrent Close left session active")
	}
}
