package asm

import (
	"bytes"
	"encoding/json"
	"io"
	"reflect"
	"runtime"
	"sort"
	"strconv"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/nativetiming"
)

// These controls bind the real private implication wrapper to its unchanged
// direct-Depth baseline. They intentionally do not run in parallel: observation
// has one process-wide active session. They neither load producer inputs nor
// inspect source files/caches. The existing post_exhaustion controls are separate
// and must remain in the focused regression plan.
//
// ASM can only use the observer's public API. Close joins the logger before this
// file reads its in-memory JSON. Closing with the enclosing coupling still open
// checks restoration without timing thresholds or a new production snapshot API.
// Exact fake-clock attribution belongs in internal/nativetiming's controls.

type implicationTimingRecord struct {
	Event  string `json:"event"`
	Phase  string `json:"phase"`
	Totals struct {
		Started   uint64            `json:"implications_started"`
		Finished  uint64            `json:"implications_finished"`
		Valuation uint64            `json:"valuations_started"`
		PhaseNS   map[string]uint64 `json:"exclusive_phase_ns"`
	} `json:"totals"`
}

type implicationTimingObservation struct {
	session *nativetiming.Session
	output  bytes.Buffer
}

func implicationTimingStart(t *testing.T) *implicationTimingObservation {
	t.Helper()
	if nativetiming.Enabled() {
		t.Fatal("another observation session is active; these controls must be serial")
	}
	o := new(implicationTimingObservation)
	var err error
	o.session, err = nativetiming.Start(&o.output)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if err := o.session.Close(); err != nil {
			t.Error(err)
		}
	})
	return o
}

func (o *implicationTimingObservation) closeRecord(t *testing.T) implicationTimingRecord {
	t.Helper()
	if err := o.session.Close(); err != nil {
		t.Fatal(err)
	}
	decoder := json.NewDecoder(bytes.NewReader(o.output.Bytes()))
	var last implicationTimingRecord
	closes := 0
	for {
		var row implicationTimingRecord
		if err := decoder.Decode(&row); err == io.EOF {
			break
		} else if err != nil {
			t.Fatal(err)
		}
		if row.Event == "close" {
			closes++
		}
		last = row
	}
	if closes != 1 || last.Event != "close" {
		t.Fatalf("expected exactly one final close row: closes=%d final=%q", closes, last.Event)
	}
	if _, ok := last.Totals.PhaseNS["implication"]; !ok {
		t.Fatal("close record omitted exclusive_phase_ns.implication")
	}
	return last
}

func implicationTimingWant(t *testing.T, row implicationTimingRecord, starts, finishes uint64, phase string) {
	t.Helper()
	if row.Totals.Started != starts || row.Totals.Finished != finishes || row.Phase != phase {
		t.Fatalf("observation: starts=%d finishes=%d phase=%q; want %d/%d/%q", row.Totals.Started, row.Totals.Finished, row.Phase, starts, finishes, phase)
	}
}

func implicationTimingCoupling() func() {
	finish := nativetiming.BeginLoops(0, 0, 0, false)
	nativetiming.Coupling(0, 0, 0)
	return finish
}

func implicationTimingCloneBudget(b *nodeBudget) *nodeBudget {
	if b == nil {
		return nil
	}
	copy := *b
	if b.decided != nil {
		copy.decided = make(map[decisionKey]decisionResult, len(b.decided))
		for key, result := range b.decided {
			copy.decided[key] = result
		}
	}
	return &copy
}

func implicationTimingNoWidth(t *testing.T) func(string) int {
	t.Helper()
	return func(name string) int {
		t.Fatalf("fast path unexpectedly requested width of %q", name)
		return 1
	}
}

type implicationTimingFixture struct {
	name       string
	p, a, b    *term
	initial    *nodeBudget
	want       decisionResult
	wantBudget *nodeBudget
}

func implicationTimingFixtures(session *verificationSession) []implicationTimingFixture {
	p, x, y := constTerm(1, 1), paramTerm("x", 1), paramTerm("y", 1)
	owner := func(remaining, calls int) *nodeBudget {
		return &nodeBudget{session: session, remaining: remaining, calls: calls, loop: true}
	}
	fixture := func(name string, a, b *term, initial *nodeBudget, want decisionResult, remaining, calls int, memo bool) implicationTimingFixture {
		expected := implicationTimingCloneBudget(initial)
		if expected != nil {
			expected.remaining, expected.calls = remaining, calls
			if memo {
				expected.decided = map[decisionKey]decisionResult{{p, a, b, 0}: want}
			}
		}
		return implicationTimingFixture{name, p, a, b, initial, want, expected}
	}
	trueResult, falseResult, unknown := decisionResult{true, true}, decisionResult{false, true}, decisionResult{false, false}
	fixtures := []implicationTimingFixture{
		fixture("equal_pointer", x, x, owner(0, 17), trueResult, 0, 17, false),
		fixture("equal_structural", paramTerm("x", 1), paramTerm("x", 1), owner(-7, implicationCallLimit+1), trueResult, -7, implicationCallLimit+1, false),
		fixture("nil_equal", x, x, nil, trueResult, 0, 0, false),
		fixture("exhausted_zero", x, y, owner(0, 17), unknown, 0, 18, false),
		fixture("exhausted_negative", x, y, owner(-7, 17), unknown, -7, 18, false),
		fixture("call_limit", x, y, owner(3, implicationCallLimit), unknown, 3, implicationCallLimit+1, false),
	}
	for _, named := range []struct {
		name string
		want decisionResult
	}{{"memo_true", trueResult}, {"memo_false", falseResult}, {"memo_unknown", unknown}} {
		budget := owner(-7, implicationCallLimit+1)
		budget.decided = map[decisionKey]decisionResult{{p, x, y, 0}: named.want}
		fixtures = append(fixtures, fixture(named.name, x, y, budget, named.want, -7, implicationCallLimit+1, false))
	}
	for remaining := 1; remaining <= 3; remaining++ {
		fixtures = append(fixtures, fixture("node_balance_"+strconv.Itoa(remaining), x, y, owner(remaining, 17), unknown, remaining-3, 18, false))
	}
	// This sole non-tiny fixture is necessarily over the real admission limit:
	// 65,536 distinct leaves, one shallow application, premise, and right side.
	// Admission stops at 65,537 visited nodes; no evaluator or BDD sees it.
	args := make([]*term, implicationNodeLimit)
	for i := range args {
		args[i] = constTerm(uint64(i), 32)
	}
	oversized := &term{kind: termApply, width: 32, name: "implication_timing_oversized", args: args}
	fixtures = append(fixtures, fixture("node_limit", oversized, constTerm(0, 32), owner(1, 17), unknown, 1-blastNodeBudget, 18, false))
	// A raw full-width mask becomes x during canonicalization, after its
	// four-node admission debit. The mask is a fresh node, distinct from p.
	// Using binaryTerm here would fold the fixture before admission.
	canonicalLeft := &term{kind: termBinary, width: 1, op: "and", left: x, right: constTerm(1, 1)}
	fixtures = append(fixtures,
		fixture("canonical_true", canonicalLeft, x, owner(64, 17), trueResult, 60, 18, true),
		fixture("nil_canonical_true", canonicalLeft, x, nil, trueResult, 0, 0, false),
		fixture("valuation_false", constTerm(0, 1), constTerm(1, 1), owner(64, 17), falseResult, 61, 18, true),
		fixture("nil_valuation_false", constTerm(0, 1), constTerm(1, 1), nil, falseResult, 0, 0, false),
	)
	return fixtures
}

func TestImplicationTimingWrapperParity(t *testing.T) {
	for _, optionCase := range []struct {
		name  string
		value VerificationOptions
	}{
		{"default_options", VerificationOptions{}},
		{"explicit_options", NewVerificationOptions("bounded,onesided,components,selfprune", "base", "implication_timing_control")},
	} {
		t.Run(optionCase.name, func(t *testing.T) {
			session := &verificationSession{options: optionCase.value}
			for _, fixture := range implicationTimingFixtures(session) {
				t.Run(fixture.name, func(t *testing.T) {
					var baseline *nodeBudget
					var baselineResult decisionResult
					for _, mode := range []struct {
						name            string
						within, enabled bool
					}{
						{"direct_depth", false, false},
						{"within_disabled", true, false},
						{"depth_enabled", false, true},
						{"within_enabled", true, true},
					} {
						t.Run(mode.name, func(t *testing.T) {
							if nativetiming.Enabled() {
								t.Fatal("observation unexpectedly active before control")
							}
							var observation *implicationTimingObservation
							if mode.enabled {
								observation = implicationTimingStart(t)
								defer implicationTimingCoupling()()
							}
							budget := implicationTimingCloneBudget(fixture.initial)
							var holds, decided bool
							if mode.within {
								holds, decided = session.impliesEqualWithin(fixture.p, fixture.a, fixture.b, implicationTimingNoWidth(t), budget)
							} else {
								holds, decided = session.impliesEqualDepth(fixture.p, fixture.a, fixture.b, implicationTimingNoWidth(t), budget, 0)
							}
							got := decisionResult{holds, decided}
							if got != fixture.want || !reflect.DeepEqual(budget, fixture.wantBudget) || session.options != optionCase.value {
								t.Fatalf("exact semantics changed: result=%v want=%v budget=%+v want=%+v options=%+v", got, fixture.want, budget, fixture.wantBudget, session.options)
							}
							if budget != nil && budget.session != session {
								t.Fatal("wrapper changed the budget's session identity")
							}
							if mode.name == "direct_depth" {
								baseline, baselineResult = implicationTimingCloneBudget(budget), got
							} else if got != baselineResult || !reflect.DeepEqual(budget, baseline) {
								t.Fatal("wrapper/observer differed from the unchanged direct-Depth baseline")
							}
							if mode.enabled {
								want := uint64(0)
								if mode.within {
									want = 1
								}
								implicationTimingWant(t, observation.closeRecord(t), want, want, "coupling")
							}
							// A nil caller budget has no externally reachable owner to
							// inspect. Its result/options/width behavior is checked here;
							// no claim is made about directly observing its private ledger.
						})
					}
				})
			}
		})
	}
}

func TestImplicationTimingFiniteHelperSequentialScopes(t *testing.T) {
	observation := implicationTimingStart(t)
	defer implicationTimingCoupling()()
	session := &verificationSession{}
	p, bit := constTerm(1, 1), paramTerm("bit", 1)
	budget := &nodeBudget{session: session, remaining: -7, calls: implicationCallLimit + 1, loop: true}
	before := implicationTimingCloneBudget(budget)
	values, ok := finiteConditionalValues(bit, 8)
	if !ok || !reflect.DeepEqual(values, []uint64{0, 1}) {
		t.Fatalf("fixture lost its exact two-value range: %v/%v", values, ok)
	}
	holds, decided, applicable := session.impliesFiniteConditionalEqual(p, bit, bit, implicationTimingNoWidth(t), budget)
	if !holds || !decided || !applicable || !reflect.DeepEqual(budget, before) {
		t.Fatal("sequential finite helper changed equality's zero-debit behavior")
	}
	implicationTimingWant(t, observation.closeRecord(t), 2, 2, "coupling")
}

func implicationTimingRecursiveFixture(t *testing.T) (p, a, b *term) {
	t.Helper()
	x, y, z := paramTerm("x", 2), paramTerm("y", 2), paramTerm("z", 2)
	a = canonical(binaryTerm("mul", x, binaryTerm("add", y, z)))
	b = canonical(binaryTerm("add", binaryTerm("mul", x, y), binaryTerm("mul", x, z)))
	p = paramTerm("irrelevant", 1)
	nodes, exceeded := dagNodes(implicationNodeLimit, p, a, b)
	if exceeded || nodes != 9 || a.kind != termBinary || a.op != "mul" || b.kind != termBinary || b.op != "add" || hasLargeBranch(a) || hasLargeBranch(b) {
		t.Fatal("recursive fixture must have nine nodes, distinct operation shapes, and no large branch")
	}
	return p, a, b
}

func TestImplicationTimingDirectDepthRecursionCounts(t *testing.T) {
	for _, optimistic := range []bool{false, true} {
		t.Run("optimistic_"+strconv.FormatBool(optimistic), func(t *testing.T) {
			p, a, b := implicationTimingRecursiveFixture(t)
			session := &verificationSession{}
			var baseline *nodeBudget
			var baselineWidths []string
			for _, mode := range []string{"direct_depth", "within_disabled", "depth_enabled", "within_enabled"} {
				t.Run(mode, func(t *testing.T) {
					if nativetiming.Enabled() {
						t.Fatal("observation unexpectedly active")
					}
					var observation *implicationTimingObservation
					if mode == "depth_enabled" || mode == "within_enabled" {
						observation = implicationTimingStart(t)
						defer implicationTimingCoupling()()
					}
					budget := &nodeBudget{session: session, remaining: 18, calls: 17, optimistic: optimistic, loop: true}
					var widths []string
					widthOf := func(name string) int {
						widths = append(widths, name)
						if name == "irrelevant" {
							return 1
						}
						return 2
					}
					var holds, decided bool
					if mode == "within_disabled" || mode == "within_enabled" {
						holds, decided = session.impliesEqualWithin(p, a, b, widthOf, budget)
					} else {
						holds, decided = session.impliesEqualDepth(p, a, b, widthOf, budget, 0)
					}
					// Nine nodes for the outer entry, then nine for its bounded
					// direct-Depth child. That child exhausts before any BDD race.
					wantMemo := map[decisionKey]decisionResult{}
					if !optimistic {
						wantMemo[decisionKey{p, a, b, 0}] = decisionResult{false, false}
					}
					if holds || decided || budget.remaining != 0 || budget.calls != 19 || budget.session != session || !budget.loop || budget.optimistic != optimistic || !reflect.DeepEqual(budget.decided, wantMemo) || session.options != (VerificationOptions{}) {
						t.Fatalf("recursive exact debit/memo/options changed: result=%v/%v budget=%+v", holds, decided, budget)
					}
					// Width lookups arise from a map; compare the exact multiset,
					// not a map-iteration-dependent order.
					sort.Strings(widths)
					if !reflect.DeepEqual(widths, []string{"irrelevant", "x", "y", "z"}) {
						t.Fatalf("recursive fixture changed width lookups: %v", widths)
					}
					if mode == "direct_depth" {
						baseline, baselineWidths = implicationTimingCloneBudget(budget), append([]string(nil), widths...)
					} else if !reflect.DeepEqual(budget, baseline) || !reflect.DeepEqual(widths, baselineWidths) {
						t.Fatal("observer changed direct-Depth recursion semantics")
					}
					if observation != nil {
						want := uint64(0)
						if mode == "within_enabled" {
							want = 1
						}
						row := observation.closeRecord(t)
						implicationTimingWant(t, row, want, want, "coupling")
						if row.Totals.Valuation != 1 {
							t.Fatalf("fixture must include one nested valuation, got %d", row.Totals.Valuation)
						}
					}
				})
			}
		})
	}
}

func TestImplicationTimingReentrantWithinCallback(t *testing.T) {
	observation := implicationTimingStart(t)
	defer implicationTimingCoupling()()
	session := &verificationSession{}
	p, x, y := constTerm(1, 1), paramTerm("x", 1), paramTerm("y", 1)
	inner := &nodeBudget{session: session, remaining: -7, calls: implicationCallLimit + 1}
	innerBefore := implicationTimingCloneBudget(inner)
	outer := &nodeBudget{session: session, remaining: 64}
	entered := false
	widthOf := func(string) int {
		if !entered {
			entered = true
			holds, decided := session.impliesEqualWithin(p, x, x, implicationTimingNoWidth(t), inner)
			if !holds || !decided || !reflect.DeepEqual(inner, innerBefore) {
				t.Fatal("reentrant equality changed its exact fast path")
			}
		}
		return 1
	}
	holds, decided := session.impliesEqualWithin(p, x, y, widthOf, outer)
	if !entered || holds || !decided || outer.remaining != 61 || outer.calls != 1 || len(outer.decided) != 1 || outer.decided[decisionKey{p, x, y, 0}] != (decisionResult{false, true}) {
		t.Fatal("real outer wrapper did not return the expected tiny refutation")
	}
	row := observation.closeRecord(t)
	implicationTimingWant(t, row, 2, 2, "coupling")
	if row.Totals.Valuation != 1 {
		t.Fatal("outer implication must retain its nested valuation")
	}
}

func TestImplicationTimingPanicUnwindsRealWrapper(t *testing.T) {
	for _, mode := range []string{"direct_depth", "within_disabled", "within_enabled"} {
		t.Run(mode, func(t *testing.T) {
			if nativetiming.Enabled() {
				t.Fatal("observation unexpectedly active")
			}
			var observation *implicationTimingObservation
			if mode == "within_enabled" {
				observation = implicationTimingStart(t)
				defer implicationTimingCoupling()()
			}
			session := &verificationSession{options: NewVerificationOptions("selfprune", "base", "panic_control")}
			options := session.options
			budget := &nodeBudget{session: session, remaining: 64}
			p, x, y := constTerm(1, 1), paramTerm("x", 1), paramTerm("y", 1)
			marker := new(struct{ sentinel byte })
			lookups := 0
			// Recovery is ONLY at this outer test boundary. The real wrapper
			// and production observer must propagate the identical panic.
			defer func() {
				if got := recover(); got != marker {
					t.Fatalf("real wrapper swallowed/replaced panic: got=%v want=%p", got, marker)
				}
				if lookups != 1 || budget.remaining != 61 || budget.calls != 1 || budget.decided != nil || budget.session != session || session.options != options {
					t.Fatal("panic changed the pre-lookup debit/memo/options or was not in the real callback")
				}
				if observation != nil {
					implicationTimingWant(t, observation.closeRecord(t), 1, 1, "coupling")
				}
			}()
			widthOf := func(string) int {
				lookups++
				panic(marker)
			}
			if mode == "direct_depth" {
				session.impliesEqualDepth(p, x, y, widthOf, budget, 0)
			} else {
				session.impliesEqualWithin(p, x, y, widthOf, budget)
			}
		})
	}
}

func TestImplicationTimingSyntheticRaceCancellationJoin(t *testing.T) {
	// This is explicitly a synthetic observed outer scope around the existing
	// production cancellation/join primitive. The actual implication wrapper has
	// no injected BDD callback. Do not describe this as real-wrapper cancellation
	// injection, and do not add production flags/hooks to make it one.
	for _, mode := range []string{"finish_after_join", "close_before_join"} {
		t.Run(mode, func(t *testing.T) {
			observation := implicationTimingStart(t)
			defer implicationTimingCoupling()()
			blasters := []*blaster{newBlaster(nil, nil), newBlaster(nil, nil)}
			for _, bl := range blasters {
				bl.bdd.budget = 1 // terminal-only stores; no BDD operations
			}
			capacity := 2 * bddOrderEstimate(1)
			admission := newBDDOrderAdmission(func() uint64 { return capacity })
			started, cancelled, release, abort := make(chan struct{}), make(chan struct{}), make(chan struct{}), make(chan struct{})
			returned := make(chan decisionResult, 1)
			done := make(chan struct{})
			var finished atomic.Int32
			var releaseOnce sync.Once
			releaseWorker := func() { releaseOnce.Do(func() { close(release) }) }
			defer func() {
				close(abort)
				releaseWorker()
				select {
				case <-done:
				case <-time.After(5 * time.Second):
					t.Error("controlled race did not join during test cleanup")
				}
			}()
			go func() {
				defer close(done)
				result, decided := func() (int, bool) {
					finish := nativetiming.BeginImplication()
					defer finish()
					return raceBDDOrdersAdmitted(blasters, func(bl *blaster) (int, bool) {
						defer finished.Add(1)
						if bl == blasters[0] {
							select {
							case <-started:
								return 7, false
							case <-abort:
								return 0, true
							}
						}
						close(started)
						for !bl.bdd.stop.Load() {
							select {
							case <-abort:
								return 0, true
							default:
								runtime.Gosched()
							}
						}
						close(cancelled)
						<-release
						return -1, false // production's interrupted check must reject it
					}, admission)
				}()
				returned <- decisionResult{result == 7, decided}
			}()
			select {
			case <-cancelled:
			case <-time.After(5 * time.Second):
				t.Fatal("winning order did not cancel the controlled loser")
			}
			if finished.Load() != 1 {
				t.Fatal("controlled losing worker did not remain inside its callback")
			}
			select {
			case <-returned:
				t.Fatal("race returned before its losing worker was released/joined")
			default:
			}
			if mode == "close_before_join" {
				implicationTimingWant(t, observation.closeRecord(t), 1, 0, "implication")
			}
			releaseWorker()
			select {
			case result := <-returned:
				if result != (decisionResult{true, true}) || finished.Load() != 2 {
					t.Fatalf("cancellation winner/join mismatch: result=%v finished=%d", result, finished.Load())
				}
			case <-time.After(5 * time.Second):
				t.Fatal("race did not return after explicit loser release")
			}
			for _, bl := range blasters {
				if bl.bdd.nodes != nil || bl.bdd.unique.entries != nil || bl.bdd.memo.entries != nil || bl.bdd.completedNodes != 1 {
					t.Fatal("race returned before terminal-only diagram stores were released")
				}
			}
			admission.mu.Lock()
			used := admission.used
			admission.mu.Unlock()
			if used != 0 {
				t.Fatalf("joined race retained %d admission bytes", used)
			}
			if mode == "finish_after_join" {
				implicationTimingWant(t, observation.closeRecord(t), 1, 1, "coupling")
			} else {
				// Repeated Close/reading cannot fabricate a finish after cutoff.
				implicationTimingWant(t, observation.closeRecord(t), 1, 0, "implication")
			}
		})
	}
}

var implicationTimingBenchmarkResult decisionResult

func BenchmarkImplicationTimingDisabledWrapper(b *testing.B) {
	for _, fixture := range []string{"equal", "memo_true", "memo_false", "memo_unknown"} {
		b.Run(fixture, func(b *testing.B) {
			for _, route := range []string{"direct_depth", "within"} {
				b.Run(route, func(b *testing.B) {
					b.StopTimer()
					if nativetiming.Enabled() {
						b.Fatal("disabled wrapper benchmark requires no active timing session")
					}
					p, x, y := constTerm(1, 1), paramTerm("x", 1), paramTerm("y", 1)
					session := &verificationSession{}
					budget := &nodeBudget{session: session, remaining: -7, calls: implicationCallLimit + 1}
					want := decisionResult{true, true}
					if fixture == "equal" {
						y = x
					} else {
						if fixture == "memo_false" {
							want = decisionResult{false, true}
						} else if fixture == "memo_unknown" {
							want = decisionResult{false, false}
						}
						budget.decided = map[decisionKey]decisionResult{{p, x, y, 0}: want}
					}
					before := implicationTimingCloneBudget(budget)
					widthOf := func(string) int { panic("benchmark fast path reached width lookup") }
					var holds, decided bool
					b.ReportAllocs()
					b.ResetTimer()
					b.StartTimer()
					if route == "direct_depth" {
						for i := 0; i < b.N; i++ {
							holds, decided = session.impliesEqualDepth(p, x, y, widthOf, budget, 0)
						}
					} else {
						for i := 0; i < b.N; i++ {
							holds, decided = session.impliesEqualWithin(p, x, y, widthOf, budget)
						}
					}
					b.StopTimer()
					implicationTimingBenchmarkResult = decisionResult{holds, decided}
					if implicationTimingBenchmarkResult != want || !reflect.DeepEqual(budget, before) || budget.session != session || session.options != (VerificationOptions{}) {
						b.Fatal("benchmark fast-path semantics changed")
					}
				})
			}
		})
	}
}
