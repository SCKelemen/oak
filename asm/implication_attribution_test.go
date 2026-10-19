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

// Source-only additive controls. No run is implied by this file's existence.
// All tests are serial because observation has one process-current session.
// Existing implication_timing_test.go and its original six roots stay intact.
// These controls reuse its immutable tiny fixtures and exact ledger assertions.
// The implementation/source inventory separately binds eleven production routes;
// synthetic controls and callback seams do not execute a whole producer.

type implicationAttributionVector [6]uint64

type implicationAttributionDetail struct {
	ProcessNS implicationAttributionVector `json:"process_ns"`
	Entries implicationAttributionVector `json:"process_stage_entries"`
	ProcessComplete bool `json:"process_detail_complete"`
	Limited bool `json:"limited"`
	ContextLost bool `json:"context_lost"`
	Saturated bool `json:"counter_saturated"`
	Candidate *struct {
		Started uint64 `json:"started"`
		Finished uint64 `json:"finished"`
		Complete bool `json:"detail_complete"`
		Dominant *struct {
			Class nativetiming.ObligationClass `json:"class"`
			Started uint64 `json:"started"`
			Finished uint64 `json:"finished"`
		} `json:"dominant"`
	} `json:"candidate"`
	Active *struct {
		ID uint64 `json:"id"`
		Class nativetiming.ObligationClass `json:"class"`
		Stage uint8 `json:"stage"`
		Complete bool `json:"detail_complete"`
	} `json:"active"`
}

type implicationAttributionRecord struct {
	implicationTimingRecord
	Detail *implicationAttributionDetail `json:"implication_detail"`
	OutputLimited bool `json:"output_limited"`
}

func implicationAttributionClose(t testing.TB, observation *implicationTimingObservation) implicationAttributionRecord {
	t.Helper()
	if err := observation.session.Close(); err != nil { t.Fatal(err) }
	decoder := json.NewDecoder(bytes.NewReader(observation.output.Bytes()))
	var last implicationAttributionRecord
	closes := 0
	for {
		var row implicationAttributionRecord
		if err := decoder.Decode(&row); err == io.EOF { break } else if err != nil { t.Fatal(err) }
		if row.Event == "close" { closes++ }
		last = row
	}
	if closes != 1 || last.Event != "close" || last.OutputLimited {
		t.Fatalf("missing/bounded close detail: closes=%d final=%q limited=%v detail=%+v", closes, last.Event, last.OutputLimited, last.Detail)
	}
	if last.Detail == nil {
		if last.Totals.Started != 0 || last.Totals.Finished != 0 || last.Totals.PhaseNS["implication"] != 0 {
			t.Fatal("nonempty wrapper observation omitted detail")
		}
		// No wrapper was entered on the direct-Depth control. Normalize the
		// absent optional object for zero-counter assertions only.
		last.Detail = new(implicationAttributionDetail)
	}
	var sum uint64
	for _, ns := range last.Detail.ProcessNS { sum += ns }
	if sum != last.Totals.PhaseNS["implication"] || last.Detail.Saturated {
		t.Fatal("six stages must exactly partition existing implication time without saturation")
	}
	return last
}

func implicationAttributionWantActive(t *testing.T, row implicationAttributionRecord, class nativetiming.ObligationClass) {
	t.Helper()
	if row.Detail.Active == nil || row.Detail.Active.Class != class || row.Detail.Active.ID == 0 {
		t.Fatalf("active wrapper has wrong owner/class: %+v; want %d", row.Detail.Active, class)
	}
}

func implicationAttributionWantEntries(t *testing.T, row implicationAttributionRecord, stage uint8, nonzero bool) {
	t.Helper()
	if (row.Detail.Entries[stage] != 0) != nonzero {
		t.Fatalf("stage %d entry count=%d, want nonzero=%v", stage, row.Detail.Entries[stage], nonzero)
	}
}

func TestImplicationAttributionWrapperParity(t *testing.T) {
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
								holds, decided = session.impliesEqualWithinClass(nativetiming.ObligationLoopInvariant, fixture.p, fixture.a, fixture.b, implicationTimingNoWidth(t), budget)
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
								row := implicationAttributionClose(t, observation)
								implicationTimingWant(t, row.implicationTimingRecord, want, want, "coupling")
								wantDAG := mode.within && (fixture.name == "node_limit" || fixture.name == "canonical_true" || fixture.name == "nil_canonical_true" || fixture.name == "valuation_false" || fixture.name == "nil_valuation_false" || fixture.name == "node_balance_1" || fixture.name == "node_balance_2" || fixture.name == "node_balance_3")
								wantCanonical := mode.within && (fixture.name == "canonical_true" || fixture.name == "nil_canonical_true" || fixture.name == "valuation_false" || fixture.name == "nil_valuation_false")
								implicationAttributionWantEntries(t, row, uint8(nativetiming.StageDAGAdmission), wantDAG)
								implicationAttributionWantEntries(t, row, uint8(nativetiming.StageCanonicalPass), wantCanonical)
								if !mode.within && row.Detail.Entries != (implicationAttributionVector{}) { t.Fatal("direct Depth acquired wrapper detail") }
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

func TestImplicationAttributionRecursiveScheduling(t *testing.T) {
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
						holds, decided = session.impliesEqualWithinClass(nativetiming.ObligationCouplingPreservation, p, a, b, widthOf, budget)
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
						row := implicationAttributionClose(t, observation)
						implicationTimingWant(t, row.implicationTimingRecord, want, want, "coupling")
						if mode == "within_enabled" {
							if row.Detail.Entries[nativetiming.StageDAGAdmission] != 2 || row.Detail.Entries[nativetiming.StageRecursiveScheduling] == 0 || row.Detail.Entries[nativetiming.StageBDDJoined] != 0 { t.Fatal("bounded child stage route changed") }
						} else if row.Detail.Entries != (implicationAttributionVector{}) { t.Fatal("direct recursion inherited detail") }
						if row.Totals.Valuation != 1 {
							t.Fatalf("fixture must include one nested valuation, got %d", row.Totals.Valuation)
						}
					}
				})
			}
		})
	}
}

func TestImplicationAttributionClassifications(t *testing.T) {
	classes := []struct {
		name string
		class nativetiming.ObligationClass
	}{
		{"unspecified", nativetiming.ObligationUnspecified},
		{"loop_invariant", nativetiming.ObligationLoopInvariant},
		{"coupling_header", nativetiming.ObligationCouplingHeader},
		{"coupling_preservation", nativetiming.ObligationCouplingPreservation},
		{"loop_continue", nativetiming.ObligationLoopContinue},
		{"loop_reach", nativetiming.ObligationLoopReach},
		{"trap_domain", nativetiming.ObligationTrapDomain},
		{"loop_entry_memory", nativetiming.ObligationLoopEntryMemory},
		{"loop_iteration_effect", nativetiming.ObligationLoopIterationEffect},
		{"loop_result", nativetiming.ObligationLoopResult},
		{"loop_exit_effect", nativetiming.ObligationLoopExitEffect},
		{"straight_write", nativetiming.ObligationStraightWrite},
	}
	for ordinal, tc := range classes {
		t.Run(tc.name, func(t *testing.T) {
			if int(tc.class) != ordinal { t.Fatal("frozen class enum order changed") }
			observation := implicationTimingStart(t)
			defer implicationTimingCoupling()()
			session := &verificationSession{}
			p, a, b := constTerm(1, 1), paramTerm("x", 1), paramTerm("y", 1)
			budget := &nodeBudget{session: session, remaining: 64}
			var row implicationAttributionRecord
			var widths []string
			widthOf := func(name string) int {
				widths = append(widths, name)
				if len(widths) == 1 { row = implicationAttributionClose(t, observation) }
				return 1
			}
			holds, decided := session.impliesEqualWithinClass(tc.class, p, a, b, widthOf, budget)
			sort.Strings(widths)
			if holds || !decided || budget.remaining != 61 || budget.calls != 1 || budget.session != session || !reflect.DeepEqual(widths, []string{"x", "y"}) || !reflect.DeepEqual(budget.decided, map[decisionKey]decisionResult{{p, a, b, 0}: {false, true}}) { t.Fatal("classified real-wrapper refutation changed") }
			implicationTimingWant(t, row.implicationTimingRecord, 1, 0, "implication")
			implicationAttributionWantActive(t, row, tc.class)
			if row.Detail.Active.Stage != uint8(nativetiming.StageOther) { t.Fatal("width callback escaped other stage") }
		})
	}
	// Exercise the actual shared callback seams, with a class captured by the
	// same closure shape as the production route. The caller inventory binds
	// these classes to entry/iteration/exit/straight-line semantic callsites.
	// These tiny seams do not claim to run each top-level loop producer.
	for _, tc := range []struct {
		name string
		class nativetiming.ObligationClass
		writeLog bool
	}{
		{"entry_callback", nativetiming.ObligationLoopEntryMemory, false},
		{"iteration_callback", nativetiming.ObligationLoopIterationEffect, false},
		{"exit_callback", nativetiming.ObligationLoopExitEffect, true},
		{"straight_callback", nativetiming.ObligationStraightWrite, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			observation := implicationTimingStart(t)
			defer implicationTimingCoupling()()
			session := &verificationSession{}
			p, x, y := constTerm(1, 1), paramTerm("x", 1), paramTerm("y", 1)
			budget := &nodeBudget{session: session, remaining: 64}
			var row implicationAttributionRecord
			var last decisionKey
			lookups, callbacks := 0, 0
			widthOf := func(string) int {
				lookups++
				if lookups == 1 { row = implicationAttributionClose(t, observation) }
				return 1
			}
			implies := func(p, a, b *term) (bool, bool) {
				callbacks++
				last = decisionKey{p, a, b, 0}
				return session.impliesEqualWithinClass(tc.class, p, a, b, widthOf, budget)
			}
			if tc.writeLog {
				at := paramTerm("index", 32)
				if writeLogsEqualUnder([]*spanWrite{{index: at, value: x}}, []*spanWrite{{index: at, value: y}}, p, implies) { t.Fatal("unequal write value was accepted") }
				if callbacks != 3 { t.Fatal("write seam must retain guard, index and value wrappers") }
			} else {
				if holds, decided := spanEqualSplitting(p, "memory", 1, x, y, nil, implies); holds || !decided { t.Fatal("span callback refutation changed") }
				if callbacks != 1 { t.Fatal("unsplit span seam changed wrapper count") }
			}
			if lookups != 2 || budget.remaining != 61 || budget.calls != 1 || budget.session != session || !reflect.DeepEqual(budget.decided, map[decisionKey]decisionResult{last: {false, true}}) { t.Fatal("callback changed exact budget/memo/width behavior") }
			implicationTimingWant(t, row.implicationTimingRecord, uint64(callbacks), uint64(callbacks-1), "implication")
			implicationAttributionWantActive(t, row, tc.class)
		})
	}
}

func TestImplicationAttributionAdmissionCanonical(t *testing.T) {
	session := &verificationSession{}
	fixtures := implicationTimingFixtures(session)
	for _, name := range []string{"canonical_true", "node_limit"} {
		t.Run(name, func(t *testing.T) {
			var fixture implicationTimingFixture
			for _, f := range fixtures { if f.name == name { fixture = f; break } }
			if fixture.name == "" { t.Fatal("required existing fixture is missing") }
			observation := implicationTimingStart(t)
			defer implicationTimingCoupling()()
			budget := implicationTimingCloneBudget(fixture.initial)
			holds, decided := session.impliesEqualWithinClass(nativetiming.ObligationLoopContinue, fixture.p, fixture.a, fixture.b, implicationTimingNoWidth(t), budget)
			if (decisionResult{holds, decided}) != fixture.want || !reflect.DeepEqual(budget, fixture.wantBudget) { t.Fatal("admission/canonical exact allowance changed") }
			row := implicationAttributionClose(t, observation)
			implicationTimingWant(t, row.implicationTimingRecord, 1, 1, "coupling")
			if row.Detail.Entries[nativetiming.StageDAGAdmission] != 1 { t.Fatal("DAG admission must be bracketed exactly once") }
			implicationAttributionWantEntries(t, row, uint8(nativetiming.StageCanonicalPass), name == "canonical_true")
			if row.Detail.Entries[nativetiming.StageBDDJoined] != 0 || row.Detail.Entries[nativetiming.StageStandalonePruning] != 0 { t.Fatal("fast route reached a diagram stage") }
		})
	}
}

func TestImplicationAttributionHelperOwnership(t *testing.T) {
	t.Run("finite_classified", implicationAttributionFiniteClassified)
	t.Run("finite_compatibility", implicationAttributionFiniteCompatibility)
	t.Run("reentrant", implicationAttributionReentrant)
	t.Run("panic", implicationAttributionPanic)
}

func implicationAttributionFiniteClassified(t *testing.T) {
	observation := implicationTimingStart(t)
	defer nativetiming.BeginSearch("finite")(0, 0, 0, false)
	defer nativetiming.BeginValidation("finite")(0, false)
	defer implicationTimingCoupling()()
	session := &verificationSession{}
	p, bit := constTerm(1, 1), paramTerm("bit", 1)
	budget := &nodeBudget{session: session, remaining: -7, calls: implicationCallLimit + 1, loop: true}
	before := implicationTimingCloneBudget(budget)
	values, ok := finiteConditionalValues(bit, 8)
	if !ok || !reflect.DeepEqual(values, []uint64{0, 1}) { t.Fatal("finite fixture lost exactly two values") }
	holds, decided, applicable := session.impliesFiniteConditionalEqualClass(nativetiming.ObligationLoopResult, p, bit, bit, implicationTimingNoWidth(t), budget)
	if !holds || !decided || !applicable || !reflect.DeepEqual(budget, before) { t.Fatal("classified finite helper changed zero debit") }
	row := implicationAttributionClose(t, observation)
	implicationTimingWant(t, row.implicationTimingRecord, 2, 2, "coupling")
	if row.Detail.Candidate == nil || row.Detail.Candidate.Dominant == nil || row.Detail.Candidate.Dominant.Class != nativetiming.ObligationLoopResult || row.Detail.Candidate.Dominant.Started != 2 || row.Detail.Candidate.Dominant.Finished != 2 { t.Fatal("two finite wrappers did not inherit loop-result class") }
}
func implicationAttributionFiniteCompatibility(t *testing.T) {
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
	row := implicationAttributionClose(t, observation)
	implicationTimingWant(t, row.implicationTimingRecord, 2, 2, "coupling")
	if row.Detail.ProcessComplete { t.Fatal("unspecified compatibility must remain detectable") }
}

func implicationAttributionReentrant(t *testing.T) {
	observation := implicationTimingStart(t)
	defer implicationTimingCoupling()()
	session := &verificationSession{}
	p, x, y := constTerm(1, 1), paramTerm("x", 1), paramTerm("y", 1)
	inner := &nodeBudget{session: session, remaining: -7, calls: implicationCallLimit + 1}
	innerBefore := implicationTimingCloneBudget(inner)
	outer := &nodeBudget{session: session, remaining: 64}
	entered := false
	var frozen implicationAttributionRecord
	widthOf := func(string) int {
		if !entered {
			entered = true
			holds, decided := session.impliesEqualWithinClass(nativetiming.ObligationTrapDomain, p, x, x, implicationTimingNoWidth(t), inner)
			if !holds || !decided || !reflect.DeepEqual(inner, innerBefore) {
				t.Fatal("reentrant equality changed its exact fast path")
			}
			// Closing immediately after the inner wrapper returns observes
			// the restored outer class/stage before it can finish. Its
			// later valuation remains outside this frozen cutoff.
			frozen = implicationAttributionClose(t, observation)
		}
		return 1
	}
	holds, decided := session.impliesEqualWithinClass(nativetiming.ObligationLoopReach, p, x, y, widthOf, outer)
	if !entered || holds || !decided || outer.remaining != 61 || outer.calls != 1 || len(outer.decided) != 1 || outer.decided[decisionKey{p, x, y, 0}] != (decisionResult{false, true}) {
		t.Fatal("real outer wrapper did not return the expected tiny refutation")
	}
	implicationTimingWant(t, frozen.implicationTimingRecord, 2, 1, "implication")
	implicationAttributionWantActive(t, frozen, nativetiming.ObligationLoopReach)
	if frozen.Detail.Active.Stage != uint8(nativetiming.StageOther) || frozen.Detail.Active.Complete || frozen.Detail.ProcessComplete {
		t.Fatal("reentrant return did not restore the outer owner at an explicitly incomplete cutoff")
	}
	if frozen.Totals.Valuation != 0 || !reflect.DeepEqual(frozen, implicationAttributionClose(t, observation)) {
		t.Fatal("late outer work changed the frozen observation")
	}
}

func implicationAttributionPanic(t *testing.T) {
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
					row := implicationAttributionClose(t, observation)
					implicationTimingWant(t, row.implicationTimingRecord, 1, 1, "coupling")
					if row.Detail.Active != nil { t.Fatal("panic unwind retained active detail") }
				}
			}()
			widthOf := func(string) int {
				lookups++
				panic(marker)
			}
			if mode == "direct_depth" {
				session.impliesEqualDepth(p, x, y, widthOf, budget, 0)
			} else {
				session.impliesEqualWithinClass(nativetiming.ObligationStraightWrite, p, x, y, widthOf, budget)
			}
		})
	}
}

func TestImplicationAttributionSyntheticJoinedRace(t *testing.T) {
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
					owner, finish := nativetiming.BeginClassifiedImplication(nativetiming.ObligationCouplingPreservation)
					defer finish()
					stage := owner.Push(nativetiming.StageBDDJoined)
					defer stage.End()
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
				row := implicationAttributionClose(t, observation)
				implicationTimingWant(t, row.implicationTimingRecord, 1, 0, "implication")
				implicationAttributionWantActive(t, row, nativetiming.ObligationCouplingPreservation)
				if row.Detail.Active.Stage != uint8(nativetiming.StageBDDJoined) || row.Detail.Entries[nativetiming.StageBDDJoined] != 1 { t.Fatal("joined stage ended before losing worker cleanup/join") }
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
				row := implicationAttributionClose(t, observation)
				implicationTimingWant(t, row.implicationTimingRecord, 1, 1, "coupling")
				if row.Detail.Active != nil || row.Detail.Entries[nativetiming.StageBDDJoined] != 1 { t.Fatal("joined stage did not finish exactly once after worker join") }
			} else {
				// Repeated Close/reading cannot fabricate a finish after cutoff.
				row := implicationAttributionClose(t, observation)
				implicationTimingWant(t, row.implicationTimingRecord, 1, 0, "implication")
				implicationAttributionWantActive(t, row, nativetiming.ObligationCouplingPreservation)
				if row.Detail.Active.Stage != uint8(nativetiming.StageBDDJoined) || row.Detail.Entries[nativetiming.StageBDDJoined] != 1 { t.Fatal("joined stage ended before losing worker cleanup/join") }
			}
		})
	}
}

func TestImplicationAttributionActualDiagramRoutes(t *testing.T) {
	for _, route := range []string{"bdd_terminal", "bdd_one_bit_refutation", "standalone_prune"} {
		t.Run(route, func(t *testing.T) {
			session := &verificationSession{}
			p, a, b := constTerm(0, 1), constTerm(0, 8), constTerm(1, 8)
			initial, wantNodes, wantCalls := 4, 3, 1
			want := decisionResult{true, true}
			if route == "bdd_one_bit_refutation" {
				p = constTerm(1, 1)
				a = selectTerm("postexhaustion", constTerm(0, 32), 1)
				b = constTerm(elementValue("postexhaustion", 0, 1), 1)
				initial, wantNodes, want = 5, 3, decisionResult{false, true}
			}
			if route == "standalone_prune" {
				p, a, b = postExhaustionSplitFixture(t)
				initial, wantNodes, wantCalls = 50, 26, 2
			}
			nodes, exceeded := dagNodes(implicationNodeLimit, p, a, b)
			if exceeded || nodes != wantNodes { t.Fatalf("frozen tiny DAG changed: %d, want %d", nodes, wantNodes) }
			var baseline *nodeBudget
			var baselineWidths []string
			for _, enabled := range []bool{false, true} {
				t.Run("enabled_"+strconv.FormatBool(enabled), func(t *testing.T) {
					var observation *implicationTimingObservation
					if enabled {
						observation = implicationTimingStart(t)
						defer implicationTimingCoupling()()
					}
					budget := &nodeBudget{session: session, remaining: initial, loop: true}
					var widths []string
					widthOf := func(name string) int {
						widths = append(widths, name)
						if route != "standalone_prune" || name == "branch" || name == "irrelevant1" || name == "irrelevant2" { return 1 }
						return 8
					}
					holds, decided := session.impliesEqualWithinClass(nativetiming.ObligationLoopExitEffect, p, a, b, widthOf, budget)
					sort.Strings(widths)
					if (decisionResult{holds, decided}) != want || budget.remaining != 0 || budget.calls != wantCalls || budget.session != session || !budget.loop || budget.optimistic || session.options != (VerificationOptions{}) || !reflect.DeepEqual(budget.decided, map[decisionKey]decisionResult{{p, a, b, 0}: want}) { t.Fatalf("tiny real diagram route changed exact verdict/allowance/memo: %+v result=%v/%v", budget, holds, decided) }
					if !enabled { baseline, baselineWidths = implicationTimingCloneBudget(budget), append([]string(nil), widths...) } else {
						if !reflect.DeepEqual(budget, baseline) || !reflect.DeepEqual(widths, baselineWidths) { t.Fatal("observation changed tiny real diagram behavior") }
						row := implicationAttributionClose(t, observation)
						implicationTimingWant(t, row.implicationTimingRecord, 1, 1, "coupling")
						implicationAttributionWantEntries(t, row, uint8(nativetiming.StageBDDJoined), route != "standalone_prune")
						implicationAttributionWantEntries(t, row, uint8(nativetiming.StageStandalonePruning), route == "standalone_prune")
					}
				})
			}
		})
	}
}

func TestImplicationAttributionNilDirectBypass(t *testing.T) {
	for _, route := range []string{"depth", "split", "child_restore"} {
		t.Run(route, func(t *testing.T) {
			observation := implicationTimingStart(t)
			defer implicationTimingCoupling()()
			owner, finish := nativetiming.BeginClassifiedImplication(nativetiming.ObligationLoopInvariant)
			defer finish()
			stage := owner.Push(nativetiming.StageRecursiveScheduling)
			defer stage.End()
			session := &verificationSession{}
			if route == "split" {
				p, a, b := postExhaustionSplitFixture(t)
				budget := &nodeBudget{session: session, remaining: 0, calls: 17}
				before := implicationTimingCloneBudget(budget)
				if holds, decided := session.splitDecide(p, a, b, implicationTimingNoWidth(t), budget, splitDepth-1); !holds || !decided || !reflect.DeepEqual(budget, before) { t.Fatal("nil-observer split lost post-exhaustion equality") }
			} else {
				p, a, b := implicationTimingRecursiveFixture(t)
				budget := &nodeBudget{session: session, remaining: 18, calls: 17, loop: true}
				widthOf := func(name string) int { if name == "irrelevant" { return 1 }; return 2 }
				var holds, decided bool
				if route == "depth" { holds, decided = session.impliesEqualDepth(p, a, b, widthOf, budget, 0) } else { holds, decided = session.impliesEqualDepthObserved(p, a, b, widthOf, budget, 0, owner) }
				if holds || decided || budget.remaining != 0 || budget.calls != 19 || !reflect.DeepEqual(budget.decided, map[decisionKey]decisionResult{{p, a, b, 0}: {false, false}}) { t.Fatal("bounded recursion debit/memo changed") }
			}
			row := implicationAttributionClose(t, observation)
			implicationTimingWant(t, row.implicationTimingRecord, 1, 0, "implication")
			implicationAttributionWantActive(t, row, nativetiming.ObligationLoopInvariant)
			if row.Detail.Active.Stage != uint8(nativetiming.StageRecursiveScheduling) { t.Fatal("direct child failed to retain/restore existing owner stage") }
			if route == "child_restore" {
				if row.Detail.Entries[nativetiming.StageDAGAdmission] != 2 || row.Detail.Entries[nativetiming.StageRecursiveScheduling] < 2 { t.Fatal("observed child did not nest and restore the synthetic scheduling owner") }
			} else {
				if row.Detail.Entries[nativetiming.StageRecursiveScheduling] != 1 || row.Detail.Entries[nativetiming.StageDAGAdmission] != 0 || row.Detail.Entries[nativetiming.StageCanonicalPass] != 0 || row.Detail.Entries[nativetiming.StageBDDJoined] != 0 || row.Detail.Entries[nativetiming.StageStandalonePruning] != 0 { t.Fatal("nil direct adapter attributed work to an unrelated owner") }
			}
		})
	}
}
