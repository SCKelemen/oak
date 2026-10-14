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
	"unsafe"
)

func attributionHarness(t *testing.T) *harness {
	t.Helper()
	h := newHarness(t, maxRecords, maxBytes)
	BeginSearch("attribution")
	BeginValidation("candidate")
	return h
}

func attributionSnapshot(t *testing.T, h *harness) *implicationDetailRecord {
	t.Helper()
	r := h.s.snapshot("test")
	d := r.ImplicationDetail
	if d == nil {
		t.Fatal("missing implication detail")
	}
	var total uint64
	for _, ns := range d.ProcessNS {
		total += ns
	}
	if !d.CounterSaturated && total != r.Totals.PhaseNS.Implication {
		t.Fatalf("partition = %d, phase = %d: %+v", total, r.Totals.PhaseNS.Implication, d)
	}
	return d
}

func requireVector(t *testing.T, got, want stageVector) {
	t.Helper()
	if got != want {
		t.Fatalf("stage vector = %v, want %v", got, want)
	}
}

func TestImplicationAttributionSixStagePartition(t *testing.T) {
	h := attributionHarness(t)
	o, done := BeginClassifiedImplication(ObligationLoopInvariant)
	var want stageVector
	for stage := StageOther; stage < implicationStageCount; stage++ {
		token := o.Push(stage)
		ns := uint64(stage) + 1
		h.clock.advance(time.Duration(ns))
		want[stage] += ns
		d := attributionSnapshot(t, h)
		requireVector(t, d.ProcessNS, want)
		requireVector(t, d.Active.NS, want)
		requireVector(t, d.Candidate.NS, want)
		if d.Active.Stage != stage || d.Active.StageScopeAgeNS != ns {
			t.Fatalf("open stage = %+v", d.Active)
		}
		token.End()
	}
	done()
	d := attributionSnapshot(t, h)
	if d.Active != nil || d.Candidate.Started != 1 || d.Candidate.Finished != 1 || !d.ProcessDetailComplete || !d.Candidate.DetailComplete {
		t.Fatalf("completed wrapper = %+v", d)
	}
	requireVector(t, d.ProcessStageEntries, stageVector{1, 1, 1, 1, 1, 1})
}

func TestImplicationAttributionSnapshotsAndBackwardClock(t *testing.T) {
	h := attributionHarness(t)
	o, done := BeginClassifiedImplication(ObligationLoopContinue)
	token := o.Push(StageDAGAdmission)
	h.clock.advance(10)
	a, b := attributionSnapshot(t, h), attributionSnapshot(t, h)
	if !reflect.DeepEqual(a, b) || h.s.detail.processNS != (stageVector{}) {
		t.Fatal("snapshots accumulated or changed counters")
	}
	token.End()
	h.clock.advance(-5)
	requireVector(t, attributionSnapshot(t, h).ProcessNS, stageVector{0, 10})
	h.clock.advance(5)
	done()
	requireVector(t, attributionSnapshot(t, h).ProcessNS, stageVector{0, 10})
}

func TestImplicationAttributionRecursiveSchedulingRestores(t *testing.T) {
	h := attributionHarness(t)
	o, done := BeginClassifiedImplication(ObligationLoopReach)
	scheduling := o.Push(StageRecursiveScheduling)
	h.clock.advance(1)
	child := o.Push(StageOther)
	h.clock.advance(2)
	for _, step := range []struct { stage ImplicationStage; ns time.Duration }{
		{StageDAGAdmission, 3}, {StageCanonicalPass, 4}, {StageBDDJoined, 5},
	} {
		token := o.Push(step.stage)
		h.clock.advance(step.ns)
		token.End()
	}
	child.End()
	h.clock.advance(6)
	d := attributionSnapshot(t, h)
	requireVector(t, d.ProcessNS, stageVector{2, 3, 4, 7, 5})
	if d.Active.Stage != StageRecursiveScheduling || d.Active.StageScopeAgeNS != 21 {
		t.Fatalf("inclusive scheduling age or restoration = %+v", d.Active)
	}
	scheduling.End()
	done()
}

func TestImplicationAttributionValuationExcluded(t *testing.T) {
	h := attributionHarness(t)
	o, done := BeginClassifiedImplication(ObligationLoopResult)
	token := o.Push(StageCanonicalPass)
	h.clock.advance(2)
	valuationDone := BeginValuation(1, 1, 1, 1, 1)
	h.clock.advance(10)
	d := attributionSnapshot(t, h)
	requireVector(t, d.ProcessNS, stageVector{0, 0, 2})
	if d.Active == nil || d.Active.Stage != StageCanonicalPass {
		t.Fatal("valuation lost enclosing wrapper")
	}
	valuationDone(1)
	h.clock.advance(3)
	token.End()
	done()
	requireVector(t, attributionSnapshot(t, h).ProcessNS, stageVector{0, 0, 5})
	if h.s.snapshot("test").Totals.PhaseNS.Valuation != 10 {
		t.Fatal("valuation phase changed")
	}
}

func TestImplicationAttributionReentrantClasses(t *testing.T) {
	h := attributionHarness(t)
	a, aDone := BeginClassifiedImplication(ObligationLoopInvariant)
	outer := a.Push(StageRecursiveScheduling)
	h.clock.advance(2)
	outerID := attributionSnapshot(t, h).Active.ID
	b, bDone := BeginClassifiedImplication(ObligationTrapDomain)
	inner := b.Push(StageDAGAdmission)
	h.clock.advance(3)
	d := attributionSnapshot(t, h)
	if d.Active.ID == outerID || d.Active.Class != ObligationTrapDomain {
		t.Fatalf("nested owner = %+v", d.Active)
	}
	inner.End()
	bDone()
	h.clock.advance(4)
	d = attributionSnapshot(t, h)
	if d.Active.ID != outerID || d.Active.Class != ObligationLoopInvariant || d.Active.Stage != StageRecursiveScheduling {
		t.Fatalf("outer restoration = %+v", d.Active)
	}
	requireVector(t, d.Active.NS, stageVector{0, 0, 0, 6})
	requireVector(t, d.ProcessNS, stageVector{0, 3, 0, 6})
	outer.End()
	aDone()
}

func TestImplicationAttributionClassAggregationAndTie(t *testing.T) {
	h := attributionHarness(t)
	for i := 0; i < 3; i++ {
		o, done := BeginClassifiedImplication(ObligationLoopInvariant)
		token := o.Push(StageCanonicalPass)
		h.clock.advance(2)
		token.End()
		done()
	}
	o, done := BeginClassifiedImplication(ObligationLoopReach)
	token := o.Push(StageBDDJoined)
	h.clock.advance(6)
	token.End()
	done()
	d := attributionSnapshot(t, h)
	if d.Candidate.Started != 4 || d.Candidate.Finished != 4 || d.Candidate.Dominant.Class != ObligationLoopInvariant || d.Candidate.Dominant.Started != 3 || d.Candidate.Dominant.Finished != 3 {
		t.Fatalf("class aggregation or enum tie = %+v", d.Candidate)
	}
	requireVector(t, d.Candidate.Dominant.NS, stageVector{0, 0, 6})
}

func TestImplicationAttributionCandidateCompletenessAndStaleKey(t *testing.T) {
	h := attributionHarness(t)
	bad, badDone := BeginClassifiedImplication(ObligationLoopInvariant)
	bad.Push(ImplicationStage(255))
	h.clock.advance(3)
	badDone()
	good, goodDone := BeginClassifiedImplication(ObligationTrapDomain)
	token := good.Push(StageDAGAdmission)
	h.clock.advance(4)
	d := attributionSnapshot(t, h)
	if d.ProcessDetailComplete || d.Candidate.DetailComplete || !d.Active.DetailComplete {
		t.Fatalf("active completeness hid earlier failure: %+v", d)
	}
	token.End()
	goodDone()
	secondDone := BeginValidation("second")
	fresh, freshDone := BeginClassifiedImplication(ObligationLoopReach)
	stage := fresh.Push(StageCanonicalPass)
	h.clock.advance(5)
	d = attributionSnapshot(t, h)
	if d.ProcessDetailComplete || !d.Candidate.DetailComplete || d.Candidate.Key[1] != 2 {
		t.Fatalf("candidate reset = %+v", d)
	}
	requireVector(t, d.Candidate.NS, stageVector{0, 0, 5})
	thirdDone := BeginValidation("third")
	thirdDone(0, false) // Restore the older wrapper, never the new candidate key.
	h.clock.advance(7)
	d = attributionSnapshot(t, h)
	if !d.ContextLost || d.Candidate != nil || d.ProcessDetailComplete {
		t.Fatalf("stale context was emitted as current: %+v", d)
	}
	stage.End()
	freshDone()
	if h.s.detail.candidate.started != 0 || h.s.detail.candidate.finished != 0 || h.s.detail.candidate.ns != (stageVector{}) || h.s.detail.candidate.complete {
		t.Fatal("stale owner charged or certified new candidate")
	}
	secondDone(0, false)
}

func TestImplicationAttributionSearchAndSessionGeneration(t *testing.T) {
	h := attributionHarness(t)
	old, oldDone := BeginClassifiedImplication(ObligationLoopResult)
	oldStage := old.Push(StageCanonicalPass)
	h.clock.advance(2)
	BeginSearch("superseding")
	BeginValidation("fresh")
	fresh, freshDone := BeginClassifiedImplication(ObligationStraightWrite)
	freshStage := fresh.Push(StageBDDJoined)
	before := attributionSnapshot(t, h)
	old.Push(StageDAGAdmission).End()
	oldStage.End()
	oldDone()
	after := attributionSnapshot(t, h)
	if after.Active.ID != before.Active.ID || after.Active.Stage != StageBDDJoined || after.Candidate.Finished != before.Candidate.Finished {
		t.Fatal("superseded owner changed current owner or candidate")
	}
	freshStage.End()
	freshDone()
	if err := h.s.Close(); err != nil { t.Fatal(err) }
	h2 := attributionHarness(t)
	current, currentDone := BeginClassifiedImplication(ObligationLoopInvariant)
	currentStage := current.Push(StageOther)
	old.Push(StageBDDJoined).End()
	oldDone()
	if err := h.s.Close(); err != nil { t.Fatal(err) }
	if !Enabled() || h2.s.snapshot("test").Totals.ImplicationsStarted != 1 {
		t.Fatal("old session affected new session")
	}
	currentStage.End()
	currentDone()
}

func TestImplicationAttributionDuplicateAndOutOfOrderTokens(t *testing.T) {
	h := attributionHarness(t)
	o, done := BeginClassifiedImplication(ObligationLoopReach)
	first := o.Push(StageDAGAdmission)
	h.clock.advance(1)
	first.End()
	second := o.Push(StageCanonicalPass)
	first.End() // Old token at the same depth cannot pop the new frame.
	if attributionSnapshot(t, h).Active.Stage != StageCanonicalPass {
		t.Fatal("duplicate token popped a replacement")
	}
	third := o.Push(StageBDDJoined)
	h.clock.advance(2)
	second.End() // Out of order: charge BDD, retire this owner into other.
	h.clock.advance(3)
	third.End()
	second.End()
	d := attributionSnapshot(t, h)
	if d.Active.Stage != StageOther || d.Active.DetailComplete || d.ProcessDetailComplete || d.OwnershipAnomalies != 1 {
		t.Fatalf("out-of-order fallback = %+v", d)
	}
	requireVector(t, d.ProcessNS, stageVector{3, 1, 0, 0, 2})
	done()
	done()
	if h.s.snapshot("test").Totals.ImplicationsFinished != 1 {
		t.Fatal("duplicate finish incremented count")
	}
}

func TestImplicationAttributionSuspendedOwnerBarrier(t *testing.T) {
	h := attributionHarness(t)
	outer, outerDone := BeginClassifiedImplication(ObligationLoopInvariant)
	outerStage := outer.Push(StageRecursiveScheduling)
	ready, release, finished := make(chan struct{}), make(chan struct{}), make(chan struct{})
	var released sync.Once
	releaseOwner := func() { released.Do(func() { close(release) }) }
	t.Cleanup(releaseOwner)
	go func() {
		inner, innerDone := BeginClassifiedImplication(ObligationTrapDomain)
		innerStage := inner.Push(StageBDDJoined)
		close(ready)
		<-release
		innerStage.End()
		innerDone()
		close(finished)
	}()
	await(t, ready)
	before := attributionSnapshot(t, h)
	outer.Push(StageCanonicalPass).End()
	after := attributionSnapshot(t, h)
	if after.Active.ID != before.Active.ID || after.Active.Stage != StageBDDJoined || after.ProcessDetailComplete || after.Candidate.DetailComplete || after.OwnershipAnomalies != 1 {
		t.Fatalf("suspended owner displaced current owner: %+v", after)
	}
	outerDone() // Ended parent must not be restored by inner's later completion.
	releaseOwner()
	await(t, finished)
	outerStage.End()
	if h.s.snapshot("test").Phase != "validation" {
		t.Fatal("out-of-order completion restored ended parent")
	}
}

func TestImplicationAttributionCloseFreezesOpenOwner(t *testing.T) {
	h := attributionHarness(t)
	o, done := BeginClassifiedImplication(ObligationLoopResult)
	token := o.Push(StageBDDJoined)
	h.clock.advance(5)
	if err := h.s.Close(); err != nil { t.Fatal(err) }
	before := h.s.snapshot("test")
	h.clock.advance(99)
	token.End()
	o.Push(StageCanonicalPass).End()
	done()
	after := h.s.snapshot("test")
	if !reflect.DeepEqual(before, after) || after.Totals.ImplicationsStarted != 1 || after.Totals.ImplicationsFinished != 0 {
		t.Fatal("late detail or finish changed frozen Close")
	}
	d := attributionSnapshot(t, h)
	if d.ProcessDetailComplete || d.Candidate.DetailComplete || d.Active.DetailComplete {
		t.Fatal("open owner reported complete at Close")
	}
	if d.Active.Stage != StageBDDJoined || d.Active.StageScopeAgeNS != 5 {
		t.Fatal("Close changed the frozen cutoff stage or age")
	}
	requireVector(t, d.ProcessNS, stageVector{0, 0, 0, 0, 5})
}

func TestImplicationAttributionPanicUnwind(t *testing.T) {
	h := attributionHarness(t)
	outer, outerDone := BeginClassifiedImplication(ObligationLoopInvariant)
	outerStage := outer.Push(StageRecursiveScheduling)
	want := &struct{ value int }{7}
	var got any
	func() {
		defer func() { got = recover() }()
		inner, innerDone := BeginClassifiedImplication(ObligationTrapDomain)
		defer innerDone()
		token := inner.Push(StageCanonicalPass)
		defer token.End()
		h.clock.advance(3)
		panic(want)
	}()
	d := attributionSnapshot(t, h)
	if got != want || d.Active.Class != ObligationLoopInvariant || d.Active.Stage != StageRecursiveScheduling || !d.ProcessDetailComplete || h.s.snapshot("test").Totals.ImplicationsFinished != 1 {
		t.Fatalf("panic identity or restoration changed: panic=%v detail=%+v", got, d)
	}
	outerStage.End()
	outerDone()
}

func TestImplicationAttributionSlotsAndEpochBarrier(t *testing.T) {
	h := attributionHarness(t)
	var owners [implicationSlots]*ImplicationObservation
	var finishes [implicationSlots]func()
	for i := range owners {
		owners[i], finishes[i] = BeginClassifiedImplication(ObligationLoopInvariant)
		if owners[i] == nil { t.Fatalf("slot %d refused", i) }
	}
	ninth, ninthDone := BeginClassifiedImplication(ObligationLoopResult)
	if ninth != nil { t.Fatal("ninth detailed owner accepted") }
	ninthDone()
	old := owners[implicationSlots-1]
	oldToken := old.Push(StageCanonicalPass)
	checked, release, finished := make(chan struct{}), make(chan struct{}), make(chan struct{})
	var released sync.Once
	releaseCheck := func() { released.Do(func() { close(release) }) }
	t.Cleanup(releaseCheck)
	go func() {
		if !old.liveFast() { t.Error("expected a live fast check before reuse"); close(checked); close(finished); return }
		close(checked)
		<-release
		h.s.mu.Lock()
		got := old.pushLocked(StageBDDJoined)
		oldToken.endLocked()
		h.s.mu.Unlock()
		if got.owner != nil { t.Error("old epoch survived locked recheck") }
		close(finished)
	}()
	await(t, checked)
	oldToken.End()
	finishes[implicationSlots-1]()
	reused, reusedDone := BeginClassifiedImplication(ObligationStraightWrite)
	if reused == nil || reused.slot != old.slot || reused.epoch == old.epoch {
		t.Fatal("slot did not reuse with a fresh epoch")
	}
	token := reused.Push(StageDAGAdmission)
	dropped := attributionSnapshot(t, h).DroppedEvents
	releaseCheck()
	await(t, finished)
	old.Push(StageBDDJoined).End()
	d := attributionSnapshot(t, h)
	if d.Active.Stage != StageDAGAdmission || d.DroppedEvents != dropped {
		t.Fatal("stale epoch changed stage or pretended to count rejected fast paths")
	}
	token.End()
	reusedDone()
	for i := implicationSlots-2; i >= 0; i-- { finishes[i]() }
}

func TestImplicationAttributionStackLimit(t *testing.T) {
	h := attributionHarness(t)
	o, done := BeginClassifiedImplication(ObligationLoopReach)
	var tokens [implicationStack]ImplicationToken
	for i := range tokens {
		tokens[i] = o.Push(StageRecursiveScheduling)
		if tokens[i].owner == nil { t.Fatalf("frame %d refused", i) }
	}
	h.clock.advance(2)
	if overflow := o.Push(StageDAGAdmission); overflow.owner != nil {
		t.Fatal("sixty-fifth frame accepted")
	}
	h.clock.advance(3)
	for i := len(tokens)-1; i >= 0; i-- { tokens[i].End() }
	d := attributionSnapshot(t, h)
	if !d.Limited || d.Active.DetailComplete || d.Candidate.DetailComplete || d.ProcessDetailComplete || d.DetailEvents != 64 || d.DroppedEvents != 1 {
		t.Fatalf("stack fallback = %+v", d)
	}
	requireVector(t, d.ProcessNS, stageVector{3, 0, 0, 2})
	done()
}

func TestImplicationAttributionEventCapRetiresGlobally(t *testing.T) {
	h := attributionHarness(t)
	h.s.mu.Lock()
	h.s.cfg.detailEventCap = 2
	h.s.mu.Unlock()
	o, done := BeginClassifiedImplication(ObligationLoopReach)
	first := o.Push(StageDAGAdmission)
	h.clock.advance(1)
	first.End()
	second := o.Push(StageCanonicalPass)
	h.clock.advance(2)
	if third := o.Push(StageBDDJoined); third.owner != nil { t.Fatal("push beyond cap accepted") }
	h.clock.advance(3)
	second.End()
	d := attributionSnapshot(t, h)
	if d.DetailEvents != 2 || !d.Limited || d.ProcessDetailComplete || h.s.detail.enabled.Load() {
		t.Fatalf("event retirement = %+v", d)
	}
	requireVector(t, d.ProcessNS, stageVector{3, 1, 2})
	done()
	BeginValidation("after global retirement")
	future, futureDone := BeginClassifiedImplication(ObligationLoopResult)
	if future != nil { t.Fatal("global cap accepted a later owner") }
	futureDone()
	if attributionSnapshot(t, h).Candidate.DetailComplete || h.s.snapshot("test").Totals.ImplicationsFinished != 2 {
		t.Fatal("global retirement reset completeness or changed original counts")
	}
	if implicationEventCap != 4_194_304 { t.Fatal("production event cap changed") }
}

func TestImplicationAttributionSaturationNeverWraps(t *testing.T) {
	for _, edge := range []string{"wrapper", "epoch", "generation", "candidate", "counter", "duration", "phase", "projection"} {
		t.Run(edge, func(t *testing.T) {
			h := attributionHarness(t)
			o, done := BeginClassifiedImplication(ObligationLoopInvariant)
			token := o.Push(StageDAGAdmission)
			h.s.mu.Lock()
			switch edge {
			case "wrapper": h.s.detail.nextID = ^uint64(0)
			case "epoch": h.s.detail.nextEpoch = ^uint64(0)
			case "generation": h.s.generation = ^uint64(0)
			case "candidate": h.s.candidate = ^uint64(0)
			case "counter": h.s.detail.entries[StageCanonicalPass] = ^uint64(0)
			case "duration", "projection": h.s.detail.processNS[StageDAGAdmission] = ^uint64(0)-1
			case "phase": h.s.totals.PhaseNS.Implication = ^uint64(0)-1
			}
			h.s.mu.Unlock()
			switch edge {
			case "wrapper", "epoch": _, finish := BeginClassifiedImplication(ObligationLoopReach); finish()
			case "generation": BeginSearch("generation exhaustion")
			case "candidate": BeginValidation("ordinal exhaustion")
			case "counter": o.Push(StageCanonicalPass)
			case "duration", "phase": h.clock.advance(2); token.End()
			case "projection":
				h.clock.advance(2)
				d := attributionSnapshot(t, h)
				if !d.CounterSaturated || d.ProcessDetailComplete || d.ProcessNS[StageDAGAdmission] != ^uint64(0) || h.s.detail.processNS[StageDAGAdmission] != ^uint64(0)-1 {
					t.Fatal("snapshot overflow wrapped or mutated accumulated time")
				}
				token.End()
			}
			d := attributionSnapshot(t, h)
			if !d.CounterSaturated || !d.Limited || d.ProcessDetailComplete || h.s.detail.enabled.Load() {
				t.Fatalf("saturation did not retire detail: %+v", d)
			}
			oldEvents := d.DetailEvents
			o.Push(StageBDDJoined).End()
			token.End()
			done()
			if h.s.detail.events != oldEvents { t.Fatal("retired event counter changed") }
		})
	}
}

func TestImplicationAttributionBoundedShapeAndState(t *testing.T) {
	if unsafe.Sizeof(implicationDetailState{}) > 64<<10 {
		t.Fatalf("fixed observer state = %d bytes", unsafe.Sizeof(implicationDetailState{}))
	}
	if unsafe.Sizeof(uintptr(0)) == 8 && unsafe.Sizeof(time.Time{}) == 24 && unsafe.Sizeof(implicationDetailState{}) != 22432 {
		t.Fatalf("64-bit concrete state differs from source layout: %d", unsafe.Sizeof(implicationDetailState{}))
	}
	// Populate concrete structs, including every array and optional object.
	maximum := ^uint64(0)
	d := implicationDetailRecord{Version: 1, Coverage: 1, DetailEvents: maximum, DroppedEvents: maximum, OwnershipAnomalies: maximum, UnattributedNS: maximum}
	d.Candidate = &implicationCandidateRecord{Key: [2]uint64{maximum, maximum}, Started: maximum, Finished: maximum}
	d.Candidate.Dominant = implicationDominantRecord{Class: ObligationStraightWrite, implicationClassRow: implicationClassRow{Started: maximum, Finished: maximum}}
	d.Active = &implicationActiveRecord{ID: maximum, Class: ObligationStraightWrite, Stage: StageStandalonePruning, StageScopeAgeNS: maximum}
	for i := range d.ProcessNS {
		d.ProcessNS[i], d.ProcessStageEntries[i] = maximum, maximum
		d.Candidate.NS[i], d.Candidate.Dominant.NS[i], d.Active.NS[i] = maximum, maximum, maximum
	}
	fullCandidate, fullActive := d.Candidate, d.Active
	for variant := 0; variant < 4; variant++ {
		d.Candidate, d.Active = nil, nil
		if variant&1 != 0 { d.Candidate = fullCandidate }
		if variant&2 != 0 { d.Active = fullActive }
		member, err := json.Marshal(struct { Detail *implicationDetailRecord `json:"implication_detail"` }{&d})
		if err != nil { t.Fatal(err) }
		insertion := len(member)-1 // Remove braces, add separating comma.
		if insertion > implicationExtensionBytes { t.Fatalf("extension variant %d = %d", variant, insertion) }
		r := record{}
		minInt := -int64(1) << (strconv.IntSize-1)
		var fill func(reflect.Value)
		fill = func(v reflect.Value) {
			switch v.Kind() {
			case reflect.Struct: for i := 0; i < v.NumField(); i++ { fill(v.Field(i)) }
			case reflect.Uint64: v.SetUint(maximum)
			case reflect.Int: v.SetInt(minInt)
			case reflect.String: v.SetString(strings.Repeat("\x00", maxIdentifier))
			}
		}
		fill(reflect.ValueOf(&r).Elem())
		r.ImplicationDetail = &d
		row, err := json.Marshal(r)
		if err != nil { t.Fatal(err) }
		if len(row)+1 > maxRecordBytes || (len(row)+1)*542+maxRecordBytes > maxBytes {
			t.Fatalf("variant %d violates row or 45-minute reserve: %d", variant, len(row)+1)
		}
		if strconv.IntSize == 64 && len(row)+1 != 5485+insertion { t.Fatal("extension does not preserve original row shape") }
	}
	// Snapshot encoding must own copies after the observer lock is released.
	h := attributionHarness(t)
	o, done := BeginClassifiedImplication(ObligationLoopInvariant)
	token := o.Push(StageCanonicalPass)
	h.clock.advance(2)
	frozen := h.s.snapshot("test")
	before, err := json.Marshal(frozen)
	if err != nil { t.Fatal(err) }
	h.clock.advance(3)
	token.End()
	done()
	BeginValidation("new key")
	after, err := json.Marshal(frozen)
	if err != nil { t.Fatal(err) }
	if !bytes.Equal(before, after) { t.Fatal("snapshot retains mutable arrays or rows") }
}

func TestImplicationAttributionPopulatedSamplingBudgets(t *testing.T) {
	for _, minutes := range []int{90, 100} {
		t.Run(strconv.Itoa(minutes), func(t *testing.T) {
			h := attributionHarness(t)
			o, done := BeginClassifiedImplication(ObligationLoopInvariant)
			token := o.Push(StageBDDJoined)
			for i := 0; i < minutes*12; i++ { h.tick(t, interval) }
			token.End()
			done()
			if err := h.s.Close(); err != nil { t.Fatal(err) }
			r := decode(t, h.out.data())
			if len(r) != minutes*12+2 || len(h.out.data()) > maxBytes { t.Fatalf("sampling records=%d bytes=%d", len(r), len(h.out.data())) }
			for i, row := range r {
				if row.OutputLimited { t.Fatalf("ordinary populated sample %d was limited", i) }
				if i > 0 && (row.ImplicationDetail == nil || row.ImplicationDetail.ProcessNS[StageBDDJoined] == 0) { t.Fatalf("unpopulated sample %d", i) }
			}
		})
	}
	t.Run("byte close reservation", func(t *testing.T) {
		h := newHarness(t, maxRecords, 2*maxRecordBytes)
		BeginSearch(strings.Repeat("\n", 1000))
		BeginValidation(strings.Repeat("\n", 1000))
		o, _ := BeginClassifiedImplication(ObligationLoopInvariant)
		o.Push(StageBDDJoined)
		for i := 0; i < 30; i++ { h.tick(t, interval) }
		if err := h.s.Close(); err != nil { t.Fatal(err) }
		r := decode(t, h.out.data())
		if len(h.out.data()) > 2*maxRecordBytes || !r[len(r)-1].OutputLimited || r[len(r)-1].Event != "close" { t.Fatal("detail violated close reserve") }
	})
}

func TestImplicationAttributionWriterFailureAndBlockedClose(t *testing.T) {
	for _, short := range []bool{false, true} {
		t.Run(strconv.FormatBool(short), func(t *testing.T) {
			h := attributionHarness(t)
			o, done := BeginClassifiedImplication(ObligationLoopInvariant)
			token := o.Push(StageCanonicalPass)
			want := errors.New("detail writer failure")
			if short { want = io.ErrShortWrite }
			h.s.writer = writeFunc(func(p []byte) (int, error) {
				if short { return len(p)-1, nil }
				return 0, want
			})
			h.clock.advance(interval)
			h.ticker.ticks <- h.clock.now()
			await(t, h.s.done)
			if err := h.s.Close(); !errors.Is(err, want) { t.Fatalf("Close error = %v", err) }
			frozen := h.s.snapshot("test")
			token.End()
			done()
			if !reflect.DeepEqual(frozen, h.s.snapshot("test")) { t.Fatal("late hooks changed failed-writer cutoff") }
		})
	}
	t.Run("blocked", func(t *testing.T) {
		h := attributionHarness(t)
		o, done := BeginClassifiedImplication(ObligationLoopResult)
		token := o.Push(StageBDDJoined)
		entered, release := make(chan struct{}), make(chan struct{})
		var once, released sync.Once
		releaseWriter := func() { released.Do(func() { close(release) }) }
		t.Cleanup(releaseWriter)
		h.s.writer = writeFunc(func(p []byte) (int, error) {
			once.Do(func() { close(entered); <-release })
			return h.out.Write(p)
		})
		h.clock.advance(interval)
		h.ticker.ticks <- h.clock.now()
		await(t, entered)
		hooksDone := make(chan struct{})
		go func() { token.End(); o.Push(StageOther).End(); close(hooksDone) }()
		await(t, hooksDone)
		closed := make(chan struct{})
		go func() { _ = h.s.Close(); close(closed) }()
		// Acquire after the closing goroutine has actually reached its cutoff,
		// using the already-existing stop channel rather than scheduler timing.
		await(t, h.s.stop)
		frozen := h.s.snapshot("test")
		select { case <-closed: t.Fatal("Close returned before writer release"); default: }
		h.clock.advance(interval)
		done()
		releaseWriter()
		await(t, closed)
		if !reflect.DeepEqual(frozen, h.s.snapshot("test")) { t.Fatal("blocked writer changed cutoff") }
	})
}

func TestImplicationAttributionDisabledRetiredAndStaleCost(t *testing.T) {
	if Enabled() { t.Fatal("unexpected active observer") }
	var nilOwner *ImplicationObservation
	if allocs := testing.AllocsPerRun(100, func() {
		o, done := BeginClassifiedImplication(ObligationLoopInvariant)
		o.Push(StageOther).End()
		nilOwner.Push(StageDAGAdmission).End()
		ImplicationToken{}.End()
		done()
	}); allocs != 0 { t.Fatalf("disabled allocations = %g", allocs) }
	h := attributionHarness(t)
	old, oldDone := BeginClassifiedImplication(ObligationLoopInvariant)
	oldToken := old.Push(StageOther)
	oldToken.End()
	oldDone()
	fresh, freshDone := BeginClassifiedImplication(ObligationLoopResult)
	freshToken := fresh.Push(StageOther)
	var clockCalls atomic.Uint64
	h.s.mu.Lock()
	h.s.cfg.now = func() time.Time { clockCalls.Add(1); return h.clock.now() }
	h.s.mu.Unlock()
	beforeEvents, beforeDropped := h.s.detail.events, h.s.detail.dropped
	if allocs := testing.AllocsPerRun(100, func() {
		nilOwner.Push(StageOther).End()
		old.Push(StageBDDJoined).End()
		oldToken.End()
	}); allocs != 0 { t.Fatalf("stale allocations = %g", allocs) }
	if clockCalls.Load() != 0 || h.s.detail.events != beforeEvents || h.s.detail.dropped != beforeDropped { t.Fatal("nil/stale path clocks or mutates counters") }
	h.s.mu.Lock()
	h.s.charge(h.clock.now())
	h.s.refuseImplicationDetail(true, false)
	h.s.retireImplicationDetail(h.clock.now(), true)
	h.s.mu.Unlock()
	if allocs := testing.AllocsPerRun(100, func() { fresh.Push(StageBDDJoined).End(); freshToken.End() }); allocs != 0 { t.Fatalf("retired allocations = %g", allocs) }
	if clockCalls.Load() != 0 { t.Fatal("globally retired detail called clock") }
	if h.s.snapshot("test").Totals.ImplicationsStarted != 2 { t.Fatal("nil adapter emitted an extra wrapper") }
	freshDone()
}

// A suspended owner's completion can saturate counters and retire a different
// current owner. Its pre-cutoff joined work must stay in that original stage.
func TestImplicationAttributionSuspendedFinishSaturation(t *testing.T) {
	for _, edge := range []string{"candidate_finished", "class_finished", "refusal"} {
		t.Run(edge, func(t *testing.T) {
			h := attributionHarness(t)
			outer, outerDone := BeginClassifiedImplication(ObligationLoopInvariant)
			outerToken := outer.Push(StageDAGAdmission)
			h.clock.advance(2)
			inner, innerDone := BeginClassifiedImplication(ObligationLoopResult)
			innerToken := inner.Push(StageBDDJoined)
			h.clock.advance(5)
			h.s.mu.Lock()
			switch edge {
			case "candidate_finished": h.s.detail.candidate.finished = ^uint64(0)
			case "class_finished": h.s.detail.candidate.classes[ObligationLoopInvariant].Finished = ^uint64(0)
			case "refusal": h.s.detail.dropped = ^uint64(0)
			}
			h.s.mu.Unlock()
			outerDone()
			d := attributionSnapshot(t, h)
			requireVector(t, d.ProcessNS, stageVector{0, 2, 0, 0, 5, 0})
			if !d.CounterSaturated || !d.Limited || d.ProcessDetailComplete || d.Candidate.DetailComplete || d.Active.Stage != StageOther || h.s.detail.enabled.Load() {
				t.Fatal("suspended finish did not retire detail at the charged cutoff")
			}
			h.clock.advance(3)
			innerToken.End()
			outerToken.End()
			innerDone()
			requireVector(t, attributionSnapshot(t, h).ProcessNS, stageVector{3, 2, 0, 0, 5, 0})
			if h.s.snapshot("test").Totals.ImplicationsFinished != 2 { t.Fatal("retirement changed original wrapper completion count") }
		})
	}
}
