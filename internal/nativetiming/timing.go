// Package nativetiming observes the native compiler without affecting its
// decisions. It is inactive unless a caller explicitly starts one session.
// Hooks accept identifiers and structural counts only, never source or values.
// Phase attribution follows the serial native compiler's nesting. Concurrent
// hooks are race-safe and cannot restore completed/superseded scopes, but do not
// provide independent per-goroutine phase attribution.
package nativetiming

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"io"
	"sync"
	"sync/atomic"
	"time"
	"unicode/utf8"
)

// Cover the 90-minute prerequisite budget plus 10 minutes of diagnostic
// allowance, with separate start/close slots. This does not extend a deadline.
const (
	interval       = 5 * time.Second
	maxRecords     = 2 + int((90*time.Minute+10*time.Minute)/interval)
	maxBytes       = 4 << 20
	maxRecordBytes = 8192 // Includes JSON escaping and maximum-width numbers.
	maxIdentifier  = 96
)

var active atomic.Pointer[Session]

// Enabled allows callers to avoid constructing identifiers when observation is
// disabled. Begin hooks still check the session themselves, so racing Close is
// safe. A draining session can briefly return true until its logger has joined.
func Enabled() bool { return active.Load() != nil }

type ticker interface {
	channel() <-chan time.Time
	stop()
}

type realTicker struct{ *time.Ticker }

func (t realTicker) channel() <-chan time.Time { return t.C }
func (t realTicker) stop()                     { t.Stop() }

// config is private so production sampling and output limits cannot be changed
// by an environment variable, command-line option, or hook.
type config struct {
	now       func() time.Time
	newTicker func(time.Duration) ticker
	recordCap int
	byteCap   int
	detailEventCap uint64 // Private finite-control override; zero selects the production cap.
}

// Session owns the sole logger. Close must be called, including after an error
// in the observed computation. The writer must eventually return from Write;
// io.Writer provides no cancellation mechanism for a blocked write.
type Session struct {
	mu         sync.Mutex
	cfg        config
	started    time.Time
	closedAt   time.Time
	closed     bool
	generation uint64
	candidate  uint64
	current    *scope
	totals     totals
	last       completedSearch
	stop       chan struct{}
	done       chan struct{}
	closeOnce  sync.Once
	detail     implicationDetailState

	// Only the logger accesses these fields, and Close reads err after joining.
	writer  io.Writer
	err     error
	records int
	bytes   int
	limited bool
}

type phase uint8

const (
	idle phase = iota
	search
	validation
	witnesses
	coupling
	valuation
	implication
)

func (p phase) String() string {
	return [...]string{"idle", "search", "validation", "witnesses", "coupling", "valuation", "implication"}[p]
}

type context struct {
	Function         string `json:"function"`
	FunctionOrdinal  uint64 `json:"function_ordinal"`
	Candidate        string `json:"candidate"`
	CandidateOrdinal uint64 `json:"candidate_ordinal"`
	ASMLoops         int    `json:"asm_loops"`
	OakLoops         int    `json:"oak_loops"`
	ResultChunk      int    `json:"result_chunk"`
	Abstract         bool   `json:"abstract"`
	CheckedWitnesses int    `json:"checked_witnesses"`
	WitnessWork      int    `json:"witness_work"`
	Slots            int    `json:"slots"`
	Nodes            int    `json:"nodes"`
	Names            int    `json:"names"`
	Targets          int    `json:"targets"`
	Rounds           int    `json:"rounds"`
	Bindings         int    `json:"bindings"`
}

type scope struct {
	parent      *scope
	generation  uint64
	kind        phase
	phase       phase
	started     time.Time
	phaseSince  time.Time
	activeSince time.Time
	ended       bool
	context     context
	observation ImplicationObservation
	wrapperID   uint64
	wrapperClass ObligationClass
}

type phaseCosts struct {
	Search      uint64 `json:"search"`
	Validation  uint64 `json:"validation"`
	Witnesses   uint64 `json:"witnesses"`
	Coupling    uint64 `json:"coupling"`
	Valuation   uint64 `json:"valuation"`
	Implication uint64 `json:"implication"`
}

func (p *phaseCosts) add(k phase, ns uint64) {
	switch k {
	case search:
		p.Search += ns
	case validation:
		p.Validation += ns
	case witnesses:
		p.Witnesses += ns
	case coupling:
		p.Coupling += ns
	case valuation:
		p.Valuation += ns
	case implication:
		p.Implication += ns
	}
}

type totals struct {
	SearchesStarted      uint64     `json:"searches_started"`
	SearchesCompleted    uint64     `json:"searches_completed"`
	SearchesFailed       uint64     `json:"searches_failed"`
	SearchNS             uint64     `json:"search_ns"`
	Considered           uint64     `json:"considered"`
	Materialized         uint64     `json:"materialized"`
	SearchValidations    uint64     `json:"search_validations"`
	ValidationsStarted   uint64     `json:"validations_started"`
	ValidationsCompleted uint64     `json:"validations_completed"`
	ValidationNS         uint64     `json:"validation_ns"`
	Cached               uint64     `json:"cached"`
	LastOutcome          int        `json:"last_outcome"`
	LoopsStarted         uint64     `json:"loops_started"`
	LoopsCompleted       uint64     `json:"loops_completed"`
	LoopNS               uint64     `json:"loop_ns"`
	Couplings            uint64     `json:"couplings"`
	CheckedWitnesses     uint64     `json:"checked_witnesses"`
	WitnessWork          uint64     `json:"witness_work"`
	Slots                uint64     `json:"slots"`
	ValuationsStarted    uint64     `json:"valuations_started"`
	ValuationsCompleted  uint64     `json:"valuations_completed"`
	ValuationNS          uint64     `json:"valuation_ns"`
	Evaluations          uint64     `json:"evaluations"`
	ImplicationsStarted  uint64     `json:"implications_started"`
	ImplicationsFinished uint64     `json:"implications_finished"`
	PhaseNS              phaseCosts `json:"exclusive_phase_ns"`
}

type completedSearch struct {
	Function string `json:"function"`
	Ordinal  uint64 `json:"ordinal"`
	NS       uint64 `json:"duration_ns"`
	Failed   bool   `json:"failed"`
}

type record struct {
	Schema         string          `json:"schema"`
	Event          string          `json:"event"`
	Sequence       int             `json:"sequence"`
	ElapsedNS      uint64          `json:"elapsed_ns"`
	Phase          string          `json:"phase"`
	PhaseAgeNS     uint64          `json:"phase_age_ns"`
	FunctionAgeNS  uint64          `json:"function_age_ns"`
	CandidateAgeNS uint64          `json:"candidate_age_ns"`
	Current        context         `json:"current"`
	Totals         totals          `json:"totals"`
	LastSearch     completedSearch `json:"last_search"`
	OutputLimited  bool            `json:"output_limited"`
	ImplicationDetail *implicationDetailRecord `json:"implication_detail,omitempty"`
}

// Start enables observation for one explicit session. At most one session can
// be active. Records are JSON lines: start, status every five seconds, and close.
// The complete stream is limited to 1202 records and 4 MiB, reserving room for
// close even if either output limit is reached. Start surfaces initial write
// errors; subsequent write errors are returned by Close.
func Start(w io.Writer) (*Session, error) {
	return start(w, config{
		now:       time.Now,
		newTicker: func(d time.Duration) ticker { return realTicker{time.NewTicker(d)} },
		recordCap: maxRecords,
		byteCap:   maxBytes,
	})
}

func start(w io.Writer, cfg config) (*Session, error) {
	if w == nil {
		return nil, errors.New("nativetiming: nil writer")
	}
	if cfg.recordCap < 2 || cfg.byteCap < 2*maxRecordBytes {
		return nil, errors.New("nativetiming: output limits cannot reserve start and close")
	}
	s := &Session{cfg: cfg, started: cfg.now(), writer: w, stop: make(chan struct{}), done: make(chan struct{})}
	s.detail.complete = true
	s.detail.enabled.Store(true)
	if !active.CompareAndSwap(nil, s) {
		return nil, errors.New("nativetiming: a session is already active")
	}
	if !s.emit("start") {
		s.mu.Lock()
		s.closed = true
		s.mu.Unlock()
		close(s.done)
		active.CompareAndSwap(s, nil)
		return nil, s.err
	}
	t := cfg.newTicker(interval)
	go s.run(t)
	return s, nil
}

// Close disables hooks, stops and joins the logger, and returns any write error.
// It is safe to call concurrently or repeatedly. A stale scope completion cannot
// affect a later session. No writer call occurs while holding the state mutex.
func (s *Session) Close() error {
	s.closeOnce.Do(func() {
		s.mu.Lock()
		s.closedAt = s.cfg.now()
		s.charge(s.closedAt)
		s.freezeImplicationDetail()
		s.closed = true
		s.mu.Unlock()
		close(s.stop)
	})
	<-s.done
	active.CompareAndSwap(s, nil)
	return s.err
}

func (s *Session) run(t ticker) {
	defer close(s.done)
	defer t.stop()
	var lastSlot uint64
	for {
		select {
		case <-s.stop:
			s.emit("close")
			return
		case <-t.channel():
			select {
			case <-s.stop:
				s.emit("close")
				return
			default:
			}
			now := s.cfg.now()
			// Anchor windows to the start rather than the prior wake: ordinary
			// timer jitter must not turn five-second sampling into ten seconds.
			slot := elapsed(s.started, now) / uint64(interval)
			if slot <= lastSlot || s.limited {
				continue
			}
			lastSlot = slot
			if !s.emit("status") {
				return
			}
		}
	}
}

// emit is exclusively owned by the logger (or Start before launching it).
func (s *Session) emit(event string) bool {
	r := s.snapshot(event)
	r.Sequence = s.records + 1
	r.OutputLimited = s.limited
	data, err := json.Marshal(r)
	if err != nil {
		s.err = err
		return false
	}
	data = append(data, '\n')
	if len(data) > maxRecordBytes {
		s.err = errors.New("nativetiming: record exceeds bounded schema")
		return false
	}
	if event == "status" && (s.records >= s.cfg.recordCap-1 || s.bytes+len(data)+maxRecordBytes > s.cfg.byteCap) {
		s.limited = true
		return true
	}
	if s.records >= s.cfg.recordCap || s.bytes+len(data) > s.cfg.byteCap {
		s.err = errors.New("nativetiming: output limit exhausted")
		return false
	}
	n, err := s.writer.Write(data)
	s.bytes += n
	s.records++
	if err == nil && n != len(data) {
		err = io.ErrShortWrite
	}
	if err != nil {
		s.err = err
		return false
	}
	return true
}

func (s *Session) snapshot(event string) record {
	s.mu.Lock()
	defer s.mu.Unlock()
	now := s.cfg.now()
	if s.closed {
		now = s.closedAt
	}
	r := record{Schema: "oak.native.timing.v1", Event: event, ElapsedNS: elapsed(s.started, now), Phase: idle.String(), Totals: s.totals, LastSearch: s.last}
	if f := s.current; f != nil {
		r.Phase = f.phase.String()
		r.PhaseAgeNS = elapsed(f.phaseSince, now)
		r.Current = f.context
		if !s.closed {
			r.Totals.PhaseNS.add(f.phase, elapsed(f.activeSince, now))
		}
		foundCandidate := false
		for ancestor := f; ancestor != nil; ancestor = ancestor.parent {
			if ancestor.ended {
				continue
			}
			switch ancestor.kind {
			case search:
				r.FunctionAgeNS = elapsed(ancestor.started, now)
			case validation:
				if !foundCandidate {
					r.CandidateAgeNS = elapsed(ancestor.started, now)
					foundCandidate = true
				}
			}
		}
	}
	r.ImplicationDetail = s.snapshotImplicationDetail(r.Current, now)
	return r
}

func elapsed(from, to time.Time) uint64 {
	if d := to.Sub(from); d > 0 {
		return uint64(d)
	}
	return 0
}

func count(n int) uint64 {
	if n > 0 {
		return uint64(n)
	}
	return 0
}

func identifier(s string) string {
	if len(s) <= maxIdentifier {
		return s
	}
	sum := sha256.Sum256([]byte(s))
	n := maxIdentifier - 17
	for n > 0 && !utf8.RuneStart(s[n]) {
		n--
	}
	return s[:n] + "#" + hex.EncodeToString(sum[:8])
}

// charge records exclusive time for the current phase, which avoids counting
// nested validation/loop/implication/valuation work again as search time.
func (s *Session) charge(now time.Time) {
	if s.current != nil {
		ns := elapsed(s.current.activeSince, now)
		if s.current.phase == implication && ^uint64(0)-s.totals.PhaseNS.Implication < ns {
			// Preserve the old counter's arithmetic, but never certify exact
			// attribution after that old counter has overflowed.
			s.saturateImplicationDetail()
		}
		s.totals.PhaseNS.add(s.current.phase, ns)
		if s.current.phase == implication {
			if s.detail.pendingOwner == s.current {
				before := elapsed(s.current.activeSince, s.detail.pendingSince)
				if before > ns {
					before = ns
				}
				s.chargeImplicationStage(s.current, s.detail.pendingStage, before, s.detail.pendingUnattributed)
				s.chargeImplicationStage(s.current, StageOther, ns-before, true)
				s.detail.pendingOwner = nil
			} else {
				s.chargeImplicationDetail(s.current, ns)
			}
		}
		s.current.activeSince = now
	}
	if s.detail.saturated && s.detail.enabled.Load() {
		s.retireImplicationDetail(now, true)
	}
}

// begin returns with s.mu held when successful. New searches establish a new
// root generation; older, overlapping completions can never restore that root.
func begin(k phase) (*Session, *scope) {
	s := active.Load()
	if s == nil {
		return nil, nil
	}
	s.mu.Lock()
	if s.closed {
		s.mu.Unlock()
		return nil, nil
	}
	now := s.cfg.now()
	s.charge(now)
	f := &scope{kind: k, phase: k, started: now, phaseSince: now, activeSince: now, parent: s.current}
	if k == search {
		if s.generation == ^uint64(0) {
			s.saturateImplicationDetail()
		}
		s.supersedeImplicationDetail(now)
		s.generation++
		s.candidate = 0
		f.parent = nil
	} else if f.parent != nil {
		f.context = f.parent.context
	}
	f.generation = s.generation
	s.current = f
	return s, f
}

// finish is called under s.mu. It is idempotent and supports out-of-order
// completion: only the current frame may restore its nearest unfinished parent.
func (s *Session) finish(f *scope) (uint64, bool) {
	if s.closed || f.ended {
		return 0, false
	}
	now := s.cfg.now()
	f.ended = true
	if s.current == f {
		s.charge(now)
		parent := f.parent
		for parent != nil && parent.ended {
			parent = parent.parent
		}
		s.current = parent
		if parent != nil {
			parent.activeSince = now
		}
	}
	if f.kind == implication {
		s.finishImplicationDetail(f, now)
	}
	if f.kind == validation && s.detail.candidate.key == implicationKey(f.context) &&
		(s.current == nil || s.current.context.CandidateOrdinal == 0) {
		// A normally completed validation has no displayed candidate. Keep
		// its storage bounded and omit it until the next validation reset.
		s.detail.candidate.valid = false
	}
	return elapsed(f.started, now), true
}

var (
	noSearch      = func(int, int, int, bool) {}
	noValidation  = func(int, bool) {}
	noLoops       = func() {}
	noValuation   = func(uint32) {}
	noImplication = func() {}
)

// BeginSearch starts a function search. Complete it with final structural search
// counts and failure status. Names must be identifiers, never source text.
func BeginSearch(function string) func(considered, materialized, validations int, failed bool) {
	s, f := begin(search)
	if s == nil {
		return noSearch
	}
	s.totals.SearchesStarted++
	f.context.Function = identifier(function)
	f.context.FunctionOrdinal = s.totals.SearchesStarted
	s.mu.Unlock()
	return func(considered, materialized, validations int, failed bool) {
		s.mu.Lock()
		defer s.mu.Unlock()
		if ns, ok := s.finish(f); ok {
			s.totals.SearchesCompleted++
			s.totals.SearchNS += ns
			s.totals.Considered += count(considered)
			s.totals.Materialized += count(materialized)
			s.totals.SearchValidations += count(validations)
			if failed {
				s.totals.SearchesFailed++
			}
			s.last = completedSearch{Function: f.context.Function, Ordinal: f.context.FunctionOrdinal, NS: ns, Failed: failed}
		}
	}
}

// BeginValidation starts one candidate's validation. The outcome is numeric so
// diagnostic records cannot include verifier messages or runtime values.
func BeginValidation(candidate string) func(outcome int, cached bool) {
	s, f := begin(validation)
	if s == nil {
		return noValidation
	}
	s.totals.ValidationsStarted++
	s.candidate++
	f.context.Candidate = identifier(candidate)
	f.context.CandidateOrdinal = s.candidate
	s.resetImplicationCandidate(f.context)
	s.mu.Unlock()
	return func(outcome int, cached bool) {
		s.mu.Lock()
		defer s.mu.Unlock()
		if ns, ok := s.finish(f); ok {
			s.totals.ValidationsCompleted++
			s.totals.ValidationNS += ns
			s.totals.LastOutcome = outcome
			if cached {
				s.totals.Cached++
			}
		}
	}
}

// BeginLoops observes witness checking followed by optional coupling.
func BeginLoops(asmLoops, oakLoops, resultChunk int, abstract bool) func() {
	s, f := begin(witnesses)
	if s == nil {
		return noLoops
	}
	s.totals.LoopsStarted++
	f.context.ASMLoops, f.context.OakLoops, f.context.ResultChunk, f.context.Abstract = asmLoops, oakLoops, resultChunk, abstract
	s.mu.Unlock()
	return func() {
		s.mu.Lock()
		defer s.mu.Unlock()
		if ns, ok := s.finish(f); ok {
			s.totals.LoopsCompleted++
			s.totals.LoopNS += ns
		}
	}
}

// Coupling transitions the nearest unfinished loop scope to coupling. It does
// nothing outside a loop scope. Counts describe work, never witness contents.
func Coupling(checkedWitnesses, witnessWork, slots int) {
	s := active.Load()
	if s == nil {
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.closed {
		return
	}
	for f := s.current; f != nil; f = f.parent {
		if f.kind != witnesses || f.ended || f.generation != s.generation {
			continue
		}
		now := s.cfg.now()
		if s.current == f {
			s.charge(now)
		}
		f.phase, f.phaseSince = coupling, now
		f.context.CheckedWitnesses, f.context.WitnessWork, f.context.Slots = checkedWitnesses, witnessWork, slots
		s.totals.Couplings++
		s.totals.CheckedWitnesses += count(checkedWitnesses)
		s.totals.WitnessWork += count(witnessWork)
		s.totals.Slots += count(slots)
		return
	}
}

// BeginValuation observes one valuation batch, with a single final evaluation
// count. It deliberately has no hook inside the node/evaluation hot loop.
func BeginValuation(nodes, names, targets, rounds, bindings int) func(evaluations uint32) {
	s, f := begin(valuation)
	if s == nil {
		return noValuation
	}
	s.totals.ValuationsStarted++
	f.context.Nodes, f.context.Names, f.context.Targets, f.context.Rounds, f.context.Bindings = nodes, names, targets, rounds, bindings
	s.mu.Unlock()
	return func(evaluations uint32) {
		s.mu.Lock()
		defer s.mu.Unlock()
		if ns, ok := s.finish(f); ok {
			s.totals.ValuationsCompleted++
			s.totals.ValuationNS += ns
			s.totals.Evaluations += uint64(evaluations)
		}
	}
}

// BeginImplication observes one implication wrapper, not each recursive decision.
// Time is exclusive process-wide wall-state: nested phases keep their own time;
// overlapping calls do not represent CPU time or independent per-goroutine work.
// Started counts accepted entries; finished counts first callbacks accepted while
// the session is open, including panic unwinds. Close freezes both without
// manufacturing finishes; their difference is neither depth nor proof failure.
func BeginImplication() func() {
	_, finish := BeginClassifiedImplication(ObligationUnspecified)
	return finish
}

// BeginClassifiedImplication has the same wrapper boundary and completion
// semantics as BeginImplication. The optional handle observes only coordinator
// stages; it must not be placed in proof state or passed to BDD workers.
func BeginClassifiedImplication(class ObligationClass) (*ImplicationObservation, func()) {
	s, f := begin(implication)
	if s == nil {
		return nil, noImplication
	}
	s.totals.ImplicationsStarted++
	observation := s.beginImplicationDetail(f, class)
	s.mu.Unlock()
	return observation, func() {
		s.mu.Lock()
		defer s.mu.Unlock()
		if _, ok := s.finish(f); ok {
			s.totals.ImplicationsFinished++
		}
	}
}

// ObligationClass describes the semantic caller, never terms or source text.
// Values are part of implication_detail v1 and must not be reordered.
type ObligationClass uint8

const (
	ObligationUnspecified ObligationClass = iota
	ObligationLoopInvariant
	ObligationCouplingHeader
	ObligationCouplingPreservation
	ObligationLoopContinue
	ObligationLoopReach
	ObligationTrapDomain
	ObligationLoopEntryMemory
	ObligationLoopIterationEffect
	ObligationLoopResult
	ObligationLoopExitEffect
	ObligationStraightWrite
	obligationClassCount
)

// ImplicationStage partitions the existing wrapper's exclusive wall time.
// Values describe explicit coordinator boundaries, not every operation of that
// kind. In particular, StageBDDJoined ends only after the joined call returns.
type ImplicationStage uint8

const (
	StageOther ImplicationStage = iota
	StageDAGAdmission
	StageCanonicalPass
	StageRecursiveScheduling
	StageBDDJoined
	StageStandalonePruning
	implicationStageCount
)

const (
	implicationSlots = 8
	implicationStack = 64
	implicationEventCap uint64 = 4_194_304
	implicationExtensionBytes = 2048
)

type stageVector [implicationStageCount]uint64

// ImplicationObservation is immutable after publication. The session pointer,
// fixed slot, and never-repeated nonzero epoch identify exactly one wrapper.
// Retirement visibility is atomic; all other detail state uses Session.mu.
type ImplicationObservation struct {
	session *Session
	epoch uint64
	slot uint8
}

// ImplicationToken is a value token for one accepted LIFO stage push. Its zero
// value and repeated End calls are harmless. It allocates no per-stage object.
type ImplicationToken struct {
	owner *ImplicationObservation
	serial uint64
	depth uint8
}

type implicationStageFrame struct {
	stage ImplicationStage
	since time.Time
	serial uint64
}

type implicationSlot struct {
	published atomic.Uint64
	epoch uint64
	owner *scope
	frames [implicationStack]implicationStageFrame
	depth uint8
	ns stageVector
	otherSince time.Time
	complete bool
	retired bool
}

type implicationClassRow struct {
	Started uint64 `json:"started"`
	Finished uint64 `json:"finished"`
	NS stageVector `json:"ns"`
}

type implicationCandidate struct {
	key [2]uint64
	valid bool
	complete bool
	started uint64
	finished uint64
	ns stageVector
	classes [obligationClassCount]implicationClassRow
}

type implicationDetailState struct {
	enabled atomic.Bool
	slots [implicationSlots]implicationSlot
	candidate implicationCandidate
	processNS stageVector
	entries stageVector
	nextID uint64
	nextEpoch uint64
	events uint64
	dropped uint64
	anomalies uint64
	unattributed uint64
	seen bool
	complete bool
	limited bool
	saturated bool
	contextLost bool
	retired bool
	// A snapshot can discover overflow in its uncharged interval. These fixed
	// fields preserve that interval's stage while atomically retiring hooks,
	// without making the snapshot mutate any accumulated time counter.
	pendingOwner *scope
	pendingStage ImplicationStage
	pendingUnattributed bool
	pendingSince time.Time
}

type implicationDominantRecord struct {
	Class ObligationClass `json:"class"`
	implicationClassRow
}

type implicationCandidateRecord struct {
	Key [2]uint64 `json:"key"`
	DetailComplete bool `json:"detail_complete"`
	Started uint64 `json:"started"`
	Finished uint64 `json:"finished"`
	NS stageVector `json:"ns"`
	Dominant implicationDominantRecord `json:"dominant"`
}

type implicationActiveRecord struct {
	ID uint64 `json:"id"`
	Class ObligationClass `json:"class"`
	Stage ImplicationStage `json:"stage"`
	StageScopeAgeNS uint64 `json:"stage_scope_age_ns"`
	NS stageVector `json:"ns"`
	DetailComplete bool `json:"detail_complete"`
}

type implicationDetailRecord struct {
	Version int `json:"v"`
	Coverage int `json:"coverage"`
	ProcessNS stageVector `json:"process_ns"`
	ProcessStageEntries stageVector `json:"process_stage_entries"`
	ProcessDetailComplete bool `json:"process_detail_complete"`
	Candidate *implicationCandidateRecord `json:"candidate,omitempty"`
	Active *implicationActiveRecord `json:"active,omitempty"`
	DetailEvents uint64 `json:"detail_events"`
	DroppedEvents uint64 `json:"dropped_events"`
	OwnershipAnomalies uint64 `json:"ownership_anomalies"`
	UnattributedNS uint64 `json:"unattributed_ns"`
	Limited bool `json:"limited"`
	CounterSaturated bool `json:"counter_saturated"`
	ContextLost bool `json:"context_lost"`
}

func implicationKey(c context) [2]uint64 {
	return [2]uint64{c.FunctionOrdinal, c.CandidateOrdinal}
}

// detailSlot is used only with the session mutex held. A retired slot can keep
// its owner's partial vector until the original wrapper callback frees it.
func (s *Session) detailSlot(f *scope) *implicationSlot {
	o := &f.observation
	if o.session != s || o.epoch == 0 || int(o.slot) >= len(s.detail.slots) {
		return nil
	}
	slot := &s.detail.slots[o.slot]
	if slot.owner != f || slot.epoch != o.epoch {
		return nil
	}
	return slot
}

func (slot *implicationSlot) stage() (ImplicationStage, time.Time) {
	if slot.depth == 0 || slot.retired {
		return StageOther, slot.otherSince
	}
	f := slot.frames[slot.depth-1]
	return f.stage, f.since
}

func saturatedAdd(dst *uint64, n uint64) bool {
	if ^uint64(0)-*dst < n {
		*dst = ^uint64(0)
		return true
	}
	*dst += n
	return false
}

func (s *Session) incompleteImplicationDetail() {
	s.detail.complete = false
	if s.detail.candidate.valid {
		s.detail.candidate.complete = false
	}
}

func (s *Session) saturateImplicationDetail() {
	s.detail.saturated = true
	s.detail.limited = true
	s.incompleteImplicationDetail()
}

func (s *Session) addDetail(dst *uint64, n uint64) {
	if saturatedAdd(dst, n) {
		s.saturateImplicationDetail()
	}
}

// Refusal counters deliberately count only the locked path. After an atomic
// retirement, ignored Push/End calls neither lock nor clock nor increment them.
func (s *Session) refuseImplicationDetail(limited, anomaly bool) {
	s.incompleteImplicationDetail()
	s.detail.limited = s.detail.limited || limited
	s.addDetail(&s.detail.dropped, 1)
	if anomaly {
		s.addDetail(&s.detail.anomalies, 1)
	}
}

func (s *Session) retireImplicationSlot(slot *implicationSlot, now time.Time) {
	slot.complete = false
	slot.retired = true
	slot.depth = 0
	slot.otherSince = now
	slot.published.Store(0)
}

// The caller charges the process-current interval before retirement. This
// function never advances a proof scope, manufactures a finish, or writes.
func (s *Session) retireImplicationDetail(now time.Time, limited bool) {
	s.detail.limited = s.detail.limited || limited
	if s.detail.retired {
		return
	}
	s.detail.retired = true
	for i := range s.detail.slots {
		slot := &s.detail.slots[i]
		if slot.owner != nil {
			s.incompleteImplicationDetail()
			s.retireImplicationSlot(slot, now)
		}
	}
	if limited {
		s.incompleteImplicationDetail()
	}
	s.detail.enabled.Store(false)
}

// Close freezes the original cutoff stage as well as its vector and age. Token
// publication is retired, but the frozen stack is retained for the close row.
func (s *Session) freezeImplicationDetail() {
	s.detail.retired = true
	for i := range s.detail.slots {
		slot := &s.detail.slots[i]
		if slot.owner != nil {
			s.incompleteImplicationDetail()
			slot.complete = false
			slot.published.Store(0)
		}
	}
	s.detail.enabled.Store(false)
}

func (s *Session) supersedeImplicationDetail(now time.Time) {
	for i := range s.detail.slots {
		slot := &s.detail.slots[i]
		if slot.owner != nil {
			s.refuseImplicationDetail(false, true)
			s.retireImplicationSlot(slot, now)
			// Superseded scopes cannot be restored by the existing root rules.
			slot.owner = nil
		}
	}
	s.detail.candidate = implicationCandidate{}
	if s.detail.saturated {
		s.retireImplicationDetail(now, true)
	}
}

func (s *Session) resetImplicationCandidate(c context) {
	key := implicationKey(c)
	if key[1] == 0 {
		// The old ordinal is left to its original semantics, but detailed keys
		// may never present a wrapped ordinal as a plausible fresh identity.
		s.saturateImplicationDetail()
		s.retireImplicationDetail(s.current.started, true)
	}
	s.detail.candidate = implicationCandidate{
		key: key, valid: key[1] != 0,
		complete: !s.detail.retired && !s.detail.saturated,
	}
}

func (s *Session) candidateFor(f *scope) *implicationCandidate {
	c := &s.detail.candidate
	if !c.valid {
		return nil
	}
	if c.key != implicationKey(f.context) {
		s.detail.contextLost = true
		s.incompleteImplicationDetail()
		return nil
	}
	return c
}

func (s *Session) beginImplicationDetail(f *scope, class ObligationClass) *ImplicationObservation {
	s.detail.seen = true
	if class >= obligationClassCount {
		class = ObligationUnspecified
	}
	f.wrapperClass = class
	if s.detail.nextID == ^uint64(0) {
		s.saturateImplicationDetail()
	} else {
		s.detail.nextID++
		f.wrapperID = s.detail.nextID
	}
	if c := s.candidateFor(f); c != nil {
		s.addDetail(&c.started, 1)
		s.addDetail(&c.classes[class].Started, 1)
	}
	if class == ObligationUnspecified {
		// Compatibility is supported, but it cannot certify class coverage.
		s.refuseImplicationDetail(false, false)
	}
	if s.detail.saturated {
		s.retireImplicationDetail(f.started, true)
	}
	if !s.detail.enabled.Load() {
		s.refuseImplicationDetail(true, false)
		return nil
	}
	for i := range s.detail.slots {
		slot := &s.detail.slots[i]
		if slot.owner != nil {
			continue
		}
		if s.detail.nextEpoch == ^uint64(0) {
			s.saturateImplicationDetail()
			s.retireImplicationDetail(f.started, true)
			return nil
		}
		s.detail.nextEpoch++
		slot.epoch = s.detail.nextEpoch
		slot.owner, slot.depth, slot.ns = f, 0, stageVector{}
		slot.otherSince = f.started
		slot.complete, slot.retired = class != ObligationUnspecified, false
		f.observation = ImplicationObservation{session: s, epoch: slot.epoch, slot: uint8(i)}
		slot.published.Store(slot.epoch)
		return &f.observation
	}
	s.refuseImplicationDetail(true, false)
	if s.detail.saturated {
		s.retireImplicationDetail(f.started, true)
	}
	return nil
}

func (s *Session) finishImplicationDetail(f *scope, now time.Time) {
	if c := s.candidateFor(f); c != nil {
		s.addDetail(&c.finished, 1)
		s.addDetail(&c.classes[f.wrapperClass].Finished, 1)
	}
	if slot := s.detailSlot(f); slot != nil {
		if slot.depth != 0 {
			s.refuseImplicationDetail(false, true)
		}
		slot.published.Store(0)
		slot.owner = nil
		slot.depth = 0
	}
	if s.detail.saturated {
		// A suspended wrapper can finish while another stage is current.
		// Charge that actual current owner at the same cutoff before global
		// retirement discards its stack. charge performs no new clock read.
		s.charge(now)
		s.retireImplicationDetail(now, true)
	}
}

func (s *Session) chargeImplicationDetail(f *scope, ns uint64) {
	stage := StageOther
	slot := s.detailSlot(f)
	if slot != nil {
		stage, _ = slot.stage()
	}
	s.chargeImplicationStage(f, stage, ns, slot == nil || slot.retired)
}

func (s *Session) chargeImplicationStage(f *scope, stage ImplicationStage, ns uint64, unattributed bool) {
	if slot := s.detailSlot(f); slot != nil {
		s.addDetail(&slot.ns[stage], ns)
	}
	s.addDetail(&s.detail.processNS[stage], ns)
	if unattributed {
		s.addDetail(&s.detail.unattributed, ns)
	}
	if c := s.candidateFor(f); c != nil {
		s.addDetail(&c.ns[stage], ns)
		s.addDetail(&c.classes[f.wrapperClass].NS[stage], ns)
	}
}

// liveFast reads only immutable identity and dedicated atomics. In particular,
// a retired handle does not consult mutable owner, stack, or accounting state.
func (o *ImplicationObservation) liveFast() bool {
	return o != nil && o.session != nil && o.epoch != 0 &&
		int(o.slot) < len(o.session.detail.slots) &&
		o.session.detail.enabled.Load() &&
		o.session.detail.slots[o.slot].published.Load() == o.epoch
}

// Push opens a nested coordinator stage. Child recursive decisions explicitly
// push StageOther so their work does not remain in the parent's scheduling time.
func (o *ImplicationObservation) Push(stage ImplicationStage) ImplicationToken {
	if !o.liveFast() {
		return ImplicationToken{}
	}
	s := o.session
	s.mu.Lock()
	defer s.mu.Unlock()
	return o.pushLocked(stage)
}

// pushLocked repeats the fast check after taking the state lock. Keeping the
// locked half separate also permits a finite barrier control of an epoch change
// between the two checks, without a production callback or test hook.
func (o *ImplicationObservation) pushLocked(stage ImplicationStage) ImplicationToken {
	s := o.session
	if !o.liveFast() || s.closed {
		return ImplicationToken{}
	}
	slot := &s.detail.slots[o.slot]
	f := slot.owner
	if f == nil || f.ended || f.generation != s.generation || s.current != f {
		now := s.cfg.now()
		s.charge(now)
		s.refuseImplicationDetail(false, true)
		s.retireImplicationSlot(slot, now)
		if s.detail.saturated {
			s.retireImplicationDetail(now, true)
		}
		return ImplicationToken{}
	}
	now := s.cfg.now()
	s.charge(now)
	if !o.liveFast() {
		return ImplicationToken{}
	}
	cap := s.cfg.detailEventCap
	if cap == 0 {
		cap = implicationEventCap
	}
	if s.detail.events >= cap {
		s.refuseImplicationDetail(true, false)
		s.retireImplicationDetail(now, true)
		return ImplicationToken{}
	}
	if stage >= implicationStageCount || int(slot.depth) == len(slot.frames) {
		s.refuseImplicationDetail(stage < implicationStageCount, stage >= implicationStageCount)
		s.retireImplicationSlot(slot, now)
		if s.detail.saturated {
			s.retireImplicationDetail(now, true)
		}
		return ImplicationToken{}
	}
	s.addDetail(&s.detail.events, 1)
	s.addDetail(&s.detail.entries[stage], 1)
	if s.detail.saturated {
		s.retireImplicationDetail(now, true)
		return ImplicationToken{}
	}
	slot.frames[slot.depth] = implicationStageFrame{stage: stage, since: now, serial: s.detail.events}
	slot.depth++
	return ImplicationToken{owner: o, serial: s.detail.events, depth: slot.depth}
}

// End restores only this token's unfinished parent stage. A duplicate token can
// never pop a later stage that happens to reuse the same stack depth.
func (t ImplicationToken) End() {
	if !t.owner.liveFast() {
		return
	}
	s := t.owner.session
	s.mu.Lock()
	defer s.mu.Unlock()
	t.endLocked()
}

func (t ImplicationToken) endLocked() {
	o := t.owner
	s := o.session
	if !o.liveFast() || s.closed {
		return
	}
	slot := &s.detail.slots[o.slot]
	if t.depth == 0 || t.depth > slot.depth || slot.frames[t.depth-1].serial != t.serial {
		return // Already popped, including after reuse of a stack depth.
	}
	now := s.cfg.now()
	s.charge(now)
	if !o.liveFast() {
		return
	}
	f := slot.owner
	if f == nil || f.ended || f.generation != s.generation || s.current != f || t.depth != slot.depth {
		s.refuseImplicationDetail(false, true)
		s.retireImplicationSlot(slot, now)
		if s.detail.saturated {
			s.retireImplicationDetail(now, true)
		}
		return
	}
	slot.depth--
}

// snapshotImplicationDetail adds the open interval to copies only. Numerical
// overflow in a projection retires detail immediately. A single fixed pending
// interval preserves the cutoff stage until the next ordinary phase charge;
// snapshots never consume events or advance accumulated time/activeSince.
func (s *Session) snapshotImplicationDetail(display context, now time.Time) *implicationDetailRecord {
	if !s.detail.seen {
		return nil
	}
	d := &s.detail
	r := &implicationDetailRecord{
		Version: 1, Coverage: 1, ProcessNS: d.processNS, ProcessStageEntries: d.entries,
		ProcessDetailComplete: d.complete, DetailEvents: d.events, DroppedEvents: d.dropped,
		OwnershipAnomalies: d.anomalies, UnattributedNS: d.unattributed,
		Limited: d.limited, CounterSaturated: d.saturated, ContextLost: d.contextLost,
	}
	c := d.candidate // Fixed twelve-row copy; no unbounded history.
	showCandidate := c.valid && c.key == implicationKey(display)
	if c.valid && !showCandidate {
		d.contextLost = true
		s.incompleteImplicationDetail()
		r.ContextLost = true
		r.ProcessDetailComplete = false
	}
	var wrapper *scope
	for f := s.current; f != nil; f = f.parent {
		if f.kind == implication && !f.ended {
			wrapper = f
			break
		}
	}
	if wrapper != nil {
		r.Active = &implicationActiveRecord{ID: wrapper.wrapperID, Class: wrapper.wrapperClass}
		if slot := s.detailSlot(wrapper); slot != nil {
			stage, since := slot.stage()
			r.Active.Stage, r.Active.StageScopeAgeNS = stage, elapsed(since, now)
			r.Active.NS, r.Active.DetailComplete = slot.ns, slot.complete
		}
	}
	projectionSaturated := false
	add := func(dst *uint64, n uint64) {
		if saturatedAdd(dst, n) {
			projectionSaturated = true
		}
	}
	if f := s.current; !s.closed && f != nil && f.phase == implication {
		ns := elapsed(f.activeSince, now)
		if ^uint64(0)-s.totals.PhaseNS.Implication < ns {
			projectionSaturated = true
		}
		stage := StageOther
		slot := s.detailSlot(f)
		if slot != nil {
			stage, _ = slot.stage()
		}
		project := func(stage ImplicationStage, ns uint64, unattributed bool) {
			add(&r.ProcessNS[stage], ns)
			if unattributed {
				add(&r.UnattributedNS, ns)
			}
			if r.Active != nil {
				add(&r.Active.NS[stage], ns)
			}
			if showCandidate && c.key == implicationKey(f.context) {
				add(&c.ns[stage], ns)
				add(&c.classes[f.wrapperClass].NS[stage], ns)
			}
		}
		if d.pendingOwner == f {
			before := elapsed(f.activeSince, d.pendingSince)
			if before > ns {
				before = ns
			}
			project(d.pendingStage, before, d.pendingUnattributed)
			project(StageOther, ns-before, true)
		} else {
			project(stage, ns, slot == nil || slot.retired)
		}
	}
	if showCandidate {
		dominant := ObligationUnspecified
		var dominantNS uint64
		for class := ObligationUnspecified; class < obligationClassCount; class++ {
			var total uint64
			for _, ns := range c.classes[class].NS {
				add(&total, ns)
			}
			if total > dominantNS {
				dominant, dominantNS = class, total
			}
		}
		r.Candidate = &implicationCandidateRecord{
			Key: c.key, DetailComplete: c.complete, Started: c.started, Finished: c.finished,
			NS: c.ns, Dominant: implicationDominantRecord{Class: dominant, implicationClassRow: c.classes[dominant]},
		}
	}
	if projectionSaturated {
		s.saturateImplicationDetail()
		if d.enabled.Load() {
			if f := s.current; !s.closed && f != nil && f.phase == implication {
				d.pendingOwner, d.pendingStage, d.pendingSince = f, StageOther, now
				slot := s.detailSlot(f)
				d.pendingUnattributed = slot == nil || slot.retired
				if slot != nil {
					d.pendingStage, _ = slot.stage()
				}
			}
			s.retireImplicationDetail(now, true)
		}
		r.ProcessDetailComplete, r.CounterSaturated, r.Limited = false, true, true
		if r.Candidate != nil {
			r.Candidate.DetailComplete = false
		}
		if r.Active != nil {
			r.Active.DetailComplete = false
			if wrapper != nil {
				if slot := s.detailSlot(wrapper); slot != nil {
					r.Active.Stage, r.Active.StageScopeAgeNS = StageOther, elapsed(slot.otherSince, now)
				}
			}
		}
	}
	return r
}
