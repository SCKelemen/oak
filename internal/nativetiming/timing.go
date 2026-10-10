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

const (
	interval       = 5 * time.Second
	maxRecords     = 1024
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
)

func (p phase) String() string {
	return [...]string{"idle", "search", "validation", "witnesses", "coupling", "valuation"}[p]
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
}

type phaseCosts struct {
	Search     uint64 `json:"search"`
	Validation uint64 `json:"validation"`
	Witnesses  uint64 `json:"witnesses"`
	Coupling   uint64 `json:"coupling"`
	Valuation  uint64 `json:"valuation"`
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
}

// Start enables observation for one explicit session. At most one session can
// be active. Records are JSON lines: start, status every five seconds, and close.
// The complete stream is limited to 1024 records and 4 MiB, reserving room for
// close even if the status limit is reached. Start surfaces initial write errors;
// subsequent write errors are returned by Close.
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
// nested validation/loop/valuation work again as search time.
func (s *Session) charge(now time.Time) {
	if s.current != nil {
		s.totals.PhaseNS.add(s.current.phase, elapsed(s.current.activeSince, now))
		s.current.activeSince = now
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
	return elapsed(f.started, now), true
}

var (
	noSearch     = func(int, int, int, bool) {}
	noValidation = func(int, bool) {}
	noLoops      = func() {}
	noValuation  = func(uint32) {}
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
