package lrat

import (
	"context"
	"errors"
	"fmt"
	"strconv"
	"unicode/utf8"
)

// Limits are per-call diagnostic budgets. Zero disables an individual limit.
// Work charges each byte scanned or converted, each explicit element visit,
// each assignment/database/domain operation, and allocation initialization/copy.
// Storage charges cumulative reserved machine-word slots, including replaced
// arrays: one per scalar, three per slice header, eight per compact-map entry,
// twelve per sparse-clause entry, and ceil(bytes/word) for byte buffers.
// Map/runtime overhead and caller-owned text are not a heap/RSS limit. Fixed
// stack state and the bounded LimitError itself are outside storage accounting.
// Count charges each parsed formula literal/clause and proof step/body integer.
// Deletions never refund any budget. Cancellation is polled at every charged
// checker operation, and before/after admitted bulk allocations and copies;
// runtime allocation, map operations and GC are not interruptible.
type Limits struct {
	MaxWork             uint64
	MaxStorage          uint64
	MaxFormulaBytes     uint64
	MaxCertificateBytes uint64
	MaxCount            uint64
}

var ErrLimit = errors.New("LRAT resource limit")

// LimitError is an incomplete check, never a logical rejection or acceptance.
// Resource is work, storage, text or count; Phase identifies the stop site.
type LimitError struct {
	Resource  string
	Phase     string
	Used      uint64
	Requested uint64
	Limit     uint64
}

func (e *LimitError) Error() string {
	return fmt.Sprintf("LRAT %s limit in %s: used %d, requested %d, limit %d", e.Resource, e.Phase, e.Used, e.Requested, e.Limit)
}
func (e *LimitError) Unwrap() error { return ErrLimit }

type meter struct {
	ctx                  context.Context
	limits               Limits
	work, storage, count uint64
	err                  error
	// A call-local deterministic checkpoint hook, used only by package tests.
	checkpoint func(string)
}

func (m *meter) poll(phase string) bool {
	if m == nil {
		return true
	}
	if m.err != nil {
		return false
	}
	if m.checkpoint != nil {
		m.checkpoint(phase)
	}
	if err := m.ctx.Err(); err != nil {
		m.err = err
		return false
	}
	return true
}
func (m *meter) charge(resource, phase string, used *uint64, amount, limit uint64) bool {
	if !m.poll(phase) {
		return false
	}
	if amount > ^uint64(0)-*used || (limit != 0 && (*used > limit || amount > limit-*used)) {
		m.err = &LimitError{resource, phase, *used, amount, limit}
		return false
	}
	*used += amount
	return true
}
func (m *meter) visit(phase string, n uint64) bool {
	return m == nil || m.charge("work", phase, &m.work, n, m.limits.MaxWork)
}
func (m *meter) reserve(phase string, n uint64) bool {
	return m == nil || m.charge("storage", phase, &m.storage, n, m.limits.MaxStorage)
}
func (m *meter) item(phase string) bool {
	return m == nil || m.charge("count", phase, &m.count, 1, m.limits.MaxCount)
}
func (m *meter) text(phase string, size int, limit uint64) bool {
	if !m.poll(phase) {
		return false
	}
	if limit != 0 && uint64(size) > limit {
		m.err = &LimitError{"text", phase, 0, uint64(size), limit}
		return false
	}
	return true
}
func (m *meter) error() error {
	if m == nil {
		return nil
	}
	return m.err
}

// CheckWithLimits checks the same relation as Check. A non-nil context is
// required. It starts no goroutines; any non-nil error means incomplete or
// rejected. Callers must also check session cancellation before publishing a
// verdict. Check and CheckWords do not acquire these additional budgets.
func CheckWithLimits(ctx context.Context, formula, certificate string, limits Limits) (Result, error) {
	if ctx == nil {
		return Result{}, errors.New("LRAT context must not be nil")
	}
	return check(formula, certificate, &meter{ctx: ctx, limits: limits})
}

// grow makes capacity explicit so the entire new backing array is reserved
// before allocation. Each scalar consumes one logical slot regardless of its
// machine representation. Growth arithmetic cannot wrap an int or a charge.
func grow[T any](s []T, needed int, slots uint64, m *meter, phase string) ([]T, bool) {
	if needed < 0 || slots == 0 {
		if m != nil {
			m.err = &LimitError{"storage", phase, m.storage, ^uint64(0), m.limits.MaxStorage}
		}
		return s, false
	}
	if needed <= cap(s) {
		return s, m.poll(phase)
	}
	capacity := cap(s)
	if capacity == 0 {
		capacity = 1
	}
	maxInt := int(^uint(0) >> 1)
	for capacity < needed {
		if !m.visit("growth-capacity", 1) {
			return s, false
		}
		if capacity > maxInt/2 {
			capacity = needed
			break
		}
		capacity *= 2
	}
	if uint64(capacity) > ^uint64(0)/slots {
		if m != nil {
			m.err = &LimitError{"storage", phase, m.storage, ^uint64(0), m.limits.MaxStorage}
		}
		return s, false
	}
	if !m.reserve(phase, uint64(capacity)*slots) || !m.visit("allocation-initialize", uint64(capacity)) {
		return s, false
	}
	replacement := make([]T, len(s), capacity)
	if !m.poll("allocation-finished") || !m.visit("allocation-copy", uint64(len(s))) {
		return s, false
	}
	copy(replacement, s)
	if !m.poll("copy-finished") {
		return s, false
	}
	return replacement, true
}
func appendMetered[T any](s []T, value T, slots uint64, m *meter, phase string) ([]T, bool) {
	if !m.visit("append-element", 1) {
		return s, false
	}
	if len(s) == int(^uint(0)>>1) {
		if m != nil {
			m.err = &LimitError{"storage", phase, m.storage, 1, m.limits.MaxStorage}
		}
		return s, false
	}
	grown, ok := grow(s, len(s)+1, slots, m, phase)
	if !ok {
		return s, false
	}
	return append(grown, value), true
}
func makeMetered[T any](n int, slots uint64, m *meter, phase string) ([]T, bool) {
	if n < 0 || slots == 0 || uint64(n) > ^uint64(0)/slots {
		if m != nil {
			m.err = &LimitError{"storage", phase, m.storage, ^uint64(0), m.limits.MaxStorage}
		}
		return nil, false
	}
	if !m.reserve(phase, uint64(n)*slots) || !m.visit("allocation-initialize", uint64(n)) {
		return nil, false
	}
	s := make([]T, n)
	return s, m.poll("allocation-finished")
}

// atoi implements Atoi's decimal syntax/range without giving an arbitrarily
// long zero-padded token to a noninterruptible conversion or error formatter.
func atoi(s string, m *meter) (int, bool) {
	if m == nil {
		n, err := strconv.Atoi(s)
		return n, err == nil
	}
	if len(s) == 0 {
		return 0, false
	}
	negative, start := false, 0
	if s[0] == '-' || s[0] == '+' {
		negative = s[0] == '-'
		start = 1
	}
	if !m.visit("integer", uint64(start)) || start == len(s) {
		return 0, false
	}
	bound := uint64(^uint(0) >> 1)
	if negative {
		bound++
	}
	var n uint64
	for i := start; i < len(s); i++ {
		if !m.visit("integer", 1) {
			return 0, false
		}
		b := s[i]
		if b < '0' || b > '9' {
			return 0, false
		}
		digit := uint64(b - '0')
		if n > bound/10 || (n == bound/10 && digit > bound%10) {
			return 0, false
		}
		n = n*10 + digit
	}
	if negative {
		return -int(n), true
	}
	return int(n), true
}

// quoted preserves fmt %q while limiting each library formatting call to one
// UTF-8 rune (at most four bytes). It reserves the conservative worst case
// first; construction, final string conversion and message copying are charged.
func quoted(s string, m *meter) string {
	if m == nil {
		return strconv.Quote(s)
	}
	worst := uint64(len(s))*10 + 2 // input is already bounded by the 1-GiB text cap
	if worst > uint64(int(^uint(0)>>1)) {
		m.err = &LimitError{"storage", "quote", m.storage, worst, m.limits.MaxStorage}
		return ""
	}
	slots := (worst + uint64(strconv.IntSize/8) - 1) / uint64(strconv.IntSize/8)
	if !m.reserve("quote", slots) || !m.visit("quote-initialize", worst) {
		return ""
	}
	b := make([]byte, 0, int(worst))
	if !m.poll("quote-allocated") {
		return ""
	}
	b = append(b, '"')
	for at := 0; at < len(s); {
		_, size := utf8.DecodeRuneInString(s[at:])
		if !m.visit("quote", uint64(size)) {
			return ""
		}
		// Quoting one encoded rune also preserves invalid UTF-8 byte escapes.
		if !m.reserve("quote-piece", 4) || !m.visit("quote-piece", 12) {
			return ""
		}
		var piece [12]byte // longest quoted single rune is "\\U00000000"
		q := strconv.AppendQuote(piece[:0], s[at:at+size])
		if !m.poll("quote-piece-formatted") {
			return ""
		}
		b = append(b, q[1:len(q)-1]...)
		at += size
	}
	b = append(b, '"')
	if !m.reserve("quote-string", uint64(len(b))) || !m.visit("quote-string", uint64(len(b))) {
		return ""
	}
	out := string(b)
	if !m.poll("quote-copied") {
		return ""
	}
	return out
}

// diagnostic reserves and charges the complete variable-sized string input
// before fmt copies it. Numeric arguments and constant formats have fixed size.
func diagnostic(m *meter, format string, args ...interface{}) error {
	if m != nil {
		size := uint64(len(format)) + 256
		for _, arg := range args {
			if s, ok := arg.(string); ok {
				size += uint64(len(s))
			}
		}
		if !m.reserve("diagnostic", size) || !m.visit("diagnostic", size) {
			return m.err
		}
	}
	err := fmt.Errorf(format, args...)
	if !m.poll("diagnostic-formatted") {
		return m.error()
	}
	return err
}

func integerString(n int, m *meter) string {
	if !m.reserve("integer-format", 4) || !m.visit("integer-format", 24) {
		return ""
	}
	s := strconv.Itoa(n)
	if !m.poll("integer-formatted") {
		return ""
	}
	return s
}
