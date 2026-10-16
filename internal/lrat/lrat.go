// Package lrat checks RUP-only LRAT certificates. It is a dependency-leaf
// acceptance kernel: formula construction, proof search, Oak, and compiler
// packages deliberately live above it.
package lrat

import (
	"fmt"
	"unicode"
	"unicode/utf8"
)

// Limit bounds the text one certificate or formula may be.
const Limit = 1 << 30

// Result counts completed additions and deletions. A non-nil error never
// signifies acceptance, regardless of these diagnostic counts.
type Result struct {
	Additions int
	Deletions int
}

// Clause is a clause by its literals; a nil entry in the database is an
// absent or deleted clause.
type Clause []int

// literalMagnitude computes abs(lit) without negating MinInt.
func literalMagnitude(lit int) uint64 {
	if lit >= 0 {
		return uint64(lit)
	}
	return uint64(-(lit + 1)) + 1
}

func validLiteral(lit, variables int) bool {
	return lit != 0 && literalMagnitude(lit) <= uint64(variables)
}

// ParseDIMACS reads a formula: the variable count and its clauses in order,
// clause 1 first, as LRAT numbers them.
func ParseDIMACS(text string) (int, []Clause, error) { return parseDIMACS(text, nil) }

func parseDIMACS(text string, m *meter) (variables int, clauses []Clause, err error) {
	defer func() {
		if m.error() != nil {
			variables, clauses, err = 0, nil, m.error()
		}
	}()
	if len(text) > Limit {
		return 0, nil, diagnostic(m, "formula text exceeds %d bytes", Limit)
	}
	declared := -1
	var current Clause
	lineNumber := 0
	for at := 0; at <= len(text); {
		if !m.visit("formula-line", 1) {
			return 0, nil, m.error()
		}
		lineNumber++
		start := at
		for at < len(text) && text[at] != '\n' {
			if !m.visit("formula-scan", 1) {
				return 0, nil, m.error()
			}
			at++
		}
		line := text[start:at]
		if at < len(text) && !m.visit("formula-newline", 1) {
			return 0, nil, m.error()
		}
		at++ // includes the final empty line, matching strings.Split
		fieldAt := 0
		field := func() (string, bool) {
			for fieldAt < len(line) {
				r, n := utf8.DecodeRuneInString(line[fieldAt:])
				if !m.visit("formula-whitespace", uint64(n)) {
					return "", false
				}
				if !unicode.IsSpace(r) {
					break
				}
				fieldAt += n
			}
			begin := fieldAt
			for fieldAt < len(line) {
				r, n := utf8.DecodeRuneInString(line[fieldAt:])
				if !m.visit("formula-token", uint64(n)) {
					return "", false
				}
				if unicode.IsSpace(r) {
					break
				}
				fieldAt += n
			}
			return line[begin:fieldAt], fieldAt > begin
		}
		first, ok := field()
		if !ok || first == "c" {
			continue
		}
		if first == "p" {
			a, aok := field()
			b, bok := field()
			c, cok := field()
			_, extra := field()
			if declared >= 0 || !aok || !bok || !cok || extra || a != "cnf" {
				return 0, nil, diagnostic(m, "line %d: malformed DIMACS header", lineNumber)
			}
			n, nOK := atoi(b, m)
			count, countOK := atoi(c, m)
			if !nOK || !countOK || n < 0 || count < 0 {
				return 0, nil, diagnostic(m, "line %d: malformed DIMACS header", lineNumber)
			}
			variables, declared = n, count
			continue
		}
		if declared < 0 {
			return 0, nil, diagnostic(m, "line %d: clauses before the header", lineNumber)
		}
		word := first
		for {
			lit, ok := atoi(word, m)
			if !ok {
				return 0, nil, diagnostic(m, "line %d: %s is not a literal", lineNumber, quoted(word, m))
			}
			if lit == 0 {
				if !m.item("formula-clause") {
					return 0, nil, m.error()
				}
				clauses, ok = appendMetered(clauses, current, 3, m, "formula-clauses")
				if !ok {
					return 0, nil, m.error()
				}
				current = nil
			} else {
				if !validLiteral(lit, variables) {
					return 0, nil, diagnostic(m, "line %d: literal %d names no declared variable", lineNumber, lit)
				}
				if !m.item("formula-literal") {
					return 0, nil, m.error()
				}
				current, ok = appendMetered(current, lit, 1, m, "formula-literals")
				if !ok {
					return 0, nil, m.error()
				}
			}
			word, ok = field()
			if !ok {
				break
			}
		}
	}
	if len(current) != 0 {
		return 0, nil, diagnostic(m, "the last clause is not terminated")
	}
	if len(clauses) != declared {
		return 0, nil, diagnostic(m, "the header declares %d clauses, the text has %d", declared, len(clauses))
	}
	return variables, clauses, nil
}

// scanner walks a certificate's bytes line by line without allocating per
// token: a wide obligation can produce a certificate over a hundred megabytes.
type scanner struct {
	m    *meter
	text string
	at   int
	line int
}

func (sc *scanner) nextLine() bool {
	if !sc.m.visit("proof-line", 1) {
		return false
	}
	if sc.at >= len(sc.text) {
		return false
	}
	sc.line++
	return true
}

func (sc *scanner) token() (string, bool) {
	for sc.at < len(sc.text) && (sc.text[sc.at] == ' ' || sc.text[sc.at] == '\t' || sc.text[sc.at] == '\r') {
		if !sc.m.visit("proof-whitespace", 1) {
			return "", false
		}
		sc.at++
	}
	if sc.at >= len(sc.text) || sc.text[sc.at] == '\n' {
		if sc.at < len(sc.text) {
			if !sc.m.visit("proof-newline", 1) {
				return "", false
			}
			sc.at++
		}
		return "", false
	}
	start := sc.at
	for sc.at < len(sc.text) && sc.text[sc.at] != ' ' && sc.text[sc.at] != '\t' && sc.text[sc.at] != '\r' && sc.text[sc.at] != '\n' {
		if !sc.m.visit("proof-token", 1) {
			return "", false
		}
		sc.at++
	}
	return sc.text[start:sc.at], true
}

func (sc *scanner) skipLine() {
	for sc.at < len(sc.text) && sc.text[sc.at] != '\n' {
		if !sc.m.visit("proof-comment", 1) {
			return
		}
		sc.at++
	}
	if sc.at < len(sc.text) {
		if !sc.m.visit("proof-newline", 1) {
			return
		}
		sc.at++
	}
}

// assignment is the assumed and propagated literals of one RUP step. A stamp
// per literal makes a new step cost no clearing.
type assignment struct {
	m      *meter
	stamps []uint32
	gen    uint32
}

func (a *assignment) grow(variable int) bool {
	if !a.m.visit("assignment-grow", 1) {
		return false
	}
	maxInt := int(^uint(0) >> 1)
	if variable < 0 || variable > (maxInt-2)/2 {
		return false
	}
	needed := 2*variable + 2
	if needed > len(a.stamps) {
		grown, ok := grow(a.stamps, needed, 1, a.m, "assignment-growth")
		if !ok {
			return false
		}
		a.stamps = grown[:needed]
	}
	return true
}

func (a *assignment) next() {
	if !a.m.visit("assignment-next", 1) {
		return
	}
	a.gen++
	if a.gen == 0 {
		for i := range a.stamps {
			if !a.m.visit("assignment-reset", 1) {
				return
			}
			a.stamps[i] = 0
		}
		a.gen = 1
	}
}

func literalIndex(lit int) int {
	if lit > 0 {
		return 2 * lit
	}
	return 2*(-lit) + 1
}

func (a *assignment) holds(lit int) bool {
	return a.m.visit("assignment-read", 1) && a.stamps[literalIndex(lit)] == a.gen
}
func (a *assignment) set(lit int) {
	if a.m.visit("assignment-write", 1) {
		a.stamps[literalIndex(lit)] = a.gen
	}
}

// Large declared domains use compact indices for variables that actually
// occur. Ordinary generated formulas stay on the direct dense-stamp path.
const denseVariableLimit = 1 << 20

type literalDomain struct {
	m        *meter
	declared uint64
	compact  map[uint64]int
	assigned assignment
}

func useDenseLiteralDomain(declared, inputEvidence uint64) bool {
	maxInt := int(^uint(0) >> 1)
	return declared <= uint64((maxInt-2)/2) && (declared <= denseVariableLimit || declared <= inputEvidence)
}

func newLiteralDomain(declared, inputEvidence uint64) *literalDomain {
	return meteredLiteralDomain(declared, inputEvidence, nil)
}
func meteredLiteralDomain(declared, inputEvidence uint64, m *meter) *literalDomain {
	if !m.reserve("domain", 8) {
		return nil
	}
	domain := &literalDomain{declared: declared, m: m, assigned: assignment{m: m}}
	var ok bool
	if useDenseLiteralDomain(declared, inputEvidence) {
		domain.assigned.stamps, ok = makeMetered[uint32](2*int(declared)+2, 1, m, "assignment-initial")
	} else {
		if !m.reserve("domain-map", 8) || !m.poll("domain-map") {
			return nil
		}
		domain.compact = map[uint64]int{}
		domain.assigned.stamps, ok = makeMetered[uint32](2, 1, m, "assignment-initial")
	}
	if !ok {
		return nil
	}
	return domain
}

func (d *literalDomain) variable(original uint64) (int, bool) {
	if !d.m.visit("domain-variable", 1) {
		return 0, false
	}
	if original == 0 || original > d.declared {
		return 0, false
	}
	if d.compact == nil {
		return int(original), true
	}
	if variable, ok := d.compact[original]; ok {
		return variable, true
	}
	variable := len(d.compact) + 1
	if !d.assigned.grow(variable) {
		return 0, false
	}
	if !d.m.reserve("domain-entry", 8) || !d.m.visit("domain-insert", 1) {
		return 0, false
	}
	d.compact[original] = variable
	if !d.m.poll("domain-inserted") {
		return 0, false
	}
	return variable, true
}

func (d *literalDomain) text(lit int) (int, bool) {
	original := literalMagnitude(lit)
	variable, ok := d.variable(original)
	if !ok || lit == 0 {
		return 0, false
	}
	if lit < 0 {
		return -variable, true
	}
	return variable, true
}

func (d *literalDomain) word(word uint32) (int, bool) {
	original := uint64(word/2) + 1
	variable, ok := d.variable(original)
	if !ok {
		return 0, false
	}
	if word%2 == 0 {
		return -variable, true
	}
	return variable, true
}

type database struct {
	m       *meter
	clauses []Clause
	alive   []bool
	sparse  map[uint64]Clause
}

func (db *database) get(id uint64) (Clause, bool) {
	if !db.m.visit("database-get", 1) {
		return nil, false
	}
	if id < uint64(len(db.alive)) {
		if !db.alive[int(id)] {
			return nil, false
		}
		return db.clauses[int(id)], true
	}
	clause, ok := db.sparse[id]
	return clause, ok
}

func (db *database) put(id uint64, clause Clause) {
	if !db.m.visit("database-put", 1) {
		return
	}
	if id < uint64(len(db.alive)) {
		db.alive[int(id)] = true
		db.clauses[int(id)] = clause
		return
	}
	if id == uint64(len(db.alive)) {
		var ok bool
		db.alive, ok = appendMetered(db.alive, false, 1, db.m, "database-alive")
		if !ok {
			return
		}
		db.clauses, ok = appendMetered(db.clauses, Clause(nil), 3, db.m, "database-clauses")
		if !ok {
			return
		}
		db.alive[int(id)] = true
		db.clauses[int(id)] = clause
		return
	}
	if db.sparse == nil {
		if !db.m.reserve("database-map", 8) {
			return
		}
		db.sparse = map[uint64]Clause{}
	}
	if !db.m.reserve("database-entry", 12) {
		return
	}
	db.sparse[id] = clause
	db.m.poll("database-inserted")
}

func (db *database) drop(id uint64) {
	if !db.m.visit("database-drop", 1) {
		return
	}
	if id < uint64(len(db.alive)) {
		db.alive[int(id)] = false
		db.clauses[int(id)] = nil
		return
	}
	delete(db.sparse, id)
	db.m.poll("database-dropped")
}

// rup checks one addition: assuming every literal of the clause false, each
// hint in order must be a unit or the final conflict.
func rup(db *database, clause Clause, hints []int64, assigned *assignment) error {
	m := assigned.m
	assigned.next()
	if m.error() != nil {
		return m.error()
	}
	for _, lit := range clause {
		if !m.visit("rup-assumption", 1) {
			return m.error()
		}
		if assigned.holds(lit) {
			return nil
		}
		assigned.set(-lit)
	}
	for i, id := range hints {
		if !m.visit("rup-hint", 1) {
			return m.error()
		}
		if id <= 0 {
			return diagnostic(m, "hint %d is not a RUP hint (RAT steps are not spoken)", id)
		}
		hinted, alive := db.get(uint64(id))
		if !alive {
			return diagnostic(m, "hint %d names no live clause", id)
		}
		remaining, unit := 0, 0
		for _, lit := range hinted {
			if !m.visit("rup-literal", 1) {
				return m.error()
			}
			if assigned.holds(lit) {
				return diagnostic(m, "hint %d is already satisfied", id)
			}
			if !assigned.holds(-lit) && lit != unit {
				remaining++
				unit = lit
			}
		}
		switch remaining {
		case 0:
			if i != len(hints)-1 {
				return diagnostic(m, "hint %d is the conflict but %d hints follow it", id, len(hints)-1-i)
			}
			return nil
		case 1:
			assigned.set(unit)
		default:
			return diagnostic(m, "hint %d is neither unit nor the conflict", id)
		}
	}
	return diagnostic(m, "the hints reach no conflict")
}

// Check checks a certificate against a formula: every addition is a RUP step
// over the live clauses, every deletion names live clauses, ids increase, and
// the empty clause is derived.
func Check(formula, certificate string) (Result, error) { return check(formula, certificate, nil) }
func check(formula, certificate string, m *meter) (result Result, err error) {
	defer func() {
		if m.error() != nil {
			err = m.error()
		}
	}()
	if !m.poll("entry") {
		return result, m.error()
	}
	if m != nil && (!m.text("certificate-text", len(certificate), m.limits.MaxCertificateBytes) || !m.text("formula-text", len(formula), m.limits.MaxFormulaBytes)) {
		return result, m.error()
	}
	if len(certificate) > Limit {
		return result, diagnostic(m, "certificate text exceeds %d bytes", Limit)
	}
	variables, clauses, err := parseDIMACS(formula, m)
	if err != nil {
		return result, err
	}
	literalEvidence := uint64(0)
	for _, clause := range clauses {
		if !m.visit("formula-evidence", 1) {
			return result, m.error()
		}
		literalEvidence += uint64(len(clause))
	}
	domain := meteredLiteralDomain(uint64(variables), literalEvidence, m)
	if domain == nil {
		return result, m.error()
	}
	if !m.reserve("database", 8) {
		return result, m.error()
	}
	dc, ok := makeMetered[Clause](len(clauses)+1, 3, m, "database-initial-clauses")
	if !ok {
		return result, m.error()
	}
	da, ok := makeMetered[bool](len(clauses)+1, 1, m, "database-initial-alive")
	if !ok {
		return result, m.error()
	}
	db := &database{m: m, clauses: dc[:1], alive: da[:1]}
	empty := false
	for i, source := range clauses {
		if !m.visit("formula-copy-clause", 1) {
			return result, m.error()
		}
		clause, ok := makeMetered[int](len(source), 1, m, "formula-copy")
		if !ok {
			return result, m.error()
		}
		for j, lit := range source {
			if !m.visit("formula-copy-literal", 1) {
				return result, m.error()
			}
			decoded, ok := domain.text(lit)
			if !ok {
				return result, diagnostic(m, "literal %d names no declared variable", lit)
			}
			clause[j] = decoded
		}
		db.put(uint64(i+1), clause)
		if m.error() != nil {
			return result, m.error()
		}
		if len(source) == 0 {
			empty = true
		}
	}
	last := uint64(len(clauses))
	sc := &scanner{text: certificate, m: m}
	var numbers []int
	var hints []int64
	for sc.nextLine() {
		first, ok := sc.token()
		if !ok {
			// token already consumed the blank line's newline. Skipping
			// here would discard the next command as well.
			continue
		}
		if first == "c" {
			sc.skipLine()
			continue
		}
		fail := func(format string, args ...interface{}) (Result, error) {
			if !m.reserve("diagnostic-frame", 64) || !m.visit("diagnostic-frame", 64) {
				return result, m.error()
			}
			return result, diagnostic(m, "certificate line %d: "+format, append([]interface{}{sc.line}, args...)...)
		}
		parsedID, parsed := atoi(first, m)
		if !parsed || parsedID <= 0 {
			return fail("%s is not a step id", quoted(first, m))
		}
		if !m.item("proof-step") {
			return result, m.error()
		}
		id := uint64(parsedID)
		second, ok := sc.token()
		if !ok {
			return fail("a step needs an id, its body, and a terminating 0")
		}
		if second == "d" {
			if id < last {
				return fail("a deletion carries the last id and ends in 0")
			}
			numbers = numbers[:0]
			for {
				word, ok := sc.token()
				if !ok {
					break
				}
				n, parsed := atoi(word, m)
				if !parsed {
					return fail("%s is not a clause id", quoted(word, m))
				}
				if !m.item("proof-number") {
					return result, m.error()
				}
				numbers, ok = appendMetered(numbers, n, 1, m, "proof-numbers")
				if !ok {
					return result, m.error()
				}
			}
			if len(numbers) == 0 || numbers[len(numbers)-1] != 0 {
				return fail("a deletion carries the last id and ends in 0")
			}
			for _, n := range numbers[:len(numbers)-1] {
				if !m.visit("proof-deletion", 1) {
					return result, m.error()
				}
				if n <= 0 {
					return fail("%s is not a clause id", quoted(integerString(n, m), m))
				}
				clauseID := uint64(n)
				if _, alive := db.get(clauseID); !alive {
					return fail("deleting clause %d, which is not live", n)
				}
				db.drop(clauseID)
				if m.error() != nil {
					return result, m.error()
				}
				result.Deletions++
			}
			continue
		}
		if id <= last {
			return fail("id %d does not increase past %d", id, last)
		}
		numbers = numbers[:0]
		zeros := [2]int{-1, -1}
		zeroCount := 0
		word := second
		for {
			n, parsed := atoi(word, m)
			if !parsed {
				return fail("%s is not an integer", quoted(word, m))
			}
			if n == 0 {
				if zeroCount < 2 {
					zeros[zeroCount] = len(numbers)
				}
				zeroCount++
			}
			if !m.item("proof-number") {
				return result, m.error()
			}
			numbers, ok = appendMetered(numbers, n, 1, m, "proof-numbers")
			if !ok {
				return result, m.error()
			}
			word, ok = sc.token()
			if !ok {
				break
			}
		}
		if len(numbers) < 2 {
			return fail("a step needs an id, its body, and a terminating 0")
		}
		if zeroCount != 2 || zeros[1] != len(numbers)-1 {
			return fail("an addition is `id literals 0 hints 0`")
		}
		clause, ok := makeMetered[int](zeros[0], 1, m, "proof-clause")
		if !ok {
			return result, m.error()
		}
		for i, lit := range numbers[:zeros[0]] {
			if !m.visit("proof-literal", 1) {
				return result, m.error()
			}
			decoded, ok := domain.text(lit)
			if !ok {
				return fail("literal %d names no declared variable", lit)
			}
			clause[i] = decoded
		}
		hints = hints[:0]
		for _, hint := range numbers[zeros[0]+1 : len(numbers)-1] {
			hints, ok = appendMetered(hints, int64(hint), 1, m, "proof-hints")
			if !ok {
				return result, m.error()
			}
		}
		if err := rup(db, clause, hints, &domain.assigned); err != nil {
			if m.error() != nil {
				return result, m.error()
			}
			return fail("%v", err)
		}
		if !m.poll("addition-commit") {
			return result, m.error()
		}
		db.put(id, clause)
		if m.error() != nil {
			return result, m.error()
		}
		last = id
		result.Additions++
		if len(clause) == 0 {
			empty = true
		}
	}
	if !empty {
		return result, diagnostic(m, "the certificate never derives the empty clause")
	}
	if !m.poll("success") {
		return result, m.error()
	}
	return result, nil
}

// Magic heads the word encoding the checker written in Oak reads.
const Magic = 1280459348

func boundedEnd(at int, count uint32, limit int) (int, bool) {
	if at < 0 || at > limit || uint64(count) > uint64(limit-at) {
		return 0, false
	}
	return at + int(count), true
}

// CheckWords checks the checker word protocol against its embedded formula.
// It uses the same RUP relation as Check.
func CheckWords(words []uint32) (Result, error) {
	var result Result
	if len(words) < 8 || words[0] != Magic {
		return result, fmt.Errorf("the record does not start with the LRAT header")
	}
	literalEnd, ok := boundedEnd(8, words[3], len(words))
	if !ok {
		return result, fmt.Errorf("the record's clauses run past its end")
	}
	stepEnd, ok := boundedEnd(literalEnd, words[4], len(words))
	if !ok || stepEnd != len(words) {
		return result, fmt.Errorf("the record's step words do not match its length")
	}
	clauseCount := uint64(words[2])
	if clauseCount > uint64(literalEnd-8) {
		return result, fmt.Errorf("the record holds fewer clauses than its header declares")
	}
	domain := newLiteralDomain(uint64(words[1]), uint64(literalEnd-8))
	db := &database{clauses: make([]Clause, 1, int(clauseCount)+1), alive: make([]bool, 1, int(clauseCount)+1)}
	empty := false
	at := 8
	for c := uint64(0); c < clauseCount; c++ {
		if at >= literalEnd {
			return result, fmt.Errorf("the record holds fewer clauses than its header declares")
		}
		n := words[at]
		at++
		clauseEnd, ok := boundedEnd(at, n, literalEnd)
		if !ok {
			return result, fmt.Errorf("clause %d runs past the clause words", c+1)
		}
		clause := make(Clause, clauseEnd-at)
		for j, word := range words[at:clauseEnd] {
			literal, ok := domain.word(word)
			if !ok {
				return result, fmt.Errorf("clause %d: literal word %d names no declared variable", c+1, word)
			}
			clause[j] = literal
		}
		at = clauseEnd
		db.put(c+1, clause)
		if n == 0 {
			empty = true
		}
	}
	if at != literalEnd {
		return result, fmt.Errorf("the record's clause words outlive its declared clauses")
	}
	last := clauseCount
	var hints []int64
	step := 0
	for at < stepEnd {
		step++
		fail := func(format string, args ...interface{}) (Result, error) {
			return result, fmt.Errorf("certificate step %d: %s", step, fmt.Sprintf(format, args...))
		}
		if stepEnd-at < 3 {
			return fail("a step needs a kind, an id, and a count")
		}
		kind := words[at]
		id := uint64(words[at+1])
		count := words[at+2]
		at += 3
		if id == 0 {
			return fail("%d is not a step id", id)
		}
		switch kind {
		case 1:
			if id < last {
				return fail("a deletion carries the last id")
			}
			idsEnd, ok := boundedEnd(at, count, stepEnd)
			if !ok {
				return fail("the deletion's ids run past the record")
			}
			for _, word := range words[at:idsEnd] {
				clauseID := uint64(word)
				if _, alive := db.get(clauseID); clauseID == 0 || !alive {
					return fail("deleting clause %d, which is not live", clauseID)
				}
				db.drop(clauseID)
				result.Deletions++
			}
			at = idsEnd
		case 0:
			if id <= last {
				return fail("id %d does not increase past %d", id, last)
			}
			clauseEnd, ok := boundedEnd(at, count, stepEnd)
			if !ok || clauseEnd >= stepEnd {
				return fail("the addition's literals run past the record")
			}
			clause := make(Clause, clauseEnd-at)
			for j, word := range words[at:clauseEnd] {
				literal, ok := domain.word(word)
				if !ok {
					return fail("literal word %d names no declared variable", word)
				}
				clause[j] = literal
			}
			hintsStart := clauseEnd + 1
			hintsEnd, ok := boundedEnd(hintsStart, words[clauseEnd], stepEnd)
			if !ok {
				return fail("the addition's hints run past the record")
			}
			hints = hints[:0]
			for _, word := range words[hintsStart:hintsEnd] {
				hints = append(hints, int64(word))
			}
			if err := rup(db, clause, hints, &domain.assigned); err != nil {
				return fail("%v", err)
			}
			db.put(id, clause)
			last = id
			result.Additions++
			if count == 0 {
				empty = true
			}
			at = hintsEnd
		default:
			return fail("%d is neither an addition (0) nor a deletion (1)", kind)
		}
	}
	if !empty {
		return result, fmt.Errorf("the certificate never derives the empty clause")
	}
	return result, nil
}
