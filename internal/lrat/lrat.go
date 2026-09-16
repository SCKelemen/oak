// Package lrat checks RUP-only LRAT certificates. It is a dependency-leaf
// acceptance kernel: formula construction, proof search, Oak, and compiler
// packages deliberately live above it.
package lrat

import (
	"fmt"
	"strconv"
	"strings"
)

// Limit bounds the text one certificate or formula may be.
const Limit = 1 << 30

// Result counts what an accepted certificate did.
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
func ParseDIMACS(text string) (int, []Clause, error) {
	if len(text) > Limit {
		return 0, nil, fmt.Errorf("formula text exceeds %d bytes", Limit)
	}
	variables, declared := 0, -1
	var clauses []Clause
	var current Clause
	for lineNumber, line := range strings.Split(text, "\n") {
		words := strings.Fields(line)
		if len(words) == 0 || words[0] == "c" {
			continue
		}
		if words[0] == "p" {
			if declared >= 0 || len(words) != 4 || words[1] != "cnf" {
				return 0, nil, fmt.Errorf("line %d: malformed DIMACS header", lineNumber+1)
			}
			n, err1 := strconv.Atoi(words[2])
			m, err2 := strconv.Atoi(words[3])
			if err1 != nil || err2 != nil || n < 0 || m < 0 {
				return 0, nil, fmt.Errorf("line %d: malformed DIMACS header", lineNumber+1)
			}
			variables, declared = n, m
			continue
		}
		if declared < 0 {
			return 0, nil, fmt.Errorf("line %d: clauses before the header", lineNumber+1)
		}
		for _, word := range words {
			lit, err := strconv.Atoi(word)
			if err != nil {
				return 0, nil, fmt.Errorf("line %d: %q is not a literal", lineNumber+1, word)
			}
			if lit == 0 {
				clauses = append(clauses, current)
				current = nil
				continue
			}
			if !validLiteral(lit, variables) {
				return 0, nil, fmt.Errorf("line %d: literal %d names no declared variable", lineNumber+1, lit)
			}
			current = append(current, lit)
		}
	}
	if len(current) != 0 {
		return 0, nil, fmt.Errorf("the last clause is not terminated")
	}
	if len(clauses) != declared {
		return 0, nil, fmt.Errorf("the header declares %d clauses, the text has %d", declared, len(clauses))
	}
	return variables, clauses, nil
}

// scanner walks a certificate's bytes line by line without allocating per
// token: a wide obligation can produce a certificate over a hundred megabytes.
type scanner struct {
	text string
	at   int
	line int
}

func (sc *scanner) nextLine() bool {
	if sc.at >= len(sc.text) {
		return false
	}
	sc.line++
	return true
}

func (sc *scanner) token() (string, bool) {
	for sc.at < len(sc.text) && (sc.text[sc.at] == ' ' || sc.text[sc.at] == '\t' || sc.text[sc.at] == '\r') {
		sc.at++
	}
	if sc.at >= len(sc.text) || sc.text[sc.at] == '\n' {
		if sc.at < len(sc.text) {
			sc.at++
		}
		return "", false
	}
	start := sc.at
	for sc.at < len(sc.text) && sc.text[sc.at] != ' ' && sc.text[sc.at] != '\t' && sc.text[sc.at] != '\r' && sc.text[sc.at] != '\n' {
		sc.at++
	}
	return sc.text[start:sc.at], true
}

func (sc *scanner) skipLine() {
	for sc.at < len(sc.text) && sc.text[sc.at] != '\n' {
		sc.at++
	}
	if sc.at < len(sc.text) {
		sc.at++
	}
}

// assignment is the assumed and propagated literals of one RUP step. A stamp
// per literal makes a new step cost no clearing.
type assignment struct {
	stamps []uint32
	gen    uint32
}

func (a *assignment) grow(variable int) bool {
	maxInt := int(^uint(0) >> 1)
	if variable < 0 || variable > (maxInt-2)/2 {
		return false
	}
	needed := 2*variable + 2
	if needed > len(a.stamps) {
		a.stamps = append(a.stamps, make([]uint32, needed-len(a.stamps))...)
	}
	return true
}

func (a *assignment) next() {
	a.gen++
	if a.gen == 0 {
		for i := range a.stamps {
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

func (a *assignment) holds(lit int) bool { return a.stamps[literalIndex(lit)] == a.gen }
func (a *assignment) set(lit int)        { a.stamps[literalIndex(lit)] = a.gen }

// Large declared domains use compact indices for variables that actually
// occur. Ordinary generated formulas stay on the direct dense-stamp path.
const denseVariableLimit = 1 << 20

type literalDomain struct {
	declared uint64
	compact  map[uint64]int
	assigned assignment
}

func useDenseLiteralDomain(declared, inputEvidence uint64) bool {
	maxInt := int(^uint(0) >> 1)
	return declared <= uint64((maxInt-2)/2) && (declared <= denseVariableLimit || declared <= inputEvidence)
}

func newLiteralDomain(declared, inputEvidence uint64) *literalDomain {
	domain := &literalDomain{declared: declared}
	if useDenseLiteralDomain(declared, inputEvidence) {
		domain.assigned.stamps = make([]uint32, 2*int(declared)+2)
	} else {
		domain.compact = map[uint64]int{}
		domain.assigned.stamps = make([]uint32, 2)
	}
	return domain
}

func (d *literalDomain) variable(original uint64) (int, bool) {
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
	d.compact[original] = variable
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
	clauses []Clause
	alive   []bool
	sparse  map[uint64]Clause
}

func (db *database) get(id uint64) (Clause, bool) {
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
	if id < uint64(len(db.alive)) {
		db.alive[int(id)] = true
		db.clauses[int(id)] = clause
		return
	}
	if id == uint64(len(db.alive)) {
		db.alive = append(db.alive, false)
		db.clauses = append(db.clauses, nil)
		db.alive[int(id)] = true
		db.clauses[int(id)] = clause
		return
	}
	if db.sparse == nil {
		db.sparse = map[uint64]Clause{}
	}
	db.sparse[id] = clause
}

func (db *database) drop(id uint64) {
	if id < uint64(len(db.alive)) {
		db.alive[int(id)] = false
		db.clauses[int(id)] = nil
		return
	}
	delete(db.sparse, id)
}

// rup checks one addition: assuming every literal of the clause false, each
// hint in order must be a unit or the final conflict.
func rup(db *database, clause Clause, hints []int64, assigned *assignment) error {
	assigned.next()
	for _, lit := range clause {
		if assigned.holds(lit) {
			return nil
		}
		assigned.set(-lit)
	}
	for i, id := range hints {
		if id <= 0 {
			return fmt.Errorf("hint %d is not a RUP hint (RAT steps are not spoken)", id)
		}
		hinted, alive := db.get(uint64(id))
		if !alive {
			return fmt.Errorf("hint %d names no live clause", id)
		}
		remaining, unit := 0, 0
		for _, lit := range hinted {
			if assigned.holds(lit) {
				return fmt.Errorf("hint %d is already satisfied", id)
			}
			if !assigned.holds(-lit) && lit != unit {
				remaining++
				unit = lit
			}
		}
		switch remaining {
		case 0:
			if i != len(hints)-1 {
				return fmt.Errorf("hint %d is the conflict but %d hints follow it", id, len(hints)-1-i)
			}
			return nil
		case 1:
			assigned.set(unit)
		default:
			return fmt.Errorf("hint %d is neither unit nor the conflict", id)
		}
	}
	return fmt.Errorf("the hints reach no conflict")
}

// Check checks a certificate against a formula: every addition is a RUP step
// over the live clauses, every deletion names live clauses, ids increase, and
// the empty clause is derived.
func Check(formula, certificate string) (Result, error) {
	var result Result
	if len(certificate) > Limit {
		return result, fmt.Errorf("certificate text exceeds %d bytes", Limit)
	}
	variables, clauses, err := ParseDIMACS(formula)
	if err != nil {
		return result, err
	}
	literalEvidence := uint64(0)
	for _, clause := range clauses {
		literalEvidence += uint64(len(clause))
	}
	domain := newLiteralDomain(uint64(variables), literalEvidence)
	db := &database{clauses: make([]Clause, 1, len(clauses)+1), alive: make([]bool, 1, len(clauses)+1)}
	empty := false
	for i, source := range clauses {
		clause := make(Clause, len(source))
		for j, lit := range source {
			decoded, ok := domain.text(lit)
			if !ok {
				return result, fmt.Errorf("literal %d names no declared variable", lit)
			}
			clause[j] = decoded
		}
		db.put(uint64(i+1), clause)
		if len(source) == 0 {
			empty = true
		}
	}
	last := uint64(len(clauses))
	sc := &scanner{text: certificate}
	var numbers []int
	var hints []int64
	for sc.nextLine() {
		first, ok := sc.token()
		if !ok || first == "c" {
			sc.skipLine()
			continue
		}
		fail := func(format string, args ...interface{}) (Result, error) {
			return result, fmt.Errorf("certificate line %d: %s", sc.line, fmt.Sprintf(format, args...))
		}
		parsedID, err := strconv.Atoi(first)
		if err != nil || parsedID <= 0 {
			return fail("%q is not a step id", first)
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
				n, err := strconv.Atoi(word)
				if err != nil {
					return fail("%q is not a clause id", word)
				}
				numbers = append(numbers, n)
			}
			if len(numbers) == 0 || numbers[len(numbers)-1] != 0 {
				return fail("a deletion carries the last id and ends in 0")
			}
			for _, n := range numbers[:len(numbers)-1] {
				if n <= 0 {
					return fail("%q is not a clause id", strconv.Itoa(n))
				}
				clauseID := uint64(n)
				if _, alive := db.get(clauseID); !alive {
					return fail("deleting clause %d, which is not live", n)
				}
				db.drop(clauseID)
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
			n, err := strconv.Atoi(word)
			if err != nil {
				return fail("%q is not an integer", word)
			}
			if n == 0 {
				if zeroCount < 2 {
					zeros[zeroCount] = len(numbers)
				}
				zeroCount++
			}
			numbers = append(numbers, n)
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
		clause := make(Clause, zeros[0])
		for i, lit := range numbers[:zeros[0]] {
			decoded, ok := domain.text(lit)
			if !ok {
				return fail("literal %d names no declared variable", lit)
			}
			clause[i] = decoded
		}
		hints = hints[:0]
		for _, hint := range numbers[zeros[0]+1 : len(numbers)-1] {
			hints = append(hints, int64(hint))
		}
		if err := rup(db, clause, hints, &domain.assigned); err != nil {
			return fail("%v", err)
		}
		db.put(id, clause)
		last = id
		result.Additions++
		if len(clause) == 0 {
			empty = true
		}
	}
	if !empty {
		return result, fmt.Errorf("the certificate never derives the empty clause")
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
