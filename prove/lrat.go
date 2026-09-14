package prove

// An LRAT certificate checker (docs/spec/125-verification.md §3, the
// certificate rung; Oak.RupCheck states its soundness). LRAT is the hinted
// clausal proof format: every added clause names, in order, the clauses
// whose unit propagation — under the added clause's negation — reaches a
// conflict, so checking is one linear pass per step and never a search.
// Deletions free clauses the proof no longer needs. RAT steps (a hint
// list with negative entries) are not spoken: the rung asks its solver for
// RUP-only proofs and refuses anything else. The checker written in Oak
// (prove/solver/lrat.oak) is its twin; a row is decided when both accept.

import (
	"fmt"
	"strconv"
	"strings"
)

// lratLimit bounds the text one certificate or formula may be.
const lratLimit = 1 << 30

// LRATResult counts what an accepted certificate did.
type LRATResult struct {
	Additions int
	Deletions int
}

// lratClause is a clause by its literals; a nil entry in the database is
// an absent or deleted clause.
type lratClause []int

// ParseDIMACS reads a formula: the variable count and its clauses in order,
// clause 1 first, as LRAT numbers them.
func ParseDIMACS(text string) (int, []lratClause, error) {
	if len(text) > lratLimit {
		return 0, nil, fmt.Errorf("formula text exceeds %d bytes", lratLimit)
	}
	variables, declared := 0, -1
	var clauses []lratClause
	var current lratClause
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
			if lit > variables || -lit > variables {
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

// lratScanner walks a certificate's bytes line by line without allocating
// per token: the certificate of a wide obligation runs to hundreds of
// thousands of lines and over a hundred megabytes, and splitting it into
// strings cost more than checking it.
type lratScanner struct {
	text string
	at   int
	line int // the current line, one-based
}

// nextLine positions the scanner on the next line; false at the end.
func (sc *lratScanner) nextLine() bool {
	if sc.at >= len(sc.text) {
		return false
	}
	sc.line++
	return true
}

// token returns the next space-separated token of the current line and
// whether there was one; the line's newline is consumed with its last
// token.
func (sc *lratScanner) token() (string, bool) {
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

// skipLine drops the rest of the current line.
func (sc *lratScanner) skipLine() {
	for sc.at < len(sc.text) && sc.text[sc.at] != '\n' {
		sc.at++
	}
	if sc.at < len(sc.text) {
		sc.at++
	}
}

// lratAssignment is the assumed and propagated literals of one RUP step:
// a stamp per literal, current when it equals the step's generation, so a
// step costs no clearing.
type lratAssignment struct {
	stamps []uint32
	gen    uint32
}

func (a *lratAssignment) next() {
	a.gen++
	if a.gen == 0 {
		for i := range a.stamps {
			a.stamps[i] = 0
		}
		a.gen = 1
	}
}

func lratIndex(lit int) int {
	if lit > 0 {
		return 2 * lit
	}
	return 2*(-lit) + 1
}

func (a *lratAssignment) holds(lit int) bool { return a.stamps[lratIndex(lit)] == a.gen }
func (a *lratAssignment) set(lit int)        { a.stamps[lratIndex(lit)] = a.gen }

// lratDatabase is the live clauses by id: ids increase, so a slice.
type lratDatabase struct {
	clauses []lratClause
	alive   []bool
}

func (db *lratDatabase) get(id int) (lratClause, bool) {
	if id < 0 || id >= len(db.alive) || !db.alive[id] {
		return nil, false
	}
	return db.clauses[id], true
}

func (db *lratDatabase) put(id int, clause lratClause) {
	for len(db.alive) <= id {
		db.alive = append(db.alive, false)
		db.clauses = append(db.clauses, nil)
	}
	db.alive[id] = true
	db.clauses[id] = clause
}

func (db *lratDatabase) drop(id int) {
	db.alive[id] = false
	db.clauses[id] = nil
}

// rup checks one addition: assuming every literal of the clause false,
// each hint in order must be a unit (assigning its remaining literal) or
// the conflict, and the last hint must be the conflict. A clause that
// contains a literal and its negation needs no hints.
func rup(db *lratDatabase, variables int, clause lratClause, hints []int, assigned *lratAssignment) error {
	assigned.next()
	for _, lit := range clause {
		if lit == 0 || lit > variables || -lit > variables {
			return fmt.Errorf("literal %d names no declared variable", lit)
		}
		if assigned.holds(lit) {
			return nil // tautology: l and ¬l both in the clause
		}
		assigned.set(-lit)
	}
	for i, id := range hints {
		if id <= 0 {
			return fmt.Errorf("hint %d is not a RUP hint (RAT steps are not spoken)", id)
		}
		hinted, alive := db.get(id)
		if !alive {
			return fmt.Errorf("hint %d names no live clause", id)
		}
		// A clause is a set: a literal repeated in the text counts once.
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

// CheckLRAT checks a certificate against a formula: every addition is a
// RUP step over the live clauses, every deletion names live clauses, ids
// increase, and the empty clause is derived. The first failing line is
// named. The clause and hint bounds are the parsed formula's.
func CheckLRAT(formula, certificate string) (LRATResult, error) {
	var result LRATResult
	if len(certificate) > lratLimit {
		return result, fmt.Errorf("certificate text exceeds %d bytes", lratLimit)
	}
	variables, clauses, err := ParseDIMACS(formula)
	if err != nil {
		return result, err
	}
	db := &lratDatabase{clauses: make([]lratClause, 0, len(clauses)+1), alive: make([]bool, 0, len(clauses)+1)}
	empty := false
	for i, clause := range clauses {
		db.put(i+1, clause)
		if len(clause) == 0 {
			empty = true
		}
	}
	last := len(clauses)
	assigned := &lratAssignment{stamps: make([]uint32, 2*variables+2)}
	sc := &lratScanner{text: certificate}
	var numbers []int
	for sc.nextLine() {
		first, ok := sc.token()
		if !ok || first == "c" {
			sc.skipLine()
			continue
		}
		fail := func(format string, args ...interface{}) (LRATResult, error) {
			return result, fmt.Errorf("certificate line %d: %s", sc.line, fmt.Sprintf(format, args...))
		}
		id, err := strconv.Atoi(first)
		if err != nil || id <= 0 {
			return fail("%q is not a step id", first)
		}
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
				if _, alive := db.get(n); !alive {
					return fail("deleting clause %d, which is not live", n)
				}
				db.drop(n)
				result.Deletions++
			}
			continue
		}
		if id <= last {
			return fail("id %d does not increase past %d", id, last)
		}
		// The rest of the line: `literals 0 hints 0`, the second token
		// already read.
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
		clause := make(lratClause, zeros[0])
		copy(clause, numbers[:zeros[0]])
		hints := numbers[zeros[0]+1 : len(numbers)-1]
		if err := rup(db, variables, clause, hints, assigned); err != nil {
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

// CheckLRATWords checks a certificate in the checkers' word protocol (the
// form the solver written in Oak records and prove/solver/lrat.oak reads;
// EncodeLRATWords writes it from text): the eight-word header, the clauses
// as `n, literals...` with literal words 2(v-1)+polarity, then steps
// `0, id, n, literals..., m, hints...` and `1, id, k, ids...`. The same
// RUP relation as CheckLRAT, over the same database and assignment.
func CheckLRATWords(words []uint32) (LRATResult, error) {
	var result LRATResult
	if len(words) < 8 || words[0] != LRATMagic {
		return result, fmt.Errorf("the record does not start with the LRAT header")
	}
	variables := int(words[1])
	clauseCount := int(words[2])
	literalWords := int(words[3])
	if 8+literalWords > len(words) {
		return result, fmt.Errorf("the record's clauses run past its end")
	}
	literal := func(w uint32) (int, error) {
		v := int(w/2) + 1
		if v > variables {
			return 0, fmt.Errorf("literal word %d names no declared variable", w)
		}
		if w%2 == 1 {
			return v, nil
		}
		return -v, nil
	}
	db := &lratDatabase{clauses: make([]lratClause, 0, clauseCount+1), alive: make([]bool, 0, clauseCount+1)}
	empty := false
	at := 8
	for c := 0; c < clauseCount; c++ {
		if at >= 8+literalWords {
			return result, fmt.Errorf("the record holds fewer clauses than its header declares")
		}
		n := int(words[at])
		at++
		if at+n > 8+literalWords {
			return result, fmt.Errorf("clause %d runs past the clause words", c+1)
		}
		clause := make(lratClause, n)
		for j := 0; j < n; j++ {
			l, err := literal(words[at+j])
			if err != nil {
				return result, fmt.Errorf("clause %d: %v", c+1, err)
			}
			clause[j] = l
		}
		at += n
		db.put(c+1, clause)
		if n == 0 {
			empty = true
		}
	}
	last := clauseCount
	assigned := &lratAssignment{stamps: make([]uint32, 2*variables+2)}
	var hints []int
	step := 0
	for at < len(words) {
		step++
		fail := func(format string, args ...interface{}) (LRATResult, error) {
			return result, fmt.Errorf("certificate step %d: %s", step, fmt.Sprintf(format, args...))
		}
		if at+3 > len(words) {
			return fail("a step needs a kind, an id, and a count")
		}
		kind, id, count := words[at], int(words[at+1]), int(words[at+2])
		at += 3
		if id <= 0 {
			return fail("%d is not a step id", id)
		}
		switch kind {
		case 1:
			if id < last {
				return fail("a deletion carries the last id")
			}
			if at+count > len(words) {
				return fail("the deletion's ids run past the record")
			}
			for _, w := range words[at : at+count] {
				n := int(w)
				if _, alive := db.get(n); n <= 0 || !alive {
					return fail("deleting clause %d, which is not live", n)
				}
				db.drop(n)
				result.Deletions++
			}
			at += count
		case 0:
			if id <= last {
				return fail("id %d does not increase past %d", id, last)
			}
			if at+count+1 > len(words) {
				return fail("the addition's literals run past the record")
			}
			clause := make(lratClause, count)
			for j := 0; j < count; j++ {
				l, err := literal(words[at+j])
				if err != nil {
					return fail("%v", err)
				}
				clause[j] = l
			}
			at += count
			m := int(words[at])
			at++
			if at+m > len(words) {
				return fail("the addition's hints run past the record")
			}
			hints = hints[:0]
			for _, w := range words[at : at+m] {
				hints = append(hints, int(w))
			}
			at += m
			if err := rup(db, variables, clause, hints, assigned); err != nil {
				return fail("%v", err)
			}
			db.put(id, clause)
			last = id
			result.Additions++
			if count == 0 {
				empty = true
			}
		default:
			return fail("%d is neither an addition (0) nor a deletion (1)", kind)
		}
	}
	if !empty {
		return result, fmt.Errorf("the certificate never derives the empty clause")
	}
	return result, nil
}

// LRATStep is one parsed certificate line: an addition of a clause with
// its hints, or a deletion of clause ids.
type LRATStep struct {
	Delete bool
	ID     int
	Lits   []int
	Hints  []int
	IDs    []int
}

// ParseLRAT reads a certificate's steps without checking them; a step with
// a non-positive hint (a RAT step) is refused here.
func ParseLRAT(certificate string) ([]LRATStep, error) {
	if len(certificate) > lratLimit {
		return nil, fmt.Errorf("certificate text exceeds %d bytes", lratLimit)
	}
	var steps []LRATStep
	for lineNumber, line := range strings.Split(certificate, "\n") {
		words := strings.Fields(line)
		if len(words) == 0 || words[0] == "c" {
			continue
		}
		fail := func(format string, args ...interface{}) ([]LRATStep, error) {
			return nil, fmt.Errorf("certificate line %d: %s", lineNumber+1, fmt.Sprintf(format, args...))
		}
		if len(words) < 3 {
			return fail("a step needs an id, its body, and a terminating 0")
		}
		id, err := strconv.Atoi(words[0])
		if err != nil || id <= 0 {
			return fail("%q is not a step id", words[0])
		}
		if words[1] == "d" {
			if words[len(words)-1] != "0" {
				return fail("a deletion ends in 0")
			}
			step := LRATStep{Delete: true, ID: id}
			for _, word := range words[2 : len(words)-1] {
				n, err := strconv.Atoi(word)
				if err != nil || n <= 0 {
					return fail("%q is not a clause id", word)
				}
				step.IDs = append(step.IDs, n)
			}
			steps = append(steps, step)
			continue
		}
		numbers := make([]int, 0, len(words)-1)
		zeros := []int{}
		for _, word := range words[1:] {
			n, err := strconv.Atoi(word)
			if err != nil {
				return fail("%q is not an integer", word)
			}
			if n == 0 {
				zeros = append(zeros, len(numbers))
			}
			numbers = append(numbers, n)
		}
		if len(zeros) != 2 || zeros[1] != len(numbers)-1 {
			return fail("an addition is `id literals 0 hints 0`")
		}
		step := LRATStep{ID: id, Lits: numbers[:zeros[0]], Hints: numbers[zeros[0]+1 : len(numbers)-1]}
		for _, hint := range step.Hints {
			if hint <= 0 {
				return fail("hint %d is not a RUP hint (RAT steps are not spoken)", hint)
			}
		}
		steps = append(steps, step)
	}
	return steps, nil
}

// LRATMagic heads the word encoding the checker written in Oak reads.
const LRATMagic = 1280459348

// EncodeLRATWords encodes a formula and certificate for the checker
// written in Oak (prove/solver/lrat.oak's word protocol): a header, the
// initial clauses, then the steps, literals as 2*(variable-1)+polarity.
func EncodeLRATWords(formula, certificate string) ([]uint32, error) {
	variables, clauses, err := ParseDIMACS(formula)
	if err != nil {
		return nil, err
	}
	steps, err := ParseLRAT(certificate)
	if err != nil {
		return nil, err
	}
	lit := func(l int) (uint32, error) {
		if l == 0 || l > variables || -l > variables {
			return 0, fmt.Errorf("literal %d names no declared variable", l)
		}
		if l > 0 {
			return uint32(2*(l-1) + 1), nil
		}
		return uint32(2 * (-l - 1)), nil
	}
	words := make([]uint32, 8)
	literalWords, storeWords, maxID := 0, 0, len(clauses)
	for _, clause := range clauses {
		words = append(words, uint32(len(clause)))
		for _, l := range clause {
			w, err := lit(l)
			if err != nil {
				return nil, err
			}
			words = append(words, w)
		}
		literalWords += 1 + len(clause)
		storeWords += len(clause)
	}
	stepStart := len(words)
	for _, step := range steps {
		if step.ID > maxID {
			maxID = step.ID
		}
		if step.Delete {
			words = append(words, 1, uint32(step.ID), uint32(len(step.IDs)))
			for _, id := range step.IDs {
				if id > maxID {
					maxID = id
				}
				words = append(words, uint32(id))
			}
			continue
		}
		words = append(words, 0, uint32(step.ID), uint32(len(step.Lits)))
		for _, l := range step.Lits {
			w, err := lit(l)
			if err != nil {
				return nil, err
			}
			words = append(words, w)
		}
		words = append(words, uint32(len(step.Hints)))
		for _, hint := range step.Hints {
			if hint > maxID {
				maxID = hint
			}
			words = append(words, uint32(hint))
		}
		storeWords += len(step.Lits)
	}
	words[0] = LRATMagic
	words[1] = uint32(variables)
	words[2] = uint32(len(clauses))
	words[3] = uint32(literalWords)
	words[4] = uint32(len(words) - stepStart)
	words[5] = uint32(maxID)
	words[6] = uint32(storeWords)
	return words, nil
}
