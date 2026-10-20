package lrat

import "fmt"

// CheckWordsAgainst checks an untrusted record against an independently
// supplied DIMACS obligation. It compares the numbered initial clauses directly,
// without calling a serializer. Order and duplicate literals are significant.
// Allocation hints are not formula identity. A nil error is the only acceptance
// signal; counters returned with an error are not evidence.
func CheckWordsAgainst(formula string, words []uint32) (Result, error) {
	variables, clauses, err := ParseDIMACS(formula)
	if err != nil {
		return Result{}, err
	}
	mismatch := func() (Result, error) {
		return Result{}, fmt.Errorf("the certificate record does not match the expected formula")
	}
	if len(words) < 8 || words[0] != Magic || uint64(variables) != uint64(words[1]) || uint64(len(clauses)) != uint64(words[2]) {
		return mismatch()
	}
	end, ok := boundedEnd(8, words[3], len(words))
	if !ok {
		return mismatch()
	}
	at := 8
	for _, clause := range clauses {
		if at >= end || uint64(len(clause)) != uint64(words[at]) {
			return mismatch()
		}
		at++
		next, ok := boundedEnd(at, words[at-1], end)
		if !ok {
			return mismatch()
		}
		for i, literal := range clause {
			magnitude := literalMagnitude(literal)
			if magnitude > uint64(1)<<31 {
				return mismatch()
			}
			encoded := 2 * (magnitude - 1)
			if literal > 0 {
				encoded++
			}
			if uint64(words[at+i]) != encoded {
				return mismatch()
			}
		}
		at = next
	}
	if at != end {
		return mismatch()
	}
	return CheckWords(words)
}

// WordsMatchFormula compares a proof-free formula record to a certificate
// record. This only checks identity and framing; it does not validate literals,
// clauses or RUP steps. Hints at words 5..7 are deliberately not identity.
func WordsMatchFormula(formula, record []uint32) bool {
	if len(formula) < 8 || len(record) < 8 || formula[0] != Magic || record[0] != Magic {
		return false
	}
	if formula[4] != 0 || uint64(formula[3]) != uint64(len(formula)-8) {
		return false
	}
	if uint64(record[3]) > uint64(len(record)-8) || uint64(record[4]) != uint64(len(record)-8)-uint64(record[3]) {
		return false
	}
	if formula[1] != record[1] || formula[2] != record[2] || formula[3] != record[3] {
		return false
	}
	for i, word := range formula[8:] {
		if record[8+i] != word {
			return false
		}
	}
	return true
}
