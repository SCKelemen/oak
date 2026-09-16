package prove

// Compatibility surface and word-protocol encoder for the LRAT certificate
// rung. The acceptance kernel lives in internal/lrat so lower compiler layers
// can depend on it without importing prove and its compiler dependency graph.

import (
	"fmt"
	"strconv"
	"strings"

	lrat "github.com/SCKelemen/oak/internal/lrat"
)

const lratLimit = lrat.Limit

// LRATResult counts what an accepted certificate did.
type LRATResult struct {
	Additions int
	Deletions int
}

type lratClause = lrat.Clause

// ParseDIMACS reads a formula: the variable count and its clauses in order,
// clause 1 first, as LRAT numbers them.
func ParseDIMACS(text string) (int, []lratClause, error) {
	return lrat.ParseDIMACS(text)
}

// CheckLRAT checks a RUP-only LRAT certificate against the exact formula
// supplied by its caller.
func CheckLRAT(formula, certificate string) (LRATResult, error) {
	result, err := lrat.Check(formula, certificate)
	return LRATResult(result), err
}

// CheckLRATWords checks the checker word protocol against its embedded
// formula. Exact-formula consumers should use CheckLRAT instead.
func CheckLRATWords(words []uint32) (LRATResult, error) {
	result, err := lrat.CheckWords(words)
	return LRATResult(result), err
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
const LRATMagic = lrat.Magic

const maxLRATWord = uint64(^uint32(0))
const maxLRATLiteralVariable = uint64(1) << 31

func lratMagnitude(value int) uint64 {
	if value >= 0 {
		return uint64(value)
	}
	return uint64(-(value + 1)) + 1
}

func lratUint32(name string, value uint64) (uint32, error) {
	if value > maxLRATWord {
		return 0, fmt.Errorf("%s %d does not fit the LRAT word protocol", name, value)
	}
	return uint32(value), nil
}

func lratAdd(name string, total, increment uint64) (uint64, error) {
	if total > maxLRATWord || increment > maxLRATWord-total {
		return 0, fmt.Errorf("%s exceeds the LRAT word protocol", name)
	}
	return total + increment, nil
}

func encodeLRATLiteral(literal int, variables uint64) (uint32, error) {
	variable := lratMagnitude(literal)
	if literal == 0 || variable > variables {
		return 0, fmt.Errorf("literal %d names no declared variable", literal)
	}
	if variable > maxLRATLiteralVariable {
		return 0, fmt.Errorf("literal %d does not fit the LRAT word protocol", literal)
	}
	word := 2 * (variable - 1)
	if literal > 0 {
		word++
	}
	return uint32(word), nil
}

type lratEncodedStep struct {
	id   uint32
	refs []uint32
}

func remapLRATClauseIDs(initial int, steps []LRATStep) ([]lratEncodedStep, uint32, error) {
	encoded := make([]lratEncodedStep, len(steps))
	encodedLast := uint32(initial)
	originalLast := initial
	liveAdded := map[int]uint32{}
	deletedInitial := map[int]bool{}
	resolve := func(original int) (uint32, bool) {
		switch {
		case original <= 0:
			return 0, false
		case original <= initial:
			if deletedInitial[original] {
				return 0, false
			}
			return uint32(original), true
		default:
			id, ok := liveAdded[original]
			return id, ok
		}
	}
	for i, step := range steps {
		if step.Delete {
			if step.ID < originalLast {
				return nil, 0, fmt.Errorf("certificate step %d: deletion id %d is before %d", i+1, step.ID, originalLast)
			}
			encoded[i].id = encodedLast
			if encoded[i].id == 0 {
				encoded[i].id = 1
			}
			encoded[i].refs = make([]uint32, len(step.IDs))
			for j, original := range step.IDs {
				id, ok := resolve(original)
				if !ok {
					return nil, 0, fmt.Errorf("certificate step %d: deletion clause %d is not live", i+1, original)
				}
				encoded[i].refs[j] = id
				if original <= initial {
					deletedInitial[original] = true
				} else {
					delete(liveAdded, original)
				}
			}
			continue
		}
		if step.ID <= originalLast {
			return nil, 0, fmt.Errorf("certificate step %d: addition id %d does not increase past %d", i+1, step.ID, originalLast)
		}
		encoded[i].refs = make([]uint32, len(step.Hints))
		for j, original := range step.Hints {
			id, ok := resolve(original)
			if !ok {
				return nil, 0, fmt.Errorf("certificate step %d: hint %d names no live clause", i+1, original)
			}
			encoded[i].refs[j] = id
		}
		next, err := lratUint32("dense clause id", uint64(encodedLast)+1)
		if err != nil {
			return nil, 0, err
		}
		encoded[i].id = next
		encodedLast = next
		originalLast = step.ID
		liveAdded[step.ID] = next
	}
	return encoded, encodedLast, nil
}

type lratWordShape struct {
	variables    uint32
	clauses      uint32
	literalWords uint32
	stepWords    uint32
	maxID        uint32
	storeWords   uint32
	totalWords   int
}

func preflightLRATWords(variables int, clauses []lratClause, steps []LRATStep) (lratWordShape, []lratEncodedStep, error) {
	var shape lratWordShape
	var err error
	shape.variables, err = lratUint32("variable count", uint64(variables))
	if err != nil {
		return shape, nil, err
	}
	shape.clauses, err = lratUint32("clause count", uint64(len(clauses)))
	if err != nil {
		return shape, nil, err
	}
	literalWords, storeWords := uint64(0), uint64(0)
	for _, clause := range clauses {
		count, err := lratUint32("clause literal count", uint64(len(clause)))
		if err != nil {
			return shape, nil, err
		}
		literalWords, err = lratAdd("initial clause words", literalWords, 1+uint64(count))
		if err != nil {
			return shape, nil, err
		}
		storeWords, err = lratAdd("literal store words", storeWords, uint64(count))
		if err != nil {
			return shape, nil, err
		}
		for _, literal := range clause {
			if _, err := encodeLRATLiteral(literal, uint64(variables)); err != nil {
				return shape, nil, err
			}
		}
	}
	encodedSteps, maxID, err := remapLRATClauseIDs(len(clauses), steps)
	if err != nil {
		return shape, nil, err
	}
	stepWords := uint64(0)
	for _, step := range steps {
		if step.Delete {
			count, err := lratUint32("deletion count", uint64(len(step.IDs)))
			if err != nil {
				return shape, nil, err
			}
			stepWords, err = lratAdd("certificate step words", stepWords, 3+uint64(count))
			if err != nil {
				return shape, nil, err
			}
			continue
		}
		literalCount, err := lratUint32("addition literal count", uint64(len(step.Lits)))
		if err != nil {
			return shape, nil, err
		}
		hintCount, err := lratUint32("addition hint count", uint64(len(step.Hints)))
		if err != nil {
			return shape, nil, err
		}
		stepWords, err = lratAdd("certificate step words", stepWords, 4+uint64(literalCount)+uint64(hintCount))
		if err != nil {
			return shape, nil, err
		}
		storeWords, err = lratAdd("literal store words", storeWords, uint64(literalCount))
		if err != nil {
			return shape, nil, err
		}
		for _, literal := range step.Lits {
			if _, err := encodeLRATLiteral(literal, uint64(variables)); err != nil {
				return shape, nil, err
			}
		}
	}
	shape.literalWords = uint32(literalWords)
	shape.stepWords = uint32(stepWords)
	shape.maxID = maxID
	shape.storeWords = uint32(storeWords)
	total := uint64(8) + literalWords + stepWords
	maxInt := uint64(^uint(0) >> 1)
	if total > maxInt {
		return shape, nil, fmt.Errorf("encoded LRAT record has %d words, which does not fit a host slice", total)
	}
	shape.totalWords = int(total)
	return shape, encodedSteps, nil
}

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
	shape, encodedSteps, err := preflightLRATWords(variables, clauses, steps)
	if err != nil {
		return nil, err
	}
	words := make([]uint32, 8, shape.totalWords)
	for _, clause := range clauses {
		words = append(words, uint32(len(clause)))
		for _, literal := range clause {
			w, err := encodeLRATLiteral(literal, uint64(variables))
			if err != nil {
				return nil, err
			}
			words = append(words, w)
		}
	}
	for i, step := range steps {
		encoded := encodedSteps[i]
		if step.Delete {
			words = append(words, 1, encoded.id, uint32(len(encoded.refs)))
			for _, id := range encoded.refs {
				words = append(words, uint32(id))
			}
			continue
		}
		words = append(words, 0, encoded.id, uint32(len(step.Lits)))
		for _, literal := range step.Lits {
			w, err := encodeLRATLiteral(literal, uint64(variables))
			if err != nil {
				return nil, err
			}
			words = append(words, w)
		}
		words = append(words, uint32(len(encoded.refs)))
		for _, hint := range encoded.refs {
			words = append(words, uint32(hint))
		}
	}
	words[0] = LRATMagic
	words[1] = shape.variables
	words[2] = shape.clauses
	words[3] = shape.literalWords
	words[4] = shape.stepWords
	words[5] = shape.maxID
	words[6] = shape.storeWords
	return words, nil
}
