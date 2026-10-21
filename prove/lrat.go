package prove

// Compatibility surface. Acceptance and formula identity belong to the leaf
// kernel; serialization and proof search confer no acceptance authority.
import lrat "github.com/SCKelemen/oak/internal/lrat"

const lratLimit = lrat.Limit

// LRATResult counts steps; only a nil check error establishes acceptance.
type LRATResult struct {
	Additions int
	Deletions int
}
type lratClause = lrat.Clause

// ParseDIMACS parses numbered initial clauses in their original order.
func ParseDIMACS(text string) (int, []lratClause, error) { return lrat.ParseDIMACS(text) }

// CheckLRAT validates a RUP certificate against the supplied formula.
func CheckLRAT(formula, certificate string) (LRATResult, error) {
	result, err := lrat.Check(formula, certificate)
	return LRATResult(result), err
}

// CheckLRATWords proves only the embedded formula. Prefer CheckLRATWordsAgainst
// when the caller has an independently supplied obligation.
func CheckLRATWords(words []uint32) (LRATResult, error) {
	result, err := lrat.CheckWords(words)
	return LRATResult(result), err
}

// CheckLRATWordsAgainst binds the embedded formula to the independent caller
// obligation and checks its certificate without trusting the producer encoder.
func CheckLRATWordsAgainst(formula string, words []uint32) (LRATResult, error) {
	result, err := lrat.CheckWordsAgainst(formula, words)
	return LRATResult(result), err
}

// LRATWordsMatchFormula establishes identity and framing, not proof validity.
func LRATWordsMatchFormula(formula, record []uint32) bool {
	return lrat.WordsMatchFormula(formula, record)
}

// LRATMagic heads the Oak checker word protocol.
const LRATMagic = lrat.Magic
