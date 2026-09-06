package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func TestEmptyADTAnalysisHasNoCounterexample(t *testing.T) {
	tc := patternAnalysisChecker()
	expr := &ast.MatchExpression{}
	analysis := tc.analyzeMatch(expr, &ADTType{Name: "Void"})
	if !analysis.Reliable {
		t.Fatal("empty ADT coverage should be reliable")
	}
	if len(analysis.Missing) != 0 {
		t.Fatalf("empty semantic case space has counterexamples: %#v", analysis.Missing)
	}
}
