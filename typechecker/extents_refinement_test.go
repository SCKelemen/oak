package typechecker

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// The extent decision against its Lean transliteration
// (spec/lean/Oak/ExtentsRefinement.lean, `indexUnder`): for each index
// site of the corpus the checker's live facts, the recognized shape, the
// container's static extent, and the decision are rendered as the
// `example … := by decide` line the Lean file states and Lean's kernel
// checks — so the Go decision and the Lean model cannot drift. Facts of
// kinds the model does not consult (an upper bound through a binding, a
// below fact, a quotient bound) are resolved before the decision and are
// not rendered.
func TestExtentDecisionsMatchLeanTransliteration(t *testing.T) {
	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "ExtentsRefinement.lean"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(lean)
	programs := []string{
		// A constant index under the static extent.
		"first: (v: [8]u8) -> u8 = v[3]\n",
		// A masked index: the mask below the extent.
		"pick: (v: [8]u8, i: u32) -> u8 = v[i & u32(7)]\n",
		// An offset index under a literal bound.
		"shifted: (v: [8]u8, i: u32) -> u8 = i < u32(6) ? v[i + u32(2)] | u8(0)\n",
		// A scaled index under a literal bound.
		"pair: (v: [8]u8, i: u32) -> u8 = i < u32(4) ? v[i * u32(2) + u32(1)] | u8(0)\n",
		// A span element under a proven minimum length and a literal bound.
		"at: (v: []u8, i: u32) -> u8 = len(v) >= u32(4) && i < u32(4) ? v[i] | u8(0)\n",
		// A literal bound too weak for the extent: not proven.
		"loose: (v: [8]u8, i: u32) -> u8 = i < u32(9) ? v[i] | u8(0)\n",
	}
	var rendered []string
	for _, src := range programs {
		tc := setupTypeChecker(src)
		tc.indexDecisionHook = func(facts []extentFact, indexExpr ast.Expression, name string, arr *ArrayType, proven bool) {
			shape, ok := renderShape(tc, indexExpr)
			if !ok {
				return
			}
			static := "none"
			if arr.Length >= 0 && !arr.IsSlice && !arr.IsSpan {
				static = fmt.Sprintf("(some %d)", arr.Length)
			}
			rendered = append(rendered, fmt.Sprintf("example : indexUnder %s %q %s %s = %v := by decide", renderFacts(facts), name, static, shape, proven))
		}
		program := parseProgram(src)
		tc.CheckProgram(program)
		if errs := tc.Errors(); len(errs) != 0 {
			t.Fatalf("%s: %v", strings.TrimSpace(src), errs)
		}
	}
	if len(rendered) < len(programs) {
		t.Fatalf("only %d of %d index sites rendered:\n%s", len(rendered), len(programs), strings.Join(rendered, "\n"))
	}
	var missing []string
	for _, line := range rendered {
		if !strings.Contains(text, line) {
			missing = append(missing, line)
		}
	}
	if len(missing) != 0 {
		t.Fatalf("%d decision(s) not stated in spec/lean/Oak/ExtentsRefinement.lean — update the Lean file or the discharge:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}

// renderFacts spells the live facts the Lean model consults, in order.
func renderFacts(facts []extentFact) string {
	var out []string
	for _, f := range facts {
		switch f.kind {
		case factMinLen:
			out = append(out, fmt.Sprintf("Fact.minLen %q %d", f.container, f.bound))
		case factIndexBound:
			out = append(out, fmt.Sprintf("Fact.indexBound %q %q %d", f.container, f.other, f.offset))
		case factSameLen:
			out = append(out, fmt.Sprintf("Fact.sameLen %q %q", f.container, f.other))
		case factIndexLit:
			out = append(out, fmt.Sprintf("Fact.indexLit %q %d", f.other, f.bound))
		case factLowerLit:
			out = append(out, fmt.Sprintf("Fact.lowerLit %q %d", f.other, f.bound))
		case factDivIndex:
			out = append(out, fmt.Sprintf("Fact.divIndex %q %q %d", f.container, f.other, f.bound))
		}
	}
	return "[" + strings.Join(out, ", ") + "]"
}

// renderShape reads the index as indexUnder does, recognizer by
// recognizer in its order; a refinement's runtime value and a mask's
// operand are irrelevant to the decision and rendered as 0.
func renderShape(tc *TypeChecker, index ast.Expression) (string, bool) {
	if _, bound, isRefined := tc.refinedBelow(index); isRefined {
		return fmt.Sprintf("(Shape.refined 0 %d)", bound), true
	}
	if mask, isMasked := maskedIndex(index); isMasked {
		return fmt.Sprintf("(Shape.masked 0 %d)", mask), true
	}
	if name, scale, offset, isScaled := scaledIndex(index); isScaled {
		return fmt.Sprintf("(Shape.scaled %q %d %d)", name, scale, offset), true
	}
	if n1, k1, n2, k2, c, isScaled2 := scaledIndex2(index); isScaled2 {
		return fmt.Sprintf("(Shape.scaled2 %q %d %q %d %d)", n1, k1, n2, k2, c), true
	}
	if name, k, isMinus := minusIndex(index); isMinus {
		return fmt.Sprintf("(Shape.minus %q %d)", name, k), true
	}
	if c, isConst := constantIndex(index); isConst && c >= 0 {
		return fmt.Sprintf("(Shape.const %d)", c), true
	}
	if name, offset, isOffset := offsetIndex(index); isOffset {
		return fmt.Sprintf("(Shape.offset %q %d)", name, offset), true
	}
	return "", false
}
