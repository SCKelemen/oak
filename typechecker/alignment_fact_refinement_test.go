package typechecker

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestAlignmentFactDecisions(t *testing.T) {
	for _, test := range []struct {
		input, want uint32
	}{
		{0, 0}, {1, 0}, {2, 2}, {64, 64}, {4096, 4096},
	} {
		if got := alignmentFact(test.input); got != test.want {
			t.Errorf("alignmentFact(%d) = %d, want %d", test.input, got, test.want)
		}
	}

	for _, test := range []struct {
		value, target uint32
		want          bool
	}{
		{0, 0, true},
		{64, 0, true},
		{4096, 64, true},
		{64, 4096, false},
		{0, 64, false},
		{64, 64, true},
	} {
		if got := alignmentFactFlows(test.value, test.target); got != test.want {
			t.Errorf("alignmentFactFlows(%d, %d) = %v, want %v", test.value, test.target, got, test.want)
		}
	}

	for _, test := range []struct {
		left, right, want uint32
	}{
		{4096, 64, 64},
		{64, 4096, 64},
		{4096, 0, 0},
		{0, 64, 0},
		{64, 64, 64},
	} {
		if got := joinAlignmentFacts(test.left, test.right); got != test.want {
			t.Errorf("joinAlignmentFacts(%d, %d) = %d, want %d", test.left, test.right, got, test.want)
		}
	}
}

// The alignment-fact decisions against their Lean transliteration. This is a
// bounded implementation pin: the live Go helpers render the exact executable
// examples checked in Oak.AlignmentFactRefinement, while the module's theorems
// prove those decisions sound for every canonical alignment fact.
func TestAlignmentFactDecisionsMatchLeanTransliteration(t *testing.T) {
	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "AlignmentFactRefinement.lean"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(lean)

	var rendered []string
	for _, input := range []uint32{0, 1, 2, 64, 4096} {
		rendered = append(rendered, fmt.Sprintf(
			"example : normalize %d = %d := by decide",
			input, alignmentFact(input),
		))
	}
	for _, pair := range [][2]uint32{{0, 0}, {4096, 64}, {64, 4096}, {64, 0}, {0, 64}, {64, 64}} {
		rendered = append(rendered, fmt.Sprintf(
			"example : flows %d %d = %v := by decide",
			pair[0], pair[1], alignmentFactFlows(pair[0], pair[1]),
		))
	}
	for _, pair := range [][2]uint32{{4096, 64}, {64, 4096}, {64, 64}, {4096, 0}, {0, 64}} {
		rendered = append(rendered, fmt.Sprintf(
			"example : join %d %d = %d := by decide",
			pair[0], pair[1], joinAlignmentFacts(pair[0], pair[1]),
		))
	}

	var missing []string
	for _, line := range rendered {
		if !strings.Contains(text, line) {
			missing = append(missing, line)
		}
	}
	if len(missing) != 0 {
		t.Fatalf("%d alignment decision(s) not stated in spec/lean/Oak/AlignmentFactRefinement.lean — update the Lean file or the implementation:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}

func TestAlignmentFactConsumersAgree(t *testing.T) {
	tc := setupTypeChecker("")
	element := &PrimitiveType{Name: "u8"}
	for _, test := range []struct {
		value, target uint32
		want          bool
	}{
		{0, 0, true},
		{64, 0, true},
		{4096, 64, true},
		{64, 4096, false},
		{0, 64, false},
	} {
		value := &ArrayType{ElementType: element, Length: -1, IsSpan: true, Align: test.value}
		target := &ArrayType{ElementType: element, Length: -1, IsSpan: true, Align: test.target}
		if got := value.alignedInto(target); got != test.want {
			t.Errorf("alignedInto(%d, %d) = %v, want %v", test.value, test.target, got, test.want)
		}
		if got := tc.alignmentAssignable(value, target); got != test.want {
			t.Errorf("alignmentAssignable(%d, %d) = %v, want %v", test.value, test.target, got, test.want)
		}
		if got := tc.representationPreservingAssignable(value, target); got != test.want {
			t.Errorf("representationPreservingAssignable(%d, %d) = %v, want %v", test.value, test.target, got, test.want)
		}
	}
}

func TestAlignmentFactValueFlowJoin(t *testing.T) {
	span := func(name string, align uint32) Type {
		return &ArrayType{ElementType: &PrimitiveType{Name: name}, Length: -1, IsSpan: true, Align: align}
	}
	for _, test := range []struct {
		name  string
		types []Type
		want  uint32
	}{
		{name: "strong then weak", types: []Type{span("u8", 4096), span("u8", 64)}, want: 64},
		{name: "weak then strong", types: []Type{span("u8", 64), span("u8", 4096)}, want: 64},
		{name: "plain alternative", types: []Type{span("u8", 4096), span("u8", 64), span("u8", 0)}, want: 0},
		{name: "never ignored", types: []Type{&NeverType{}, span("u8", 4096), span("u8", 64)}, want: 64},
		{name: "repeated", types: []Type{span("u8", 4096), span("u8", 4096)}, want: 4096},
	} {
		t.Run(test.name, func(t *testing.T) {
			got, ok := joinValueFlowTypes(test.types...).(*ArrayType)
			if !ok || got.Align != test.want {
				t.Fatalf("joinValueFlowTypes() = %T %v, want alignment %d", got, got, test.want)
			}
		})
	}

	span64 := span("u8", 64).(*ArrayType)
	view64 := *span64
	view64.IsSpan, view64.IsSlice = false, true
	length64 := *span64
	length64.Length = 4
	for _, test := range []struct {
		name        string
		left, right Type
	}{
		{name: "kind mismatch", left: span64, right: &view64},
		{name: "length mismatch", left: span64, right: &length64},
		{name: "element mismatch", left: span64, right: span("u16", 64)},
	} {
		t.Run(test.name, func(t *testing.T) {
			if _, narrowed := joinValueFlowTypes(test.left, test.right).(*ArrayType); narrowed {
				t.Fatal("mismatched shapes used the alignment-only value-flow join")
			}
		})
	}
}
