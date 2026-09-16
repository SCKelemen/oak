package asm

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"
)

// TestNativeCNFReplayWordMatchesLean pins the raw, width-carrying term syntax
// accepted by nativeCNFReplay.term to CNFWordProjection.projectWord. It covers
// only parameters, constants and pointwise and/or/xor at widths 1..64. Go
// pointer-memo reachability, arbitrary term kinds and source/frontend lowering
// remain outside this projection. This is not whole-constructor admission
// equivalence either: projectWord need not inspect an invalid parameter table
// for a constant-only term, while newNativeCNFReplay always checks that table.
func TestNativeCNFReplayWordMatchesLean(t *testing.T) {
	const replayMaxInt = 1_000_000
	parameters := []string{"p1", "p8", "p16", "p32", "p64"}
	widths := map[string]int{"p1": 1, "p8": 8, "p16": 16, "p32": 32, "p64": 64}
	bl := newCNFBlaster(parameters, widths)

	// Raw declared zero exercises term.declaredWidth's fallback. Explicit
	// declared fields retain the source width across a wider or narrower use.
	p1 := nativeWordParam(1, 0, "p1")
	p8 := nativeWordParam(8, 0, "p8")
	p8Wide16 := nativeWordParam(16, 8, "p8")
	p16Narrow8 := nativeWordParam(8, 16, "p16")
	p16 := nativeWordParam(16, 0, "p16")
	p32 := nativeWordParam(32, 0, "p32")
	p64 := nativeWordParam(64, 0, "p64")
	false1 := nativeWordConstant(1, 0)
	true1 := nativeWordConstant(1, 1)
	constant8 := nativeWordConstant(8, 0xa5)
	constant16 := nativeWordConstant(16, 0x8001)
	constant32 := nativeWordConstant(32, 0x80000001)
	constant64 := nativeWordConstant(64, uint64(1)<<63|1)
	mask8 := nativeWordConstant(8, 0xff)

	// The left child is narrower than the result and zero-extends. Blasting
	// this first allocates p1 and p8, then gate 10, before later parameters.
	and8 := nativeWordBinary(8, "and", p1, p8)
	// The left child is wider than the result and truncates.
	orWide8 := nativeWordBinary(8, "or", p16, false1)
	xor8 := nativeWordBinary(8, "xor", p8, mask8)
	shared8 := nativeWordBinary(8, "or", p8, p8)
	orNarrow16 := nativeWordBinary(16, "or", p8, false1)

	type wordCase struct {
		name      string
		term      *term
		wantRoots []int
		wantValue uint64
	}
	p8Roots := []int{4, 6, 8, 10, 12, 14, 16, 18}
	p16Roots := fixedEvenCNFEdges(22, 16)
	cases := []wordCase{
		{name: "narrow child and", term: and8, wantRoots: []int{20, 0, 0, 0, 0, 0, 0, 0}, wantValue: 1},
		{name: "width 1 fallback parameter", term: p1, wantRoots: []int{2}, wantValue: 1},
		{name: "width 8 fallback parameter", term: p8, wantRoots: p8Roots, wantValue: 0xa5},
		{name: "declared 8 widened to 16", term: p8Wide16, wantRoots: appendFixedZeros(p8Roots, 8), wantValue: 0xa5},
		{name: "declared 16 truncated to 8", term: p16Narrow8, wantRoots: fixedEvenCNFEdges(22, 8), wantValue: 0xef},
		{name: "width 16 fallback parameter", term: p16, wantRoots: p16Roots, wantValue: 0xbeef},
		{name: "wide child or", term: orWide8, wantRoots: fixedEvenCNFEdges(22, 8), wantValue: 0xef},
		{name: "xor complement", term: xor8, wantRoots: []int{5, 7, 9, 11, 13, 15, 17, 19}, wantValue: 0x5a},
		{name: "shared operands", term: shared8, wantRoots: p8Roots, wantValue: 0xa5},
		{name: "narrow child or at 16", term: orNarrow16, wantRoots: appendFixedZeros(p8Roots, 8), wantValue: 0xa5},
		{name: "false constant", term: false1, wantRoots: []int{0}, wantValue: 0},
		{name: "true constant", term: true1, wantRoots: []int{1}, wantValue: 1},
		{name: "width 8 constant", term: constant8, wantRoots: fixedConstantEndpointBits(8, 0xa5), wantValue: 0xa5},
		{name: "width 16 high-bit constant", term: constant16, wantRoots: fixedConstantEndpointBits(16, 0x8001), wantValue: 0x8001},
		{name: "width 32 high-bit constant", term: constant32, wantRoots: fixedConstantEndpointBits(32, 0x80000001), wantValue: 0x80000001},
		{name: "width 64 high-bit constant", term: constant64, wantRoots: fixedConstantEndpointBits(64, uint64(1)<<63|1), wantValue: uint64(1)<<63 | 1},
		{name: "width 32 fallback parameter", term: p32, wantRoots: fixedEvenCNFEdges(54, 32), wantValue: 0x89abcdef},
		{name: "width 64 fallback parameter", term: p64, wantRoots: fixedEvenCNFEdges(118, 64), wantValue: 0xfedcba9876543210},
	}

	// Witness values are normalized to their declared Oak types. Go term.eval
	// masks at the current term width, whereas the replay intentionally zeros
	// widened parameter bits at the declared width; arbitrary high garbage in
	// a widened parameter is therefore outside this typed-input correspondence.
	sample := map[string]uint64{
		"p1": 1, "p8": 0xa5, "p16": 0xbeef,
		"p32": 0x89abcdef, "p64": 0xfedcba9876543210,
	}
	for name, width := range widths {
		if sample[name]&^mask(width) != 0 {
			t.Fatalf("sample %s is not normalized to its declared %d-bit type", name, width)
		}
	}
	for _, test := range cases {
		roots := bl.blast(test.term)
		if !sameReplayBits(roots, test.wantRoots) {
			t.Fatalf("producer %s roots = %v, want %v", test.name, roots, test.wantRoots)
		}
		if value := test.term.eval(sample); value != test.wantValue {
			t.Fatalf("producer %s value = %#x, want %#x", test.name, value, test.wantValue)
		}
	}

	// A negative raw override falls back in Go because declaredWidth tests
	// declared > 0. Nat projection deliberately refuses that representation.
	negativeDeclared := nativeWordParam(8, -1, "p8")
	if roots := bl.blast(negativeDeclared); !sameReplayBits(roots, p8Roots) {
		t.Fatalf("negative raw-declared Go fallback roots = %v, want %v", roots, p8Roots)
	}
	if bl.stride() != len(parameters)+selectSlots || bl.stride() != 13 {
		t.Fatalf("interleaved stride = %d, want len(parameters)+8 = 13", bl.stride())
	}
	if bl.cnf.inputs[0] != 1 || bl.cnf.inputs[1] != 2 || bl.cnf.inputs[14] != 3 ||
		bl.cnf.inputs[2] != 11 || bl.cnf.inputs[823] != 122 {
		t.Fatalf("unexpected interleaved input allocation: %v", bl.cnf.inputs)
	}
	if _, err := validateCNFAllocation(bl.cnf); err != nil {
		t.Fatalf("word fixture does not satisfy the production allocation boundary: %v", err)
	}

	replay, err := newNativeCNFReplay(bl)
	if err != nil {
		t.Fatal(err)
	}
	replay.maxInt = replayMaxInt
	leanPins := make([]string, 0, len(cases))
	termIndex := make(map[*term]int, len(cases))
	t.Run("decisions", func(t *testing.T) {
		for index, test := range cases {
			termIndex[test.term] = index
			t.Run(test.name, func(t *testing.T) {
				roots, err := replay.term(test.term)
				if err != nil {
					t.Fatal(err)
				}
				if !sameReplayBits(roots, test.wantRoots) {
					t.Fatalf("replayed roots = %v, want %v", roots, test.wantRoots)
				}
				rendered, err := renderNativeCNFWordTerm(test.term)
				if err != nil {
					t.Fatal(err)
				}
				rootList, err := renderNativeCNFNatList(test.wantRoots)
				if err != nil {
					t.Fatal(err)
				}
				leanPins = append(leanPins, fmt.Sprintf(
					"def word%d : WordTerm := %s\n"+
						"example : replayProjected word%d = some %s := by decide\n"+
						"example : (WordTerm.eval wordInputs word%d).toNat = %d := by decide",
					index, rendered, index, rootList, index, test.wantValue))
			})
		}

		negativeRoots, err := replay.term(negativeDeclared)
		if err != nil || !sameReplayBits(negativeRoots, p8Roots) {
			t.Fatalf("negative raw declaration Go fallback: roots=%v error=%v", negativeRoots, err)
		}
		if _, err := renderNativeCNFWordTerm(negativeDeclared); err == nil {
			t.Fatal("negative raw declaration entered the Nat projection")
		}

		productionRefusals := []struct {
			name string
			term *term
		}{
			{name: "zero width", term: nativeWordConstant(0, 0)},
			{name: "width above 64", term: nativeWordConstant(65, 1)},
			{name: "constant bits above width", term: nativeWordConstant(8, 0x100)},
			{name: "unknown parameter", term: nativeWordParam(8, 0, "missing")},
			{name: "mismatched declared width", term: nativeWordParam(16, 16, "p8")},
			{name: "unsupported operation", term: nativeWordBinary(8, "add", p8, constant8)},
			{name: "malformed constant fields", term: &term{kind: termConst, width: 1, name: "bad"}},
			{name: "negative width", term: nativeWordConstant(-1, 0)},
		}
		for _, invalid := range productionRefusals {
			if roots, err := replay.term(invalid.term); err == nil {
				t.Errorf("%s replayed roots %v", invalid.name, roots)
			}
		}
		if _, err := renderNativeCNFWordTerm(productionRefusals[5].term); err == nil {
			t.Error("unsupported operation entered the formal operation projection")
		}
		if _, err := renderNativeCNFWordTerm(productionRefusals[6].term); err == nil {
			t.Error("malformed fields entered the raw syntax projection")
		}
		if _, err := renderNativeCNFWordTerm(productionRefusals[7].term); err == nil {
			t.Error("negative width entered the Nat projection")
		}

		limited, err := newNativeCNFReplay(bl)
		if err != nil {
			t.Fatal(err)
		}
		limited.maxInt = 2
		if roots, err := limited.term(p8); err == nil {
			t.Fatalf("maxInt-limited replay accepted roots %v", roots)
		}

		p8Replayed, err := replay.term(p8)
		if err != nil {
			t.Fatal(err)
		}
		sharedReplayed, err := replay.term(shared8)
		if err != nil {
			t.Fatal(err)
		}
		difference, err := replay.disequality(p8Replayed, sharedReplayed)
		if err != nil || difference != bddFalse {
			t.Fatalf("nonempty shared-word difference = %d, error=%v, want false", difference, err)
		}
		if err := replay.finish(); err != nil {
			t.Fatalf("word corpus did not cover the completed producer: %v", err)
		}
	})
	if t.Failed() {
		return
	}

	t.Run("kernel", func(t *testing.T) {
		lake, err := exec.LookPath("lake")
		if err != nil {
			requireOracle(t, "lake not on PATH; the formal workflow runs this kernel oracle")
		}
		snapshot, err := renderCNFAllocationSnapshot(bl.cnf)
		if err != nil {
			t.Fatal(err)
		}
		renderedParameters, err := renderNativeCNFWordParameters(parameters, widths)
		if err != nil {
			t.Fatal(err)
		}
		invalidPins := make([]string, 0, 6)
		for index, invalid := range []*term{
			nativeWordConstant(0, 0),
			nativeWordConstant(65, 1),
			nativeWordConstant(8, 0x100),
			nativeWordParam(8, 0, "missing"),
			nativeWordParam(16, 16, "p8"),
		} {
			rendered, err := renderNativeCNFWordTerm(invalid)
			if err != nil {
				t.Fatal(err)
			}
			invalidPins = append(invalidPins, fmt.Sprintf(
				"def invalid%d : WordTerm := %s\n"+
					"example : projectWord wordSnapshot wordParameters wordMaxInt invalid%d = none := by decide",
				index, rendered, index))
		}
		p8Index, sharedIndex := termIndex[p8], termIndex[shared8]
		leanSource := fmt.Sprintf(`import Oak.CNFWordProjection

set_option maxRecDepth 100000

namespace Oak.CNFWordProjection

def wordSnapshot : CNFDenseAllocation.Snapshot := %s
example : (CNFDenseAllocation.check wordSnapshot).isSome = true := by decide

def wordParameters : List CNFWordInput.Parameter := %s
def wordMaxInt : Nat := %d

def wordInputs : CNFWordInput.Inputs := fun name =>
  if name = "p1" then BitVec.ofNat 64 1
  else if name = "p8" then BitVec.ofNat 64 165
  else if name = "p16" then BitVec.ofNat 64 48879
  else if name = "p32" then BitVec.ofNat 64 2309737967
  else if name = "p64" then BitVec.ofNat 64 18364758544493064720
  else BitVec.ofNat 64 0

def replayProjected (word : WordTerm) : Option (List Nat) := do
  let bits <- projectWord wordSnapshot wordParameters wordMaxInt word
  bits.mapM (CNFReplayTerm.replayTerm wordSnapshot wordMaxInt)

%s

%s

example : projectWord wordSnapshot wordParameters 2 word%d = none := by decide

example :
    (match projectWord wordSnapshot wordParameters wordMaxInt word%d,
        projectWord wordSnapshot wordParameters wordMaxInt word%d with
      | some left, some right =>
          CNFReplayTerm.replayTerm wordSnapshot wordMaxInt
            (CNFReplayTerm.differenceTerm (List.zip left right))
      | _, _ => none) = some 0 := by decide

end Oak.CNFWordProjection
`, snapshot, renderedParameters, replayMaxInt, strings.Join(leanPins, "\n\n"),
			strings.Join(invalidPins, "\n\n"), p8Index, p8Index, sharedIndex)
		leanPath := filepath.Join(t.TempDir(), "NativeCNFWordProjectionProductionPins.lean")
		file, err := os.OpenFile(leanPath, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o600)
		if err != nil {
			t.Fatal(err)
		}
		if _, err := file.WriteString(leanSource); err != nil {
			file.Close()
			t.Fatal(err)
		}
		if err := file.Close(); err != nil {
			t.Fatal(err)
		}

		ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
		defer cancel()
		command := exec.CommandContext(ctx, lake, "env", "lean", leanPath)
		command.Dir = filepath.Join("..", "spec", "lean")
		if output, err := command.CombinedOutput(); err != nil {
			t.Fatalf("kernel-checking native CNF word pins: %v (context: %v)\n%s\n--- source ---\n%s",
				err, ctx.Err(), output, leanSource)
		}
	})
}

func nativeWordParam(width, declared int, name string) *term {
	return &term{kind: termParam, width: width, declared: declared, name: name}
}

func nativeWordConstant(width int, value uint64) *term {
	return &term{kind: termConst, width: width, value: value}
}

func nativeWordBinary(width int, operation string, left, right *term) *term {
	return &term{kind: termBinary, width: width, op: operation, left: left, right: right}
}

func fixedEvenCNFEdges(first, count int) []int {
	edges := make([]int, count)
	for index := range edges {
		edges[index] = first + 2*index
	}
	return edges
}

func appendFixedZeros(prefix []int, count int) []int {
	result := append([]int(nil), prefix...)
	return append(result, make([]int, count)...)
}

func fixedConstantEndpointBits(width int, value uint64) []int {
	bits := make([]int, width)
	for bit := range bits {
		bits[bit] = int(value >> uint(bit) & 1)
	}
	return bits
}

func renderNativeCNFWordParameters(parameters []string, widths map[string]int) (string, error) {
	if len(parameters) != len(widths) {
		return "", fmt.Errorf("parameter list and width map have different sizes")
	}
	seen := make(map[string]bool, len(parameters))
	rendered := make([]string, len(parameters))
	for index, name := range parameters {
		leanName, err := renderNativeCNFLeanASCIIName(name)
		width, known := widths[name]
		if err != nil || !known || seen[name] || width < 1 || width > 64 {
			return "", fmt.Errorf("parameter %d is outside the bounded metadata projection", index)
		}
		seen[name] = true
		rendered[index] = fmt.Sprintf("⟨%s, %d⟩", leanName, width)
	}
	return "[" + strings.Join(rendered, ", ") + "]", nil
}

// renderNativeCNFWordTerm projects raw fields, not precomputed bit syntax or
// values. Semantic width, declaration, constant and input checks remain in
// projectWord; fields with no Nat/WordTerm representation fail here.
func renderNativeCNFWordTerm(root *term) (string, error) {
	var render func(*term, int) (string, error)
	render = func(current *term, depth int) (string, error) {
		if current == nil || depth > 256 {
			return "", fmt.Errorf("term is nil or exceeds the bounded syntax projection")
		}
		if current.width < 0 || current.declared < 0 {
			return "", fmt.Errorf("negative term fields are outside the Nat projection")
		}
		switch current.kind {
		case termConst:
			if current.name != "" || current.op != "" || current.left != nil || current.right != nil ||
				current.cond != nil || current.declared != 0 {
				return "", fmt.Errorf("constant carries fields absent from WordTerm")
			}
			return fmt.Sprintf(".constant %d %d", current.width, current.value), nil
		case termParam:
			if current.name == "" || current.op != "" || current.left != nil || current.right != nil ||
				current.cond != nil || current.value != 0 {
				return "", fmt.Errorf("parameter carries fields absent from WordTerm")
			}
			name, err := renderNativeCNFLeanASCIIName(current.name)
			if err != nil {
				return "", err
			}
			return fmt.Sprintf(".param %d %d %s", current.width, current.declared, name), nil
		case termBinary:
			if current.name != "" || current.value != 0 || current.declared != 0 || current.cond != nil ||
				current.left == nil || current.right == nil {
				return "", fmt.Errorf("binary term carries fields absent from WordTerm")
			}
			operation := -1
			switch current.op {
			case "and":
				operation = opAnd
			case "or":
				operation = opOr
			case "xor":
				operation = opXor
			default:
				return "", fmt.Errorf("operation %q has no WordTerm tag", current.op)
			}
			left, err := render(current.left, depth+1)
			if err != nil {
				return "", err
			}
			right, err := render(current.right, depth+1)
			if err != nil {
				return "", err
			}
			return fmt.Sprintf(".binary %d %d (%s) (%s)", current.width, operation, left, right), nil
		default:
			return "", fmt.Errorf("term kind %d has no WordTerm constructor", current.kind)
		}
	}
	return render(root, 0)
}

func renderNativeCNFLeanASCIIName(name string) (string, error) {
	if name == "" {
		return "", fmt.Errorf("empty parameter name")
	}
	for _, character := range name {
		if (character < 'a' || character > 'z') && (character < 'A' || character > 'Z') &&
			(character < '0' || character > '9') && character != '_' {
			return "", fmt.Errorf("parameter name %q is outside fixed ASCII identifiers", name)
		}
	}
	return strconv.Quote(name), nil
}

func renderNativeCNFNatList(values []int) (string, error) {
	rendered := make([]string, len(values))
	for index, value := range values {
		if value < 0 {
			return "", fmt.Errorf("value %d is outside the Nat projection", value)
		}
		rendered[index] = strconv.Itoa(value)
	}
	return "[" + strings.Join(rendered, ", ") + "]", nil
}
